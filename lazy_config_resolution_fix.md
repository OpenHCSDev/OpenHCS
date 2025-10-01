# Lazy Config Resolution Fix

## Problem Summary

The lazy configuration system wasn't working during compilation because code was accessing configs through `ProcessingContext` getters instead of through the active `config_context()`. This caused lazy configs with `None` values to fail to resolve to their inherited/default values.

## Root Cause

**The Issue:**
- During compilation, the compiler wraps operations in `config_context(orchestrator.pipeline_config)`
- But various components (PathPlanner, MaterializationFlagPlanner, etc.) were calling `context.get_path_planning_config()` which returned the stored `global_config` directly
- This bypassed the active `config_context()` and prevented lazy resolution
- Result: `sub_dir=None` stayed as `None` instead of resolving to `""` from GlobalPipelineConfig

**Why This Happened:**
The ProcessingContext getters were designed for use AFTER compilation (in workers with frozen context), but they were being used DURING compilation when lazy resolution should still be active.

## Solution for sub_dir (✅ FIXED)

### Changes Made:

1. **Compiler (`openhcs/core/pipeline/compiler.py`)**
   - Wrapped entire compilation loop in `config_context(orchestrator.pipeline_config)` at line ~770
   - This establishes the context for ALL lazy resolution during compilation
   
   ```python
   # CRITICAL: Wrap all compilation steps in config_context() for lazy resolution
   from openhcs.core.context.contextvars_context import config_context
   with config_context(orchestrator.pipeline_config):
       PipelineCompiler.initialize_step_plans_for_context(...)
       PipelineCompiler.declare_zarr_stores_for_context(...)
       PipelineCompiler.plan_materialization_flags_for_context(...)
       PipelineCompiler.validate_memory_contracts_for_context(...)
       PipelineCompiler.assign_gpu_resources_for_context(...)
       # ... etc
   ```

2. **PathPlanner (`openhcs/core/pipeline/path_planner.py`)**
   - Modified `__init__` to accept `pipeline_config` parameter
   - Changed from `context.get_path_planning_config()` to `pipeline_config.path_planning_config`
   - Updated `PipelinePathPlanner.prepare_pipeline_paths` signature to include `pipeline_config`
   
   ```python
   class PathPlanner:
       def __init__(self, context: ProcessingContext, pipeline_config):
           self.ctx = context
           # Access config directly from pipeline_config (lazy resolution via config_context)
           self.cfg = pipeline_config.path_planning_config
           self.vfs = pipeline_config.vfs_config
   ```

3. **MaterializationFlagPlanner (`openhcs/core/pipeline/materialization_flag_planner.py`)**
   - Modified `prepare_pipeline_flags` to accept `pipeline_config` parameter
   - Changed from `context.get_vfs_config()` to `pipeline_config.vfs_config`
   
   ```python
   @staticmethod
   def prepare_pipeline_flags(
       context: ProcessingContext,
       pipeline_definition: List[AbstractStep],
       plate_path: Path,
       pipeline_config
   ) -> None:
       # Access config directly from pipeline_config (lazy resolution via config_context)
       vfs_config = pipeline_config.vfs_config
   ```

4. **ProcessingContext (`openhcs/core/context/processing_context.py`)**
   - Added comment clarifying getters are only for use outside compilation
   - Reverted changes that made getters check for active context (overcomplicated)
   
   ```python
   # --- Config Getters ---
   # NOTE: These are only used outside compilation (e.g., in workers after context is frozen)
   # During compilation, code should access orchestrator.pipeline_config directly
   ```

### Result:
✅ The `sub_dir=None` error is COMPLETELY FIXED
✅ Test now runs full pipeline and processes images
✅ Lazy resolution works correctly: `LazyPathPlanningConfig(sub_dir=None)` → resolves to `""` from GlobalPipelineConfig

## Problem with napari_port (❌ NOT FIXED YET)

### Current Error:
```
zmq.error.ZMQError: Invalid argument (addr='tcp://localhost:None')
```

### Root Cause Analysis:

**Where the error occurs:**
- `openhcs/io/napari_stream.py` line 86: `publisher = self._get_publisher(kwargs['napari_port'])`
- The `kwargs` come from `config_instance.get_streaming_kwargs(context)` in `function_step.py` line 978
- The `config_instance` is a `NapariStreamingConfig` from the frozen `step_plan`

**The config chain:**
1. Test creates: `LazyNapariStreamingConfig(well_filter=2)` (no napari_port specified)
2. Expected: `napari_port=None` should resolve to class default `5555` from `NapariStreamingConfig.napari_port = 5555`
3. Actual: `napari_port=None` stays as `None` even after resolution

**Why it's not resolving:**

The step's streaming config is accessed during step execution (AFTER compilation), when configs are already frozen. The `config_instance` in `step_plan` was resolved during compilation via `resolve_lazy_dataclasses_for_context()`, but the resolution didn't properly fall back to class defaults.

### Attempted Fix (didn't work):

Added `config_context(step)` wrapper around `step.process()` in orchestrator:

```python
# openhcs/core/orchestrator/orchestrator.py line ~170
from openhcs.core.context.contextvars_context import config_context
with config_context(step):
    step.process(frozen_context, step_index)
```

**Why this didn't work:**
The step configs are already resolved and frozen during compilation. The `config_context(step)` can't re-resolve them because they're concrete (not lazy) after `resolve_lazy_dataclasses_for_context()`.

### The Real Issue:

The problem is in `resolve_lazy_dataclasses_for_context()` or the underlying `resolve_field_inheritance()` function. When resolving `napari_port=None`, it should:

1. Check context hierarchy (GlobalPipelineConfig.napari_streaming_config.napari_port) - not found
2. Check MRO siblings - not found
3. **Fall back to class default** (`NapariStreamingConfig.napari_port = 5555`) ← THIS STEP IS FAILING

The class default fallback exists in the code (`dual_axis_resolver.py` lines 317-325), but it's not being reached or not working correctly for `napari_port`.

### Next Steps to Debug:

1. Add debug logging to `resolve_field_inheritance()` to see what's happening with `napari_port`
2. Check if `napari_port` is being resolved to `None` from somewhere in the context before reaching class defaults
3. Verify that the class default lookup (`object.__getattribute__(obj_type, field_name)`) works for `napari_port`
4. Check if there's a difference in how `sub_dir` (which works) vs `napari_port` (which doesn't) are being resolved

### Hypothesis:

The issue might be that `napari_port` is nested inside `NapariStreamingConfig` which is nested inside the step, while `sub_dir` is in `PathPlanningConfig` which is directly on `PipelineConfig`. The nesting level might affect resolution.

Or: The GlobalPipelineConfig doesn't have a `napari_streaming_config` field at all, so there's no context to inherit from, and the class default fallback isn't working for some reason.

## ACTUAL ROOT CAUSE (✅ FOUND)

The real issue is in `to_base_config()` in `openhcs/config_framework/lazy_factory.py` line 211-216:

```python
def to_base_config(self):
    field_values = {f.name: object.__getattribute__(self, f.name) for f in fields(self)}
    return base_class(**field_values)
```

When a lazy config has `napari_port=None`, this code:
1. Extracts all field values including `napari_port=None`
2. Passes them to the base class constructor: `NapariStreamingConfig(napari_port=None, ...)`
3. **Explicit `None` overrides the class default!**

Test proof:
```python
@dataclass(frozen=True)
class Config:
    napari_port: int = 5555

c1 = Config()  # napari_port=5555 ✅
c2 = Config(napari_port=None)  # napari_port=None ❌ (overrides default!)
```

### Solution:

Filter out `None` values before passing to base class constructor:

```python
def to_base_config(self):
    field_values = {}
    for f in fields(self):
        value = object.__getattribute__(self, f.name)
        if value is not None:  # Only pass non-None values
            field_values[f.name] = value
    return base_class(**field_values)
```

This way, fields with `None` values are omitted, allowing the base class to use its defaults.

## PyQt GUI Issue (❌ SEPARATE BUG)

### Error:
```
RuntimeError: No global configuration context found.
Ensure application startup has called ensure_global_config_context().
```

### Root Cause:

There are TWO different `global_config.py` modules:
- `openhcs/config_framework/global_config.py` (generic framework version)
- `openhcs/core/context/global_config.py` (OpenHCS-specific version)

These maintain SEPARATE thread-local storages!

- `ensure_global_config_context()` sets context in `openhcs.config_framework.global_config`
- Orchestrator checks context in `openhcs.core.context.global_config`
- Result: Context is set in one storage but checked in another → always returns None!

### Solution:

Make orchestrator use the same module as `ensure_global_config_context()`:

```python
# openhcs/core/orchestrator/orchestrator.py line 347
from openhcs.config_framework.global_config import get_current_global_config  # Changed from openhcs.core.context.global_config
```

### Long-term Fix:

These two modules should be consolidated into one. Having duplicate global config management is a code smell.

