# plan_01_eliminate_config_merging.md
## Component: Eliminate Orchestrator Config Merging

### Objective
Delete `_merge_nested_dataclass()` and `_create_merged_config()` from orchestrator.py. These 90 lines of imperative config merging code duplicate what the config framework's dual-axis resolver already does declaratively.

### Findings

**Current Rot (orchestrator.py lines 72-161):**
```python
def _merge_nested_dataclass(pipeline_value, global_value):
    # 36 lines of imperative field-by-field merging
    for field in dataclass_fields(type(pipeline_value)):
        raw_pipeline_field = pipeline_value.__dict__.get(field.name)
        if raw_pipeline_field is not None:
            # more imperative logic...

def _create_merged_config(pipeline_config, global_config):
    # 49 lines of imperative merging with lazy config handling
    for field in fields(GlobalPipelineConfig):
        pipeline_value = pipeline_config.__dict__.get(field.name)
        if pipeline_value is not None:
            if hasattr(pipeline_value, 'to_base_config'):
                # more special casing...
```

**The Config Framework Already Solves This:**

`config_context()` + lazy `__getattribute__` resolution:
```python
with config_context(pipeline_config):  # Pushes to context stack
    # ANY access to a lazy field automatically:
    # 1. Checks instance value (if not None, return it)
    # 2. Walks context stack from most to least specific
    # 3. Walks MRO for sibling inheritance
    # 4. Returns first non-None value found
    value = step.path_planning_config.well_filter  # Resolved automatically
```

**Why the Duplication Exists:**
The orchestrator was written before the config framework's dual-axis resolver was complete. It manually merges configs to create a "materialized" GlobalPipelineConfig. But this materialization is unnecessary — lazy resolution handles it.

### Plan

**Phase 1: Audit Call Sites**

Find all usages of `_create_merged_config`:
```python
# orchestrator.py
self._effective_config = _create_merged_config(...)  # in apply_pipeline_config()
```

**Phase 2: Replace with config_context()**

Instead of eagerly materializing a merged config:
```python
# BEFORE (imperative)
def apply_pipeline_config(self, pipeline_config):
    self._effective_config = _create_merged_config(pipeline_config, self.global_config)

def get_effective_config(self):
    return self._effective_config
```

```python
# AFTER (declarative)
def apply_pipeline_config(self, pipeline_config):
    self._pipeline_config = pipeline_config
    # No merging. Config framework handles it lazily.

def get_effective_config(self):
    # Just wrap access in config_context — lazy resolution does the rest
    with config_context(self._pipeline_config):
        return get_current_temp_global()
```

**Phase 3: Delete Dead Code**

Delete both functions:
- `_merge_nested_dataclass()` (lines 72-108)
- `_create_merged_config()` (lines 111-160)

~90 lines removed.

### Structural Properties

- **No imperative merging** — Config merging is declarative via context stack
- **No field-by-field loops** — MRO resolution handles inheritance
- **No special-casing lazy vs non-lazy** — Lazy `__getattribute__` handles both
- **Single source of truth** — Config framework is THE config resolution system

### Risk Assessment

**Low risk** — The config framework's resolver is battle-tested (used by all UI resolution). The orchestrator's merging logic was a workaround for pre-framework code.

### Cleanup — DELETE ALL OF THIS

**Functions to DELETE from `orchestrator.py`:**
```python
def _merge_nested_dataclass(...)   # DELETE (lines 72-108)
def _create_merged_config(...)     # DELETE (lines 111-160)
```

**No wrappers. No backwards compatibility.**
- Replace merge calls with `with config_context(step_config): ...`
- Field access inside context returns resolved values via lazy resolution
- If something doesn't resolve correctly, fix the config hierarchy — don't add special-case merging

### ❌ ANTIPATTERNS TO AVOID

**DO NOT create a "simplified" merge helper:**
```python
# ❌ WRONG: Wrapper around config_context
def merge_configs(global_config, step_config):
    with config_context(step_config):
        return get_current_temp_global()  # DON'T CREATE WRAPPER
```
Just use `config_context` directly. No wrapper needed.

**DO NOT add "fallback" merging for edge cases:**
```python
# ❌ WRONG: Fallback to old behavior
with config_context(step_config):
    value = getattr(config, field)
    if value is None:
        value = _merge_nested_dataclass(...)  # DON'T KEEP OLD LOGIC
```
If resolution returns None, that's the correct value. Fix the config hierarchy, not the resolver.

**DO NOT create a MergedConfig class:**
```python
# ❌ WRONG: Wrapper class
class MergedConfig:
    def __init__(self, global_config, step_config):
        self._merged = _create_merged_config(...)  # DON'T
```
Use the existing lazy dataclass resolution. No new classes.

**DO NOT add field-by-field copying logic:**
```python
# ❌ WRONG: Manual field copying
for field in fields(step_config):
    if getattr(step_config, field.name) is not None:
        setattr(result, field.name, ...)  # DON'T
```
This is the exact rot we're deleting. Lazy resolution handles this.

### Implementation Draft

(After smell loop approval)
