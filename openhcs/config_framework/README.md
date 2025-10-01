# Configuration Framework

**Generic configuration framework for lazy dataclass resolution with dual-axis inheritance.**

## Overview

This framework provides a complete system for hierarchical configuration management with lazy resolution, enabling sophisticated inheritance patterns without explicit parameter passing.

### Key Features

- **Lazy Dataclass Factory**: Dynamically create dataclasses with lazy field resolution
- **Dual-Axis Inheritance**: 
  - X-Axis: Context hierarchy (Step → Pipeline → Global)
  - Y-Axis: Sibling inheritance within same context
- **Contextvars-Based**: Uses Python's `contextvars` for clean context management
- **UI Integration**: Placeholder text generation for configuration forms
- **Thread-Safe**: Thread-local global configuration storage
- **100% Generic**: No application-specific dependencies

## Quick Start

```python
from dataclasses import dataclass
from openhcs.config_framework import (
    set_base_config_type,
    LazyDataclassFactory,
    config_context,
    ensure_global_config_context,
)

# 1. Define your configuration dataclasses
@dataclass(frozen=True)
class PathPlanningConfig:
    sub_dir: str = "images"
    output_dir_suffix: str = "_processed"

@dataclass(frozen=True)
class GlobalPipelineConfig:
    num_workers: int = 4
    path_planning_config: PathPlanningConfig = PathPlanningConfig()

@dataclass
class PipelineConfig:
    num_workers: int | None = None  # Inherits from GlobalPipelineConfig
    path_planning_config: PathPlanningConfig | None = None

@dataclass
class StepMaterializationConfig:
    sub_dir: str | None = None  # Inherits from PathPlanningConfig
    output_dir_suffix: str | None = None

# 2. Initialize framework
set_base_config_type(GlobalPipelineConfig)

# 3. Create lazy dataclasses
LazyPipelineConfig = LazyDataclassFactory.make_lazy_simple(PipelineConfig)
LazyStepMaterializationConfig = LazyDataclassFactory.make_lazy_simple(StepMaterializationConfig)

# 4. Set up global config
global_config = GlobalPipelineConfig(
    num_workers=8,
    path_planning_config=PathPlanningConfig(
        sub_dir="images",
        output_dir_suffix="_processed"
    )
)
ensure_global_config_context(GlobalPipelineConfig, global_config)

# 5. Create pipeline config (inherits from global)
pipeline_config = LazyPipelineConfig(
    path_planning_config=PathPlanningConfig(
        output_dir_suffix="_custom"  # Override global
        # sub_dir inherits from global
    )
)

# 6. Create step with lazy config (inherits from pipeline)
from openhcs.core.steps import FunctionStep

step = FunctionStep(
    func=my_processing_function,
    name="preprocess",
    step_materialization_config=LazyStepMaterializationConfig(
        sub_dir="checkpoints"  # Override pipeline
        # output_dir_suffix=None - inherits from pipeline
    )
)

# 7. Use with nested context hierarchy
with config_context(pipeline_config):
    # Pipeline context active

    with config_context(step):  # Pass step object, not config directly
        # Step context active - step has lazy config attributes

        # step.step_materialization_config.output_dir_suffix resolves:
        # 1. Check step config: None
        # 2. Check pipeline config: "_custom" ✓
        # Result: "_custom"

        # step.step_materialization_config.sub_dir resolves:
        # 1. Check step config: "checkpoints" ✓
        # Result: "checkpoints"

        print(step.step_materialization_config.output_dir_suffix)  # "_custom"
        print(step.step_materialization_config.sub_dir)  # "checkpoints"
```

## Architecture

### Dual-Axis Inheritance

The framework uses pure MRO-based dual-axis resolution:

**X-Axis (Context Hierarchy)**:
```
Step Context → Pipeline Context → Global Context → Static Defaults
All contexts are merged into available_configs dict
```

**Y-Axis (MRO Traversal)**:
```
Most specific class → Least specific class (following Python's MRO)
```

**How it works:**
1. Context hierarchy is flattened into a single `available_configs` dict
2. For each field resolution, traverse the requesting object's MRO from most to least specific
3. For each MRO class, check if there's a config instance in `available_configs` with a concrete (non-None) value
4. Return the first concrete value found

**No priority functions needed** - Python's MRO IS the priority!

### MRO Inheritance in Action

The framework supports **multiple inheritance** with automatic MRO-based field resolution. This is one of the most powerful features.

#### Real-World Example: StepMaterializationConfig

```python
# From openhcs/core/config.py

@dataclass(frozen=True)
class WellFilterConfig:
    """Base configuration for well filtering."""
    well_filter: Optional[Union[List[str], str, int]] = None
    well_filter_mode: WellFilterMode = WellFilterMode.INCLUDE

@dataclass(frozen=True)
class PathPlanningConfig(WellFilterConfig):
    """Path planning configuration - inherits well filtering."""
    output_dir_suffix: str = "_openhcs"
    sub_dir: str = "images"
    # Inherits: well_filter, well_filter_mode

@dataclass(frozen=True)
class StepWellFilterConfig(WellFilterConfig):
    """Step-level well filtering with different defaults."""
    well_filter: Optional[Union[List[str], str, int]] = 1  # Override default

@dataclass(frozen=True)
class StepMaterializationConfig(StepWellFilterConfig, PathPlanningConfig):
    """
    Per-step materialization config using MULTIPLE INHERITANCE.

    MRO: StepMaterializationConfig → StepWellFilterConfig → PathPlanningConfig → WellFilterConfig
    """
    sub_dir: str = "checkpoints"  # Override PathPlanningConfig default
    # Inherits well_filter from StepWellFilterConfig (comes first in MRO)
    # Inherits output_dir_suffix from PathPlanningConfig
    # Inherits well_filter_mode from WellFilterConfig (via both parents)
```

#### MRO Resolution Example

```python
# Setup
global_config = GlobalPipelineConfig(
    path_planning_config=PathPlanningConfig(
        output_dir_suffix="_global",
        sub_dir="images",
        well_filter=10
    )
)

pipeline_config = PipelineConfig(
    path_planning_config=LazyPathPlanningConfig(
        output_dir_suffix="_pipeline"
        # sub_dir=None - inherits from global
        # well_filter=None - inherits from global
    )
)

step = Step(
    func=process_images,
    step_materialization_config=LazyStepMaterializationConfig(
        sub_dir="checkpoints"  # Override
        # output_dir_suffix=None - inherits from pipeline
        # well_filter=None - inherits from pipeline
    )
)

# Resolution with nested contexts
with config_context(pipeline_config):
    with config_context(step):
        # step.step_materialization_config.sub_dir resolves:
        # 1. Check StepMaterializationConfig in step context: "checkpoints" ✓
        # Result: "checkpoints"

        # step.step_materialization_config.output_dir_suffix resolves:
        # 1. Check StepMaterializationConfig in step context: None
        # 2. Check StepWellFilterConfig in step context: None (no such field)
        # 3. Check PathPlanningConfig in step context: None
        # 4. Check StepMaterializationConfig in pipeline context: None
        # 5. Check PathPlanningConfig in pipeline context: "_pipeline" ✓
        # Result: "_pipeline"

        # step.step_materialization_config.well_filter resolves:
        # 1. Check StepMaterializationConfig in step context: None
        # 2. Check StepWellFilterConfig in step context: None (inherits from WellFilterConfig)
        # 3. Check PathPlanningConfig in step context: None
        # 4. Check WellFilterConfig in step context: None
        # 5. Check StepMaterializationConfig in pipeline context: None
        # 6. Check PathPlanningConfig in pipeline context: None
        # 7. Check WellFilterConfig in pipeline context: None
        # 8. Check PathPlanningConfig in global context: 10 ✓
        # Result: 10

        print(step.step_materialization_config.sub_dir)  # "checkpoints"
        print(step.step_materialization_config.output_dir_suffix)  # "_pipeline"
        print(step.step_materialization_config.well_filter)  # 10
```

#### Three-Level Inheritance Test (from test_main.py)

```python
# Global config
global_config = GlobalPipelineConfig(
    step_well_filter_config=StepWellFilterConfig(well_filter=3)
)

# Pipeline config
pipeline_config = PipelineConfig(
    step_well_filter_config=LazyStepWellFilterConfig(well_filter=2)
)

# Pipeline with different step configs
pipeline = Pipeline([
    Step(
        name="Step 0",
        func=process,
        step_well_filter_config=LazyStepWellFilterConfig(well_filter=4)  # Override
    ),
    Step(
        name="Step 1",
        func=process
        # No step_well_filter_config - uses default LazyStepWellFilterConfig()
    ),
    Step(
        name="Step 2",
        func=process,
        step_materialization_config=LazyStepMaterializationConfig()
        # step_materialization_config inherits well_filter from pipeline
    )
])

# Resolution results:
# Step 0: well_filter = 4 (explicit override)
# Step 1: well_filter = 2 (inherits from pipeline)
# Step 2: well_filter = 2 (inherits from pipeline via StepMaterializationConfig MRO)
```

### Context Management

Uses Python's `contextvars` for clean, thread-safe context management:

```python
from openhcs.config_framework import config_context
from openhcs.core.steps import FunctionStep

# Create pipeline config
pipeline_config = PipelineConfig()

# Create step with lazy config attributes
step = FunctionStep(
    func=process_images,
    step_materialization_config=LazyStepMaterializationConfig()
)

# Create nested context scope
with config_context(pipeline_config):
    # Pipeline context active

    with config_context(step):  # Pass step object (has lazy config attributes)
        # Step context active
        # step.step_materialization_config fields resolve through contextvars stack
        # Resolution: step config → pipeline config → global config → static defaults

# Context automatically cleaned up on exit
```

### Placeholder Generation

For UI integration, the framework provides placeholder text generation:

```python
from openhcs.config_framework import LazyDefaultPlaceholderService

# Get placeholder text for a field
placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
    dataclass_type=LazyStepMaterializationConfig,
    field_name='output_dir_suffix',
    placeholder_prefix='Pipeline default'
)
# Returns: "Pipeline default: _custom"
# (Shows inherited value from pipeline config)
```

## API Reference

### Configuration

```python
set_base_config_type(config_type: Type) -> None
```
Set the base configuration type for the framework. This should be your top-level global config.

### Factory

```python
LazyDataclassFactory.make_lazy_simple(base_class: Type, lazy_class_name: str = None) -> Type
```
Create a lazy dataclass from a base dataclass. The lazy version resolves fields through the context hierarchy.

```python
auto_create_decorator(target_class: Type) -> Callable
```
Decorator factory for automatically creating lazy dataclasses with field inheritance.

### Context

```python
config_context(obj) -> ContextManager
```
Create a context scope for lazy resolution. Accepts:
- Dataclass instances (e.g., `PipelineConfig()`)
- Step objects with lazy config attributes (e.g., `FunctionStep(...)`)
- Dict-like objects

```python
get_current_temp_global() -> Any
```
Get the current context (merged global config).

### Global Config

```python
ensure_global_config_context(config_type: Type, config_instance: Any) -> None
```
Establish global config as the base context for all resolution.

```python
set_global_config_for_editing(config_type: Type, config_instance: Any) -> None
```
Set global config for editing scenarios (UI, tests, etc.).

## Integration with OpenHCS

OpenHCS uses this framework for its configuration system:

```python
# openhcs/core/config.py
from openhcs.config_framework import set_base_config_type
from openhcs.core.config import GlobalPipelineConfig

# Initialize framework with OpenHCS types
set_base_config_type(GlobalPipelineConfig)

# That's it! MRO-based resolution handles everything.
```

## Design Principles

1. **Generic**: No application-specific dependencies
2. **Explicit**: Context scoping is explicit via `config_context()`
3. **Fail-Loud**: Errors are raised immediately, no silent failures
4. **Type-Safe**: Uses dataclasses and type hints throughout
5. **Thread-Safe**: Thread-local storage for global config
6. **Clean**: Automatic cleanup via context managers

## Requirements

- Python 3.10+
- No external dependencies (pure stdlib)

## License

Part of the OpenHCS project.

