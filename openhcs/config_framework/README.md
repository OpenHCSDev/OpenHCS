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
    set_config_priority_func,
    LazyDataclassFactory,
    config_context,
    ensure_global_config_context,
)

# 1. Define your configuration dataclasses
@dataclass
class GlobalConfig:
    num_workers: int = 4
    gpu_enabled: bool = False

@dataclass
class PipelineConfig:
    num_workers: int | None = None  # Inherits from GlobalConfig
    gpu_enabled: bool | None = None
    output_dir: str = "/tmp/output"

@dataclass
class StepConfig:
    num_workers: int | None = None  # Inherits from PipelineConfig
    gpu_enabled: bool | None = None
    step_name: str = "process"

# 2. Initialize framework
set_base_config_type(GlobalConfig)

# 3. Create lazy dataclasses
LazyPipelineConfig = LazyDataclassFactory.make_lazy_simple(PipelineConfig)
LazyStepConfig = LazyDataclassFactory.make_lazy_simple(StepConfig)

# 4. Set up global config
global_config = GlobalConfig(num_workers=8, gpu_enabled=True)
ensure_global_config_context(GlobalConfig, global_config)

# 5. Use with context hierarchy
pipeline_config = LazyPipelineConfig(output_dir="/data/output")

with config_context(pipeline_config):
    # Pipeline context: num_workers=8 (from global), output_dir="/data/output"
    
    step_config = LazyStepConfig(step_name="preprocess")
    
    with config_context(step_config):
        # Step context: num_workers=8 (from global via pipeline)
        # gpu_enabled=True (from global via pipeline)
        # output_dir="/data/output" (from pipeline)
        # step_name="preprocess" (from step)
        
        print(step_config.num_workers)  # 8
        print(step_config.gpu_enabled)  # True
        print(step_config.output_dir)   # "/data/output"
```

## Architecture

### Dual-Axis Inheritance

The framework uses pure MRO-based dual-axis resolution:

**X-Axis (Context Flattening)**:
```
Step Context → Pipeline Context → Global Context
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

### Context Management

Uses Python's `contextvars` for clean, thread-safe context management:

```python
from openhcs.config_framework import config_context

# Create context scope
with config_context(pipeline_config):
    # All lazy resolution within this scope sees pipeline_config
    lazy_instance = LazyStepConfig()
    # Fields resolve through contextvars stack

# Context automatically cleaned up on exit
```

### Placeholder Generation

For UI integration, the framework provides placeholder text generation:

```python
from openhcs.config_framework import LazyDefaultPlaceholderService

# Get placeholder text for a field
placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
    dataclass_type=LazyStepConfig,
    field_name='num_workers',
    placeholder_prefix='Pipeline default'
)
# Returns: "Pipeline default: 8"
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
Create a context scope for lazy resolution. Accepts dataclass instances, function steps, or dict-like objects.

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

