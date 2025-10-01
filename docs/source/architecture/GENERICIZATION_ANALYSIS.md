# Configuration Framework Genericization Analysis

**Date**: 2025-01-01
**Goal**: Extract configuration framework into standalone, reusable module
**Status**: ANALYSIS COMPLETE

## Executive Summary

The configuration framework is **95% generic** already. Only a few OpenHCS-specific dependencies need to be abstracted:

1. **`GlobalPipelineConfig`** - Hardcoded type reference (easily parameterized)
2. **`_get_config_priority()`** - OpenHCS-specific config name matching (easily abstracted)
3. **UI formatting utilities** - Optional dependency (already gracefully handled)

**Recommendation**: Extract to `openhcs/config_framework/` as a standalone module with minimal changes.

## Current Architecture

### Core Framework Files (100% Generic)

1. **`openhcs/core/dual_axis_resolver_recursive.py`** (454 lines)
   - **Purpose**: Pure function dual-axis inheritance resolver
   - **Dependencies**: NONE (pure Python stdlib)
   - **Generic Score**: 100%
   - **Issues**: `_get_config_priority()` has OpenHCS-specific config names (lines 35-75)

2. **`openhcs/core/lazy_placeholder_simplified.py`** (200 lines)
   - **Purpose**: Placeholder text generation for UI
   - **Dependencies**: `lazy_config._lazy_type_registry`, optional `ui.shared.ui_utils`
   - **Generic Score**: 95%
   - **Issues**: UI formatting is optional (already gracefully handled)

3. **`openhcs/core/context/global_config.py`** (62 lines)
   - **Purpose**: Thread-local storage for global config
   - **Dependencies**: NONE (pure Python stdlib)
   - **Generic Score**: 100%
   - **Issues**: NONE

### Core Framework Files (95% Generic)

4. **`openhcs/core/lazy_config.py`** (1054 lines)
   - **Purpose**: Lazy dataclass factory with dynamic resolution
   - **Dependencies**: `context.global_config`, `lazy_placeholder_simplified`, `dual_axis_resolver_recursive`
   - **Generic Score**: 95%
   - **Issues**: 
     - Imports from `openhcs.core.*` (easily changed to relative imports)
     - No actual OpenHCS-specific logic

5. **`openhcs/core/context/contextvars_context.py`** (529 lines)
   - **Purpose**: Contextvars-based context management
   - **Dependencies**: `config.GlobalPipelineConfig`, `context.global_config`, `lazy_config._lazy_type_registry`
   - **Generic Score**: 90%
   - **Issues**:
     - Hardcoded `GlobalPipelineConfig` type (lines 105, 298)
     - Easily parameterized with base config type

## OpenHCS-Specific Dependencies

### 1. GlobalPipelineConfig Type Reference

**Location**: `openhcs/core/context/contextvars_context.py`

**Lines 105, 298**:
```python
from openhcs.core.config import GlobalPipelineConfig

def get_base_global_config():
    """Get base GlobalPipelineConfig from thread-local storage."""
    from openhcs.core.context.global_config import get_current_global_config
    return get_current_global_config(GlobalPipelineConfig)
```

**Solution**: Parameterize with base config type:
```python
# Framework code
_base_config_type = None

def set_base_config_type(config_type: Type):
    """Set the base config type for the framework."""
    global _base_config_type
    _base_config_type = config_type

def get_base_global_config():
    """Get base config from thread-local storage."""
    if _base_config_type is None:
        raise RuntimeError("Base config type not set. Call set_base_config_type() first.")
    from .global_config import get_current_global_config
    return get_current_global_config(_base_config_type)
```

**OpenHCS initialization**:
```python
from openhcs.config_framework import set_base_config_type
from openhcs.core.config import GlobalPipelineConfig

set_base_config_type(GlobalPipelineConfig)
```

### 2. Config Priority Function

**Location**: `openhcs/core/dual_axis_resolver_recursive.py`

**Lines 35-75**:
```python
def _get_config_priority(config_type: Type) -> int:
    """Get priority level for config types."""
    config_name = config_type.__name__
    
    # Step-level configs (highest priority)
    if 'Step' in config_name:
        if 'Materialization' in config_name:
            return 1  # StepMaterializationConfig - most specific
        # ... more OpenHCS-specific names
```

**Solution**: Make it pluggable with default implementation:
```python
# Framework code
_config_priority_func = None

def set_config_priority_func(func: Callable[[Type], int]):
    """Set custom config priority function."""
    global _config_priority_func
    _config_priority_func = func

def _get_config_priority(config_type: Type) -> int:
    """Get priority level for config types."""
    if _config_priority_func:
        return _config_priority_func(config_type)
    
    # Default: use MRO depth (more derived = higher priority)
    return len(config_type.__mro__)
```

**OpenHCS initialization**:
```python
from openhcs.config_framework import set_config_priority_func

def openhcs_config_priority(config_type: Type) -> int:
    """OpenHCS-specific config priority."""
    config_name = config_type.__name__
    if 'Step' in config_name:
        if 'Materialization' in config_name:
            return 1
        # ... etc
    return 15

set_config_priority_func(openhcs_config_priority)
```

### 3. UI Formatting Utilities

**Location**: `openhcs/core/lazy_placeholder_simplified.py`

**Lines 135, 174**:
```python
try:
    from openhcs.ui.shared.ui_utils import format_enum_display
    formatted = format_enum_display(value)
except ImportError:
    formatted = str(value)
```

**Solution**: Already gracefully handled with try/except. No changes needed.

## Proposed Module Structure

```
openhcs/
├── config_framework/          # NEW: Standalone framework
│   ├── __init__.py           # Public API exports
│   ├── lazy_factory.py       # Lazy dataclass factory (from lazy_config.py)
│   ├── dual_axis_resolver.py # Dual-axis resolver (from dual_axis_resolver_recursive.py)
│   ├── context_manager.py    # Context management (from contextvars_context.py)
│   ├── placeholder.py        # Placeholder service (from lazy_placeholder_simplified.py)
│   ├── global_config.py      # Thread-local storage (from context/global_config.py)
│   ├── README.md             # Framework documentation
│   └── examples/             # Example usage
│       └── basic_usage.py
│
├── core/                      # OpenHCS-specific code
│   ├── config.py             # GlobalPipelineConfig and OpenHCS configs
│   ├── config_init.py        # NEW: Initialize framework with OpenHCS types
│   └── context/              # Keep for backward compatibility (re-exports)
│       ├── __init__.py
│       └── processing_context.py  # OpenHCS-specific processing context
│
└── pyqt_gui/
    └── widgets/
        └── shared/
            └── parameter_form_manager.py  # Uses framework
```

## Migration Plan

### Phase 1: Create Framework Module (1 hour)

1. Create `openhcs/config_framework/` directory
2. Copy files with new names:
   - `lazy_config.py` → `lazy_factory.py`
   - `dual_axis_resolver_recursive.py` → `dual_axis_resolver.py`
   - `contextvars_context.py` → `context_manager.py`
   - `lazy_placeholder_simplified.py` → `placeholder.py`
   - `context/global_config.py` → `global_config.py`

3. Update imports to be relative within framework:
   ```python
   # Before
   from openhcs.core.lazy_config import LazyDataclassFactory
   
   # After
   from .lazy_factory import LazyDataclassFactory
   ```

4. Create `__init__.py` with public API:
   ```python
   """
   Generic configuration framework for lazy dataclass resolution.
   
   This framework provides:
   - Lazy dataclass factory with dynamic field resolution
   - Dual-axis inheritance (context hierarchy + sibling inheritance)
   - Contextvars-based context management
   - Placeholder text generation for UI
   """
   
   from .lazy_factory import (
       LazyDataclassFactory,
       auto_create_decorator,
       register_lazy_type_mapping,
       get_base_type_for_lazy,
   )
   from .dual_axis_resolver import (
       resolve_field_inheritance,
       _has_concrete_field_override,
   )
   from .context_manager import (
       config_context,
       get_current_temp_global,
       merge_configs,
       extract_config_overrides,
   )
   from .placeholder import LazyDefaultPlaceholderService
   from .global_config import (
       set_current_global_config,
       get_current_global_config,
       set_global_config_for_editing,
   )
   
   # Configuration functions
   from .config import (
       set_base_config_type,
       set_config_priority_func,
   )
   
   __all__ = [
       # Factory
       'LazyDataclassFactory',
       'auto_create_decorator',
       'register_lazy_type_mapping',
       'get_base_type_for_lazy',
       # Resolver
       'resolve_field_inheritance',
       '_has_concrete_field_override',
       # Context
       'config_context',
       'get_current_temp_global',
       'merge_configs',
       'extract_config_overrides',
       # Placeholder
       'LazyDefaultPlaceholderService',
       # Global config
       'set_current_global_config',
       'get_current_global_config',
       'set_global_config_for_editing',
       # Configuration
       'set_base_config_type',
       'set_config_priority_func',
   ]
   ```

### Phase 2: Genericize Framework Code (30 minutes)

1. Add `config.py` to framework:
   ```python
   """Framework configuration."""
   from typing import Type, Callable, Optional
   
   _base_config_type: Optional[Type] = None
   _config_priority_func: Optional[Callable[[Type], int]] = None
   
   def set_base_config_type(config_type: Type):
       """Set the base config type for the framework."""
       global _base_config_type
       _base_config_type = config_type
   
   def get_base_config_type() -> Type:
       """Get the base config type."""
       if _base_config_type is None:
           raise RuntimeError("Base config type not set. Call set_base_config_type() first.")
       return _base_config_type
   
   def set_config_priority_func(func: Callable[[Type], int]):
       """Set custom config priority function."""
       global _config_priority_func
       _config_priority_func = func
   
   def get_config_priority_func() -> Optional[Callable[[Type], int]]:
       """Get the config priority function."""
       return _config_priority_func
   ```

2. Update `context_manager.py` to use `get_base_config_type()`:
   ```python
   def get_base_global_config():
       """Get base config from thread-local storage."""
       from .config import get_base_config_type
       from .global_config import get_current_global_config
       
       base_type = get_base_config_type()
       return get_current_global_config(base_type)
   ```

3. Update `dual_axis_resolver.py` to use pluggable priority:
   ```python
   def _get_config_priority(config_type: Type) -> int:
       """Get priority level for config types."""
       from .config import get_config_priority_func
       
       priority_func = get_config_priority_func()
       if priority_func:
           return priority_func(config_type)
       
       # Default: use MRO depth
       return len(config_type.__mro__)
   ```

### Phase 3: Update OpenHCS to Use Framework (30 minutes)

1. Create `openhcs/core/config_init.py`:
   ```python
   """Initialize config framework with OpenHCS types."""
   from openhcs.config_framework import set_base_config_type, set_config_priority_func
   from openhcs.core.config import GlobalPipelineConfig
   from typing import Type
   
   def openhcs_config_priority(config_type: Type) -> int:
       """OpenHCS-specific config priority."""
       config_name = config_type.__name__
       
       # Step-level configs (highest priority)
       if 'Step' in config_name:
           if 'Materialization' in config_name:
               return 1
           elif 'WellFilter' in config_name:
               return 2
           else:
               return 3
       
       # Pipeline-level configs
       elif config_name in ['PathPlanningConfig', 'WellFilterConfig', ...]:
           if 'PathPlanning' in config_name:
               return 10
           elif 'WellFilter' in config_name:
               return 11
           else:
               return 12
       
       # Global-level configs
       elif 'Global' in config_name:
           return 20
       
       return 15
   
   def initialize_config_framework():
       """Initialize config framework with OpenHCS types."""
       set_base_config_type(GlobalPipelineConfig)
       set_config_priority_func(openhcs_config_priority)
   ```

2. Call initialization in `openhcs/__init__.py`:
   ```python
   from openhcs.core.config_init import initialize_config_framework
   initialize_config_framework()
   ```

3. Update imports throughout OpenHCS:
   ```python
   # Before
   from openhcs.core.lazy_config import LazyDataclassFactory
   from openhcs.core.context.contextvars_context import config_context
   
   # After
   from openhcs.config_framework import LazyDataclassFactory, config_context
   ```

### Phase 4: Add Backward Compatibility (15 minutes)

Keep old import paths working:

```python
# openhcs/core/lazy_config.py
"""DEPRECATED: Use openhcs.config_framework instead."""
from openhcs.config_framework.lazy_factory import *

# openhcs/core/context/contextvars_context.py
"""DEPRECATED: Use openhcs.config_framework instead."""
from openhcs.config_framework.context_manager import *
```

## Benefits of Genericization

1. **Reusability**: Framework can be used in other projects
2. **Clarity**: Clear separation between framework and application code
3. **Testability**: Framework can be tested independently
4. **Documentation**: Framework can have its own documentation
5. **Maintenance**: Easier to maintain and evolve framework separately

## Next Steps

1. ✅ Complete this analysis
2. ⏳ Execute Phase 1: Create framework module
3. ⏳ Execute Phase 2: Genericize framework code
4. ⏳ Execute Phase 3: Update OpenHCS to use framework
5. ⏳ Execute Phase 4: Add backward compatibility
6. ⏳ Update documentation to reference new module structure
7. ⏳ Test everything
8. ⏳ Commit and prepare for PR

**Estimated Total Time**: 2-3 hours

