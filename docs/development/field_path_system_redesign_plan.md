# Field Path System Refactor: Eliminate String Prefix Hack

## ARCHITECTURAL PRINCIPLE: Visual Programming Framework

OpenHCS is a **visual programming framework** where the UI must directly reflect the code structure. The current string prefix hack (`"nested_"`) violates this principle by creating artificial naming that doesn't match the actual dataclass hierarchy.

## Current System Analysis

### Existing Field Path Infrastructure

**FieldPathDetector** (`openhcs/core/field_path_detection.py`):
- Already handles dot-separated field paths: `"well_filter_config"`, `"step_materialization_config"`
- Auto-discovers field paths using type introspection
- Provides `find_field_path_for_type()` and `find_all_field_paths_unified()`

**FieldPathNavigator** (`openhcs/core/lazy_config.py`):
- Already navigates dot-separated paths: `field_path.split('.')`
- Used throughout lazy config system for field resolution

**Context Structure (GlobalPipelineConfig)**:
```python
@dataclass
class GlobalPipelineConfig:
    num_workers: int = 1
    # Nested dataclass fields (auto-injected by decorators)
    well_filter_config: WellFilterConfig = field(default_factory=WellFilterConfig)
    zarr_config: ZarrConfig = field(default_factory=ZarrConfig)
    step_materialization_config: StepMaterializationConfig = field(default_factory=StepMaterializationConfig)
```

### Current UI Naming Problem

**BROKEN: String Prefix Hack**:
- Form manager field_id: `"nested_well_filter_config"` ❌
- Context field name: `"well_filter_config"` ✅
- Requires fragile string manipulation: `form_field_name[7:]` ❌

**CORRECT: Direct Field Path Mapping**:
- Form manager field_id: `"well_filter_config"` ✅
- Context field name: `"well_filter_config"` ✅
- No string manipulation needed ✅

## Refactor Strategy: Use Existing FieldPathDetector

### Leverage Existing Infrastructure

Instead of creating new path utilities, **use the existing field path system**:

1. **FieldPathDetector.find_field_path_for_type()** - Auto-discovers field paths
2. **FieldPathNavigator.navigate_to_instance()** - Navigates dot-separated paths
3. **Existing lazy config field paths** - Already proven and battle-tested

### New UI Field Path Format

**Use actual dataclass field paths directly**:
```python
# Form manager field_id = actual context field name
"well_filter_config"           # matches context.well_filter_config
"zarr_config"                  # matches context.zarr_config
"step_materialization_config"  # matches context.step_materialization_config

# Widget names = field_id + parameter
"well_filter_config_well_filter"           # well_filter_config.well_filter
"zarr_config_store_name"                   # zarr_config.store_name
"step_materialization_config_well_filter"  # step_materialization_config.well_filter
```

### Mathematical Elegance

**O(1) field resolution** - Direct attribute access:
```python
# BEFORE: String manipulation
if form_field_name.startswith('nested_'):
    context_field_name = form_field_name[7:]  # O(n) string operation

# AFTER: Direct mapping
context_field_name = form_field_id  # O(1) identity operation
```

## Implementation Plan

### Phase 1: Update Field ID Generation

**Eliminate `generate_field_ids()` entirely**:
```python
# REMOVE: The entire generate_field_ids() method is architectural debt
# Field IDs should be the actual dataclass field names, period.

# REPLACE WITH: Direct field path usage in nested manager creation
def _create_nested_form_inline(self, param_name: str, param_type: Type, current_value: Any) -> Any:
    """Create nested form - use actual field path instead of artificial field IDs"""

    # Get actual field path from FieldPathDetector (no artificial "nested_" prefix)
    field_path = FieldPathDetector.find_field_path_for_type(
        self.dataclass_type,  # Use existing dataclass_type directly - no helper method needed
        param_type
    )

    # FAIL LOUD: If FieldPathDetector can't find the path, the architecture is broken
    if not field_path:
        raise ValueError(f"FieldPathDetector could not find field path for type {param_type} in {self.dataclass_type}. "
                        f"This indicates the dataclass is not properly registered or the type is incorrect.")

    # Extract nested parameters using service
    nested_params, nested_types = self.service.extract_nested_parameters(
        current_value, param_type, self.dataclass_type
    )

    # Create nested manager with actual field path (no artificial field ID generation)
    nested_manager = ParameterFormManager(
        nested_params,
        nested_types,
        field_path,  # Use actual dataclass field name directly
        param_type,
        None,  # parameter_info
        None,  # parent
        False,  # use_scroll_area
        None,   # function_target
        PyQt6ColorScheme(),  # color_scheme
        self.placeholder_prefix
    )

    return nested_manager
```

### Phase 2: Update Context Building

**Remove string manipulation from `_build_context_from_current_form_values()`**:
```python
def _build_context_from_current_form_values(self, exclude_field: str = None) -> Any:
    # Get current context
    current_context = get_current_global_config(GlobalPipelineConfig)

    # CRITICAL CHANGE: Direct field mapping (no prefix stripping)
    context_field_name = self.field_id  # Direct mapping!

    if hasattr(current_context, context_field_name):
        current_dataclass_instance = getattr(current_context, context_field_name)
        # ... rest of context building logic unchanged
```

### Phase 3: Update Form Manager Creation

**Use FieldPathDetector with fail-loud behavior**:
```python
# NO SEPARATE METHOD NEEDED - integrate directly into existing _create_nested_form_inline()
# The dataclass_type is already available as self.dataclass_type (GlobalPipelineConfig or PipelineConfig)
# No need for get_root_config_type() - it's just self.dataclass_type

# Widget names are constructed directly from field paths:
def format_widget_name(field_path: str, param_name: str) -> str:
    """Convert field path to widget name - replaces generate_field_ids() complexity"""
    return f"{field_path}_{param_name}"

# Examples:
# field_path="well_filter_config", param_name="well_filter"
# → widget_name="well_filter_config_well_filter"
```

### Phase 4: Validation and Testing

**Verify Field Path Mapping**:
```python
def validate_field_path_mapping():
    """Ensure all form field_ids map correctly to context fields"""
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.core.field_path_detection import FieldPathDetector
    import dataclasses

    # Get all dataclass fields from GlobalPipelineConfig
    context_fields = {f.name for f in dataclasses.fields(GlobalPipelineConfig)
                     if dataclasses.is_dataclass(f.type)}

    print("Context fields:", context_fields)
    # Should include: well_filter_config, zarr_config, step_materialization_config, etc.

    # Verify FieldPathDetector can find all these types
    for field in dataclasses.fields(GlobalPipelineConfig):
        if dataclasses.is_dataclass(field.type):
            field_path = FieldPathDetector.find_field_path_for_type(GlobalPipelineConfig, field.type)
            assert field_path == field.name, f"FieldPathDetector mismatch: {field_path} != {field.name}"
```

## Benefits of This Refactor

### 1. **Visual Programming Alignment**
- UI field paths **directly match** dataclass structure
- No artificial naming that obscures the code relationship
- Form managers reflect actual configuration hierarchy

### 2. **Architectural Cleanliness**
- **Eliminates string manipulation** hack completely
- **O(1) field resolution** through direct attribute access
- **Uses existing FieldPathDetector** infrastructure

### 3. **Maintainability**
- **Self-documenting** field paths that match code structure
- **Easier debugging** with explicit field identification
- **Leverages proven infrastructure** instead of creating new systems

## Root Config vs Nested Config Patterns

### Root Config Field ID Pattern
**Use dataclass type name for root configurations**:
```python
# CORRECT: Root config uses dataclass type name
root_field_id = type(current_config).__name__  # "GlobalPipelineConfig"
form_manager = ParameterFormManager.from_dataclass_instance(
    dataclass_instance=current_config,
    field_id=root_field_id,  # Self-documenting, matches actual type
    placeholder_prefix=placeholder_prefix
)

# WRONG: Artificial field_id that doesn't exist in dataclass structure
form_manager = ParameterFormManager.from_dataclass_instance(
    dataclass_instance=current_config,
    field_id="config",  # ❌ GlobalPipelineConfig has no "config" field
    placeholder_prefix=placeholder_prefix
)
```

### Generic Root vs Nested Detection
**Use hasattr() for generic detection without hardcoding class names**:
```python
def _build_context_from_current_form_values(self, exclude_field=None):
    current_context = get_current_global_config(GlobalPipelineConfig)

    # Generic detection - works for any dataclass hierarchy
    if hasattr(current_context, self.field_id):
        # Nested config: field_id exists as actual field in context
        # Examples: "well_filter_config", "zarr_config", "step_materialization_config"
        current_dataclass_instance = getattr(current_context, self.field_id)
    else:
        # Root config: field_id doesn't exist as field in context
        # Examples: "GlobalPipelineConfig", "PipelineConfig", "LazyStepMaterializationConfig"
        current_dataclass_instance = current_context
```

### Context Update Strategy
**Handle root config updates differently from nested config updates**:
```python
# Nested config: Update specific field in context
if hasattr(current_context, self.field_id):
    context_updates[self.field_id] = updated_instance
    return replace(current_context, **context_updates)
else:
    # Root config: Replace entire context with nested updates applied
    if context_updates:
        return replace(updated_instance, **context_updates)
    else:
        return updated_instance
```

### 4. **Extensibility**
- **Works with arbitrary nesting** through FieldPathDetector
- **Automatic field path discovery** adapts to config changes
- **Future-proof** for deeper configuration hierarchies

## Migration Strategy

### Step 1: Eliminate Field ID Generation (IMMEDIATE)

**Target**: `openhcs/ui/shared/parameter_form_service.py`
```python
# REMOVE: The entire generate_field_ids() method - it's architectural debt
# Field IDs should be actual dataclass field names from FieldPathDetector, period.

# Widget names should be constructed directly from field paths:
def format_widget_name(field_path: str, param_name: str) -> str:
    """Convert field path to widget name - single line, no complexity"""
    return f"{field_path}_{param_name}"

# Examples:
# field_path="well_filter_config", param_name="well_filter"
# → widget_name="well_filter_config_well_filter"

# NO ARTIFICIAL FIELD ID GENERATION - use actual dataclass field names directly
```

### Step 2: Remove String Manipulation (IMMEDIATE)

**Target**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`
```python
def _build_context_from_current_form_values(self, exclude_field: str = None):
    # REMOVE: String prefix stripping hack
    # if form_field_name.startswith('nested_'):
    #     context_field_name = form_field_name[7:]

    # REPLACE WITH: Direct mapping
    context_field_name = self.field_id
```

### Step 3: Use FieldPathDetector with Fail-Loud (CRITICAL)

**Target**: Nested form manager creation in `_create_nested_form_inline()`
```python
# Use FieldPathDetector with fail-loud behavior - no helper method needed
# self.dataclass_type is already available (GlobalPipelineConfig or PipelineConfig)
field_path = FieldPathDetector.find_field_path_for_type(self.dataclass_type, param_type)

# FAIL LOUD: No fallbacks, no defensive programming
if not field_path:
    raise ValueError(f"FieldPathDetector failed to find field path for {param_type} in {self.dataclass_type}. "
                    f"Architecture is broken - fix the dataclass registration.")

# Use actual field path directly - no artificial "nested_" prefix
nested_manager = ParameterFormManager(..., field_id=field_path, ...)
```

### Step 4: Validation (TESTING)

**Add validation** to ensure field paths match context structure:
```python
def validate_ui_field_paths(root_config_type):
    """Ensure UI field paths match dataclass structure exactly"""
    from openhcs.core.field_path_detection import FieldPathDetector
    import dataclasses

    # Verify FieldPathDetector can find all dataclass types
    for field in dataclasses.fields(root_config_type):
        if dataclasses.is_dataclass(field.type):
            field_path = FieldPathDetector.find_field_path_for_type(root_config_type, field.type)
            assert field_path == field.name  # Direct mapping, no prefixes
```

## Why This Approach is Correct

### 1. **Leverages Existing Infrastructure**
- Uses proven `FieldPathDetector` and `FieldPathNavigator`
- No duplication of existing field path functionality
- Builds on battle-tested lazy config system

### 2. **Minimal, Surgical Changes**
- Remove string manipulation hack
- Use FieldPathDetector for field path discovery
- No massive refactoring required

### 3. **Visual Programming Principle**
- UI field paths **directly match** dataclass structure
- Form managers use **actual field names** from code
- No artificial naming that obscures relationships

### 4. **Future-Proof Architecture**
- Works with arbitrary nesting through existing FieldPathDetector
- Automatic adaptation to configuration structure changes
- Extensible without complexity growth

### 5. **Fail-Loud Behavior**
- No defensive programming or fallbacks
- Forces architectural correctness
- Exposes problems immediately instead of hiding them

This refactor **eliminates the architectural debt** of string prefix manipulation while leveraging OpenHCS's existing, proven field path infrastructure.

## Implementation Validation

### Final Step: Rerun the Passing Test

After implementing all changes, **rerun the test that was just passing** to ensure the refactor doesn't break existing functionality:

```bash
cd /home/ts/code/projects/openhcs && python -m pytest tests/pyqt_gui/functional/test_reset_placeholder_simplified.py::TestResetPlaceholderInheritance::test_comprehensive_inheritance_chains -v -s --tb=short -x
```

**Expected Result**: Test should continue to pass with the new field path architecture.

**If test fails**: The refactor exposed an architectural problem that needs to be fixed (no defensive programming - fix the root cause).

### Generic Root Config Type

**No helper method needed - use existing dataclass_type**:
```python
# BEFORE: Hardcoded (WRONG)
field_path = FieldPathDetector.find_field_path_for_type(GlobalPipelineConfig, param_type)

# AFTER: Use existing dataclass_type directly (CORRECT)
field_path = FieldPathDetector.find_field_path_for_type(self.dataclass_type, param_type)
```

This ensures the field path system works with **any dataclass hierarchy**, not just GlobalPipelineConfig. The `self.dataclass_type` is already available in ParameterFormManager and contains the correct root config type (GlobalPipelineConfig or PipelineConfig).
