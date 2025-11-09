# Lazy Dataclass Code Editor Fix

## Problem Summary

When using code mode to edit nested lazy dataclass fields, **all** nested fields were being set to concrete values, even fields that weren't explicitly set in the code.

### Example of the Bug

```python
# User sets only well_filter in code mode:
config = PipelineConfig(
    well_filter_config=LazyWellFilterConfig(
        well_filter=3,
    )
)
```

**Expected behavior:**
- `well_filter` = `3` ✅
- `well_filter_mode` = `None` (stays lazy/placeholder) ✅

**Actual behavior (before fix):**
- `well_filter` = `3` ✅
- `well_filter_mode` = `WellFilterMode.INCLUDE` (default value) ❌

## Root Cause

The issue had **two parts**:

### Part 1: Lazy Dataclass Constructors Fill in Defaults

When executing `LazyWellFilterConfig(well_filter=3)` during `exec()`, the lazy dataclass constructor was filling in default values for all unspecified fields:

```python
# What was created:
LazyWellFilterConfig(
    well_filter=3,
    well_filter_mode=WellFilterMode.INCLUDE  # Default was auto-filled!
)
```

### Part 2: Form Update Logic Updated ALL Nested Fields

The form update logic was updating **every field** in the nested dataclass, not just the explicitly set ones:

```python
# Old buggy code:
for field in fields(new_value):  # Iterates ALL fields!
    nested_manager.update_parameter(field.name, getattr(new_value, field.name))
```

This meant even if constructor patching worked, the form updater would still overwrite all fields.

## The Solution

All fixes were consolidated into **one central utility**: [`CodeEditorFormUpdater`](../openhcs/ui/shared/code_editor_form_updater.py)

### Three Key Methods

1. **`extract_explicitly_set_fields(code, class_name, variable_name)`**
   - Parses code to find which fields appear in the constructor
   - Returns: `{'well_filter_config', 'well_filter'}` (parent and nested fields)

2. **`patch_lazy_constructors()` (context manager)**
   - Temporarily patches all lazy dataclass constructors during `exec()`
   - Makes constructors only set explicitly passed kwargs to field values
   - Unset fields get `None` instead of defaults

3. **`update_form_from_instance(form_manager, instance, explicitly_set_fields)`**
   - Works with both dataclasses (e.g., `PipelineConfig`) and regular objects (e.g., `FunctionStep`)
   - Updates **only** the fields in `explicitly_set_fields`
   - Uses `_store_parameter_value()` for parent fields (no widget trigger)
   - Recursively updates nested fields selectively

### Usage Pattern

```python
# Extract what was set
explicitly_set_fields = CodeEditorFormUpdater.extract_explicitly_set_fields(
    edited_code,
    class_name='PipelineConfig',
    variable_name='config'
)

# Execute with patched constructors
namespace = {}
with CodeEditorFormUpdater.patch_lazy_constructors():
    exec(edited_code, namespace)

new_config = namespace['config']

# Update only explicitly set fields
CodeEditorFormUpdater.update_form_from_instance(
    form_manager,
    new_config,
    explicitly_set_fields
)
```

## Files Modified

### Core Fix (Single Source of Truth)

- **[`openhcs/ui/shared/code_editor_form_updater.py`](../openhcs/ui/shared/code_editor_form_updater.py)**
  - Added `patch_lazy_constructors()` static method (lines 178-231)
  - Fixed `_update_nested_dataclass()` to use `explicitly_set_fields` (lines 103-136)
  - Fixed `_update_nested_dataclass_in_manager()` to use `explicitly_set_fields` (lines 138-169)

### Updated to Use Shared Utility

- **[`openhcs/pyqt_gui/widgets/step_parameter_editor.py`](../openhcs/pyqt_gui/widgets/step_parameter_editor.py)**
  - `_handle_edited_step_code()` now uses `CodeEditorFormUpdater` (lines 558-626)
  - Removed duplicate `_patch_lazy_constructors()` method
  - Removed duplicate `_update_nested_dataclass()` methods

- **[`openhcs/pyqt_gui/windows/config_window.py`](../openhcs/pyqt_gui/windows/config_window.py)**
  - `_handle_edited_config_code()` uses `CodeEditorFormUpdater.patch_lazy_constructors()` (line 515)
  - `_update_form_from_config()` uses `CodeEditorFormUpdater.update_form_from_instance()` (lines 543-548)
  - Removed duplicate `_patch_lazy_constructors()` method
  - Removed duplicate `_update_nested_dataclass()` methods

## Benefits of Centralized Approach

✅ **Single fix point** - All code editors benefit from the same fix
✅ **No code duplication** - Removed ~150 lines of duplicate code
✅ **Future-proof** - New code editors just need to use `CodeEditorFormUpdater`
✅ **Consistent behavior** - All editors handle nested lazy dataclasses identically
✅ **Easy to test** - All logic in one testable utility class

## Other Code Editors

These editors already use compatible approaches and continue to work:

- **[`openhcs/pyqt_gui/widgets/pipeline_editor.py`](../openhcs/pyqt_gui/widgets/pipeline_editor.py)**
  - Has its own `_patch_lazy_constructors()` (lines 783-835)
  - Could be migrated to use shared utility in future

- **[`openhcs/pyqt_gui/widgets/plate_manager.py`](../openhcs/pyqt_gui/widgets/plate_manager.py)**
  - Has its own `_patch_lazy_constructors()` (similar pattern)
  - Could be migrated to use shared utility in future

## Testing

To verify the fix works:

1. Open any config/step editor with nested lazy dataclass fields
2. Click "Code" button
3. Set a nested field: `LazyWellFilterConfig(well_filter=3)`
4. Save the code
5. Verify:
   - Explicitly set field (`well_filter`) shows concrete value ✅
   - Unset fields (`well_filter_mode`) remain `None`/lazy ✅

## Technical Details

### Constructor Patching Implementation

The `patch_lazy_constructors()` method:

1. Discovers all lazy dataclass types from `openhcs.core.config`
2. Temporarily replaces `__init__` with a patched version
3. Patched `__init__` sets only explicitly passed kwargs:
   ```python
   for field in dataclasses.fields(dataclass_type):
       value = kwargs.get(field.name, None)  # None if not in kwargs!
       object.__setattr__(self, field.name, value)
   ```
4. Restores original `__init__` methods after `exec()`

### Selective Field Update Implementation

The `_update_nested_dataclass()` method:

1. Stores the dataclass instance value (doesn't trigger widget updates)
2. Gets the nested form manager
3. Only updates widgets for fields in `explicitly_set_fields`:
   ```python
   for field in fields(new_value):
       if field.name in explicitly_set_fields:  # Only these!
           nested_manager.update_parameter(field.name, value)
   ```

This prevents widgets from being updated with default values for unset fields.
