# List[Enum] Checkbox Group Consistency Fix

## Summary

Fixed `List[Enum]` checkbox group widgets to use the same `NoneAwareCheckBox` pattern as boolean parameters, ensuring consistent handling of placeholder states and proper distinction between `None` (inherit from parent) and explicit values.

## Problem

The `List[Enum]` checkbox group implementation had inconsistencies compared to the boolean parameter pattern:

### 1. Widget Initialization Inconsistency

**Boolean parameters** used `set_value()`:
```python
bool: lambda current_value, **kwargs: (
    lambda w: (w.set_value(current_value), w)[1]  # ✅ Uses set_value()
)(_create_none_aware_checkbox())
```

**List[Enum] parameters** used `setChecked()` directly:
```python
if current_value and isinstance(current_value, list):
    for enum_value in current_value:
        if enum_value in widget._checkboxes:
            widget._checkboxes[enum_value].setChecked(True)  # ❌ Direct setChecked()
```

**Impact**: Using `setChecked()` directly bypassed the `NoneAwareCheckBox.set_value()` method, which meant:
- The `_is_placeholder` flag was never properly initialized
- `None` values weren't handled correctly
- Checkboxes couldn't distinguish between placeholder state and concrete state

### 2. Value Retrieval Inconsistency

**Boolean parameters** used `get_value()`:
```python
def get_value(self):
    """Get value, returning None if in placeholder state."""
    if self._is_placeholder:
        return None  # ✅ Returns None for placeholder
    return self.isChecked()
```

**List[Enum] parameters** used `isChecked()` directly:
```python
def get_selected_values():
    return [enum_val for enum_val, checkbox in widget._checkboxes.items()
            if checkbox.isChecked()]  # ❌ Uses isChecked() directly
```

**Impact**: The `get_selected_values()` method couldn't distinguish between:
- `None` - "I want to inherit the parent's list"
- `[]` - "I explicitly want an empty list"
- `[OPTION_A, OPTION_B]` - "I explicitly selected these values"

## Solution

### Changes Made

#### 1. Updated `_create_checkbox_group_widget()` in `widget_strategies.py`

**File**: `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`

- **Use `set_value()` for initialization** instead of `setChecked()`:
  ```python
  if current_value is None:
      # None means inherit from parent - initialize all checkboxes in placeholder state
      for checkbox in widget._checkboxes.values():
          checkbox.set_value(None)
  elif isinstance(current_value, list):
      # Explicit list - set concrete values
      for enum_value, checkbox in widget._checkboxes.items():
          checkbox.set_value(enum_value in current_value)
  ```

- **Updated `get_selected_values()` to use `get_value()` pattern**:
  ```python
  def get_selected_values():
      """Get selected enum values, returning None if all checkboxes are in placeholder state."""
      # Check if any checkbox has a concrete value (not placeholder)
      has_concrete_value = any(
          checkbox.get_value() is not None 
          for checkbox in widget._checkboxes.values()
      )
      
      if not has_concrete_value:
          # All checkboxes are in placeholder state - return None to inherit from parent
          return None
      
      # Return list of enum values where checkbox is checked (get_value() == True)
      return [
          enum_val for enum_val, checkbox in widget._checkboxes.items()
          if checkbox.get_value() == True
      ]
  ```

#### 2. Updated `_update_checkbox_group()` in `parameter_form_manager.py`

**File**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

- **Use `set_value()` for updates** instead of `setChecked()`:
  ```python
  def _update_checkbox_group(self, widget: QWidget, value: Any) -> None:
      """Update checkbox group using set_value() pattern for proper placeholder handling."""
      if not hasattr(widget, '_checkboxes'):
          return
      
      if value is None:
          # None means inherit from parent - set all checkboxes to placeholder state
          for checkbox in widget._checkboxes.values():
              checkbox.set_value(None)
      elif isinstance(value, list):
          # Explicit list - set concrete values using set_value()
          for enum_val, checkbox in widget._checkboxes.items():
              checkbox.set_value(enum_val in value)
  ```

#### 3. Updated signal handler logging in `widget_strategies.py`

**File**: `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`

- **Handle `None` values in logging**:
  ```python
  def handler(state):
      selected = widget.get_selected_values()
      # Handle None (placeholder state) in logging
      selected_str = "None (inherit from parent)" if selected is None else [v.name for v in selected]
      logger.info(f"🔘 Checkbox {cb.text()} changed to {state}, selected values: {selected_str}")
      PyQt6WidgetEnhancer._clear_placeholder_state(widget)
      callback(param_name, selected)
  ```

## Benefits

### 1. Consistent API
- Both `bool` and `List[Enum]` parameters now use the same `set_value()`/`get_value()` pattern
- Easier to understand and maintain

### 2. Proper Placeholder State Handling
- `None` values are properly tracked using the `_is_placeholder` flag
- Users can distinguish between "inherit from parent" and "explicit empty list"

### 3. Correct Lazy Dataclass Behavior
- Checkbox groups now properly participate in the lazy dataclass placeholder system
- Inherited values are shown with visual dimming (via `NoneAwareCheckBox.paintEvent()`)
- Clicking a checkbox clears the placeholder state and sets a concrete value

### 4. Type Safety
- `get_selected_values()` now returns `None | List[Enum]` instead of always returning a list
- This matches the type signature of the parameter (`Optional[List[Enum]]`)

## Testing

Created and ran comprehensive tests (`test_checkbox_group_fix.py`) that verify:

1. ✅ Creating widget with `None` initializes all checkboxes in placeholder state
2. ✅ Creating widget with `[]` creates unchecked checkboxes (not placeholder)
3. ✅ Creating widget with `[OPTION_A, OPTION_C]` creates properly checked/unchecked checkboxes
4. ✅ `get_selected_values()` returns `None` when all checkboxes are in placeholder state
5. ✅ `get_selected_values()` returns proper list when checkboxes have concrete values
6. ✅ Updating widget to `None` sets all checkboxes to placeholder state
7. ✅ Updating widget to explicit list sets concrete values

All tests passed successfully.

## Backward Compatibility

These changes are **backward compatible** because:

1. The external API (`get_selected_values()`) remains the same
2. The widget structure (`_checkboxes` dict) remains the same
3. Signal connections remain the same
4. The only change is internal implementation details

However, the **behavior** changes slightly:
- **Before**: `get_selected_values()` always returned a list (even for placeholder state)
- **After**: `get_selected_values()` returns `None` for placeholder state, list for concrete values

This is the **correct** behavior for lazy dataclass contexts and matches the boolean parameter pattern.

## Files Modified

1. `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`
   - `_create_checkbox_group_widget()` method
   - `_connect_checkbox_group_signals()` method

2. `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`
   - `_update_checkbox_group()` method

## Related Code (No Changes Needed)

The following code already works correctly with these changes:

- `NoneAwareCheckBox` class - already implements `get_value()`/`set_value()` pattern
- `_apply_checkbox_placeholder()` - correctly uses `setChecked()` with signal blocking for visual preview
- `_apply_checkbox_group_placeholder()` - delegates to `_apply_checkbox_placeholder()` for each checkbox
- Signal connection registry - already uses `get_selected_values()`
- Widget update/get dispatch tables - already use `get_selected_values()`

## Future Improvements

Consider adding:
1. Unit tests in the test suite (currently only manual test script)
2. Integration tests for placeholder state transitions
3. Documentation for the `NoneAwareCheckBox` pattern

