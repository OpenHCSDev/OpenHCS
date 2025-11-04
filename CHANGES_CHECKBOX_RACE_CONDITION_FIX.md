# Checkbox Group Race Condition Fix

## Problem

In the StepEditor, List[Enum] checkbox groups exhibited a race condition where:
1. User clicks checkbox A → it becomes concrete with value `[A]`
2. User clicks checkbox B → checkbox A's value is LOST
3. Checkboxes would sometimes not toggle properly
4. Styling would be inconsistent

This issue did NOT occur in PipelineConfig editor, only in StepEditor.

## Root Cause

The issue was caused by **automatic placeholder refresh after every parameter change**:

### Line 326 in `parameter_form_manager.py`:
```python
self.parameter_changed.connect(lambda param_name, value: 
    self._refresh_with_live_context() if not getattr(self, '_in_reset', False) and param_name != 'enabled' else None)
```

### The Race Condition Sequence:

1. **User clicks checkbox A**
   - Signal fires, converts all checkboxes to concrete
   - Callback updates parameter to `[A]`
   - Emits `parameter_changed` signal

2. **`parameter_changed` triggers `_refresh_with_live_context()`**
   - Refreshes ALL placeholders for ALL parameters
   - Includes the checkbox group that was just edited

3. **Placeholder refresh re-applies placeholder logic**
   - Checks if current value (`[A]`) matches inherited value
   - If it doesn't match, it might reset the checkboxes
   - Or it might re-apply placeholder styling incorrectly

4. **User clicks checkbox B**
   - But checkbox A is now in an inconsistent state
   - Value gets corrupted or lost

### Why It Only Happened in StepEditor

- **StepEditor** has `context_obj=self.pipeline_config` (parent context for inheritance)
  - This enables live placeholder updates
  - Every parameter change triggers a full placeholder refresh

- **PipelineConfig** editor doesn't have the same parent context setup
  - Placeholder refresh logic is different
  - No automatic refresh after every change

## Solution

**Skip placeholder refresh for the parameter that just changed** (since it's a user edit, not an inherited value).

### Changes Made

#### 1. Updated `parameter_changed` connection (line 326)
```python
# CRITICAL: Pass the changed param_name so we can skip refreshing it (user just edited it, it's not inherited)
self.parameter_changed.connect(lambda param_name, value: 
    self._refresh_with_live_context(exclude_param=param_name) if not getattr(self, '_in_reset', False) and param_name != 'enabled' else None)
```

#### 2. Updated `_refresh_with_live_context()` signature
```python
def _refresh_with_live_context(self, live_context: dict = None, exclude_param: str = None) -> None:
    """Refresh placeholders using live context from other open windows.
    
    Args:
        live_context: Optional pre-collected live context. If None, will collect it.
        exclude_param: Optional parameter name to exclude from refresh (e.g., the param that just changed)
    """
```

#### 3. Updated `_refresh_all_placeholders()` signature and logic
```python
def _refresh_all_placeholders(self, live_context: dict = None, exclude_param: str = None) -> None:
    """Refresh placeholder text for all widgets in this form.
    
    Args:
        live_context: Optional dict mapping object instances to their live values from other open windows
        exclude_param: Optional parameter name to exclude from refresh (e.g., the param that just changed)
    """
    # ...
    for param_name, widget in self.widgets.items():
        # CRITICAL: Skip the parameter that just changed (user edited it, it's not inherited)
        if exclude_param and param_name == exclude_param:
            logger.info(f"🔍 SKIP REFRESH: {param_name} (user just edited it)")
            continue
        # ... rest of placeholder refresh logic
```

#### 4. Also Fixed: Signal Blocking in `_update_checkbox_group()`

Added signal blocking to prevent cascading signal loops:

```python
def _update_checkbox_group(self, widget: QWidget, value: Any) -> None:
    """Update checkbox group using set_value() pattern for proper placeholder handling.
    
    CRITICAL: Block signals on ALL checkboxes to prevent race conditions.
    Without signal blocking, set_value() triggers stateChanged signals which
    fire the user click handler, creating an infinite loop.
    """
    if not hasattr(widget, '_checkboxes'):
        return

    # CRITICAL: Block signals on ALL checkboxes before updating
    for checkbox in widget._checkboxes.values():
        checkbox.blockSignals(True)

    try:
        if value is None:
            # None means inherit from parent - set all checkboxes to placeholder state
            for checkbox in widget._checkboxes.values():
                checkbox.set_value(None)
        elif isinstance(value, list):
            # Explicit list - set concrete values using set_value()
            for enum_val, checkbox in widget._checkboxes.items():
                checkbox.set_value(enum_val in value)
    finally:
        # CRITICAL: Always unblock signals, even if there's an exception
        for checkbox in widget._checkboxes.values():
            checkbox.blockSignals(False)
```

## How It Works Now

### Correct Sequence:

1. **User clicks checkbox A**
   - Signal fires, converts all checkboxes to concrete
   - Callback updates parameter to `[A]`
   - Emits `parameter_changed(param_name="my_list_param", value=[A])`

2. **`parameter_changed` triggers `_refresh_with_live_context(exclude_param="my_list_param")`**
   - Refreshes placeholders for ALL parameters EXCEPT `my_list_param`
   - The checkbox group that was just edited is NOT refreshed
   - Other parameters get updated placeholders (in case they inherit from the changed value)

3. **User clicks checkbox B**
   - Checkbox A is still in concrete state with value `True`
   - Signal fires, gets selected values `[A, B]`
   - Callback updates parameter to `[A, B]`
   - Emits `parameter_changed(param_name="my_list_param", value=[A, B])`

4. **Again, `my_list_param` is excluded from refresh**
   - Checkbox group maintains its concrete state
   - No race condition!

## Benefits

1. **No More Race Conditions**: User edits are never overridden by placeholder refresh
2. **Consistent Behavior**: Checkbox groups work the same in StepEditor and PipelineConfig
3. **Proper State Management**: Concrete values stay concrete, placeholders stay placeholders
4. **Better Performance**: Skip unnecessary refresh of the parameter that just changed

## Testing

To test this fix:
1. Open StepEditor
2. Find a List[Enum] parameter (e.g., `sequential_components`)
3. Click one checkbox → should become checked and stay checked
4. Click another checkbox → both should stay checked
5. Uncheck one → should uncheck and stay unchecked
6. No weird toggling or value loss

## Additional Issue: Concrete Values Shown as Placeholders After Save/Load

### Problem

After fixing the race condition, a new issue appeared:
1. User sets `sequential_components = [PLATE, WELL]` in StepEditor
2. Saves and closes
3. Reopens StepEditor
4. The value shows as placeholder (grayed out) instead of concrete!

### Root Cause

The placeholder refresh logic (lines 2279-2302) was checking if the current value **matched** the inherited value, and if it did, applying placeholder styling even though the value was concrete!

```python
# OLD BUGGY CODE:
if not should_apply_placeholder and hasattr(widget, '_checkboxes'):
    # Check if current value matches the inherited value
    placeholder_text = self.service.get_placeholder_text(param_name, self.dataclass_type)
    if placeholder_text:
        # Extract inherited value and compare
        if set(current_values_str) == set(inherited_values):
            should_apply_placeholder = True  # ❌ WRONG!
```

This caused:
1. Step has concrete value `[PLATE, WELL]` (saved to disk)
2. Parent also has `[PLATE, WELL]`
3. Placeholder refresh sees they match → applies placeholder styling
4. Sets `widget.setProperty("is_placeholder_state", True)`
5. `get_widget_value()` checks this property and returns `None` instead of `[PLATE, WELL]`!

### The Fundamental Problem

**We cannot distinguish between "user explicitly set this to match parent" vs "user is inheriting from parent" just by comparing values.**

In lazy dataclasses:
- `None` means "inherit from parent"
- Concrete value means "I explicitly set this, don't inherit"

If we apply placeholder styling to concrete values that happen to match the parent, we lose the distinction!

### Solution

**Only apply placeholder styling if `current_value is None`**, never if it's a concrete value that matches the parent.

```python
# NEW CORRECT CODE:
# CRITICAL: Only apply placeholder styling if current_value is None
# Do NOT apply placeholder styling if value matches parent - that would make
# concrete values appear as placeholders, breaking save/load!
should_apply_placeholder = current_value is None or widget_in_placeholder_state
```

### Why This Is Correct

- If the step has `sequential_components = None` → inherit from parent → show placeholder ✅
- If the step has `sequential_components = [PLATE, WELL]` → concrete value → show as concrete ✅
- Even if parent also has `[PLATE, WELL]`, the step's value is still concrete, not inherited

The user explicitly set it, so we should show it as concrete, not as a placeholder.

## Files Modified

1. `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`
   - Line 326: Pass `exclude_param` to `_refresh_with_live_context()`
   - Line 2214: Add `exclude_param` parameter to `_refresh_with_live_context()`
   - Line 2240: Add `exclude_param` parameter to `_refresh_all_placeholders()`
   - Line 2262-2266: Skip refresh for excluded parameter
   - Line 1254-1284: Add signal blocking to `_update_checkbox_group()`
   - **Line 2270-2280: Remove "matching value" logic that incorrectly applied placeholder styling to concrete values**

## Related Documentation

- See `CHANGES_LIST_ENUM_AS_LIST_BOOL.md` for the "list of bools" pattern
- See `CHANGES_CHECKBOX_GROUP_CONSISTENCY.md` for the initial consistency fix

