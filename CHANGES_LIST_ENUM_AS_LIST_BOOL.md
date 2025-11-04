# List[Enum] as "List of Bools" Pattern

## Summary

Updated `List[Enum]` checkbox group widgets to treat the parameter as a **list of independent boolean values** rather than a single atomic list. This ensures that when a user clicks ANY checkbox in the group, ALL checkboxes convert from placeholder state to concrete state, making the entire list concrete.

## Key Behavior Change

### Before (Atomic List Pattern)
- Each checkbox could independently be in placeholder or concrete state
- `get_selected_values()` returned `None` only if ALL checkboxes were placeholders
- Mixed states were possible (some placeholder, some concrete)
- Confusing semantics: what does it mean if OPTION_A is placeholder but OPTION_B is concrete?

### After (List of Bools Pattern)
- **When user clicks ANY checkbox, ALL checkboxes convert to concrete state**
- `get_selected_values()` returns `None` only if the user has never interacted with the widget
- Once the user starts editing, the entire list becomes concrete
- Clear semantics: either inheriting the entire list (None) or editing the entire list (concrete)

## Implementation Details

### 1. Signal Handler Enhancement

**File**: `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`

**Method**: `_connect_checkbox_group_signals()`

**Change**: When ANY checkbox is clicked, the signal handler now converts ALL checkboxes from placeholder to concrete:

```python
def handler(state):
    # CRITICAL: When user clicks ANY checkbox, convert ALL checkboxes to concrete
    # This implements "list of bools" behavior - editing one makes the whole list concrete
    for other_checkbox in widget._checkboxes.values():
        if hasattr(other_checkbox, '_is_placeholder') and other_checkbox._is_placeholder:
            # Convert placeholder to concrete by setting current displayed state
            other_checkbox._is_placeholder = False
            # Keep the current checked state (which shows the inherited value)
            # No need to call setChecked - it's already showing the right state
    
    # Clear placeholder state from the group widget itself
    PyQt6WidgetEnhancer._clear_placeholder_state(widget)
    
    # Get selected values (now all concrete)
    selected = widget.get_selected_values()
    callback(param_name, selected)
```

### 2. Simplified get_selected_values()

**File**: `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`

**Method**: `_create_checkbox_group_widget()` → `get_selected_values()`

**Change**: Simplified logic since we no longer have mixed states:

```python
def get_selected_values():
    """Get selected enum values, returning None if all checkboxes are in placeholder state.
    
    Treats List[Enum] like a list of independent bools:
    - If ALL checkboxes are in placeholder state → return None (inherit from parent)
    - If ANY checkbox has been clicked → ALL become concrete, return list of checked items
    
    Note: The signal handler ensures that clicking ANY checkbox converts ALL to concrete,
    so we should never have a mixed state (some placeholder, some concrete).
    """
    # Check if any checkbox has a concrete value (not placeholder)
    has_concrete_value = any(
        checkbox.get_value() is not None
        for checkbox in widget._checkboxes.values()
    )

    if not has_concrete_value:
        # All checkboxes are in placeholder state - return None to inherit from parent
        return None

    # All checkboxes are concrete (signal handler converted them)
    # Return list of enum values where checkbox is checked
    return [
        enum_val for enum_val, checkbox in widget._checkboxes.items()
        if checkbox.get_value() == True
    ]
```

## Example Scenarios

### Scenario 1: Initial State (Inherit from Parent)
```
Parent config has: [OPTION_A, OPTION_B]

Initial display:
☑ OPTION_A (grayed/placeholder)
☑ OPTION_B (grayed/placeholder)
☐ OPTION_C (grayed/placeholder)

get_selected_values() → None (inherit from parent)
```

### Scenario 2: User Clicks OPTION_C
```
User clicks OPTION_C to check it

After click:
☑ OPTION_A (concrete - kept inherited state)
☑ OPTION_B (concrete - kept inherited state)
☑ OPTION_C (concrete - user just checked it)

get_selected_values() → [OPTION_A, OPTION_B, OPTION_C]
```

### Scenario 3: User Unchecks OPTION_A
```
User unchecks OPTION_A

After click:
☐ OPTION_A (concrete - user just unchecked it)
☑ OPTION_B (concrete - converted when OPTION_A was clicked)
☑ OPTION_C (concrete - converted when OPTION_A was clicked)

get_selected_values() → [OPTION_B, OPTION_C]
```

### Scenario 4: Explicit Empty List
```
Config explicitly set to []

Initial display:
☐ OPTION_A (concrete)
☐ OPTION_B (concrete)
☐ OPTION_C (concrete)

get_selected_values() → []
```

## Benefits

1. **Clearer Semantics**: Either you're inheriting the entire list (None) or editing the entire list (concrete). No confusing mixed states.

2. **Consistent with Bool Pattern**: Single bool parameters work the same way - once you click, it becomes concrete.

3. **Intuitive UX**: Users expect that when they start editing a list, they're taking ownership of the entire list, not just individual items.

4. **Simpler Implementation**: No need to handle complex mixed-state logic.

5. **Proper Lazy Dataclass Behavior**: Can clearly distinguish between:
   - `None` - "I want to inherit the parent's list"
   - `[]` - "I explicitly want an empty list"
   - `[OPTION_A, OPTION_B]` - "I explicitly selected these values"

## Testing

Created comprehensive tests verifying:
- ✅ Initial placeholder state (all checkboxes placeholder, returns None)
- ✅ Explicit list initialization (creates concrete checkboxes)
- ✅ Clicking ANY checkbox converts ALL to concrete
- ✅ Empty list `[]` is different from `None`
- ✅ `get_selected_values()` returns correct values in all scenarios

All tests passed successfully! ✅

## Backward Compatibility

This change is **backward compatible** because:
- The API remains the same (`get_selected_values()` still returns `None` or `List[Enum]`)
- The initialization logic is unchanged
- The only difference is the behavior when the user interacts with the widget
- This new behavior is more intuitive and consistent with the rest of the GUI

## Files Modified

1. `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`
   - Updated `_connect_checkbox_group_signals()` to convert all checkboxes to concrete when any is clicked
   - Updated `get_selected_values()` with clearer documentation and simplified logic

## Related Documentation

- See `CHANGES_CHECKBOX_GROUP_CONSISTENCY.md` for the initial consistency fix
- This change builds on that work to implement the "list of bools" pattern

