# Fix for Nested Enabled Field Styling Bug

## Problem
Critical bug where toggling a nested dataclass's `enabled` field caused incorrect styling changes for the entire form, including parents and siblings.

### Scenario
```
Parent Form (has enabled field)
├── Nested Dataclass A (has enabled field)  
└── Nested Dataclass B (has enabled field)
```

When toggling Nested Dataclass A's `enabled` field:
- ❌ Parent form's styling changed incorrectly
- ❌ Sibling Dataclass B's styling changed incorrectly
- ✅ Only Nested Dataclass A's styling should change

## Root Cause
The bug occurred due to signal propagation in `ParameterFormManager`:

1. Nested form changes its `enabled` field → emits `parameter_changed('enabled', value)`
2. Signal propagates to parent via `_on_nested_parameter_changed`
3. Parent re-emits the signal: `parameter_changed.emit('enabled', value)`
4. Parent's `_on_enabled_field_changed_universal` handler is triggered (because param_name == 'enabled')
5. **BUG**: Parent incorrectly applies styling changes thinking its own `enabled` field changed

Additionally, the parent was refreshing ALL nested managers' styling whenever ANY nested parameter changed, causing unnecessary cascade effects.

## Solution

### Fix 1: Flag Propagated Signals
Added `_propagating_nested_enabled` flag in `_on_nested_parameter_changed`:

```python
# In _on_nested_parameter_changed (line ~2227)
if param_name == 'enabled':
    self._propagating_nested_enabled = True

self.parameter_changed.emit(param_name, value)

if param_name == 'enabled':
    self._propagating_nested_enabled = False
```

### Fix 2: Ignore Propagated Signals in Handler
Modified `_on_enabled_field_changed_universal` to check the flag:

```python
# In _on_enabled_field_changed_universal (line ~2009)
# Ignore propagated 'enabled' signals from nested forms
if getattr(self, '_propagating_nested_enabled', False):
    logger.info(f"[ENABLED HANDLER] field_id={self.field_id}, ignoring propagated 'enabled' signal")
    return

# Also check if this form actually has an enabled parameter
if 'enabled' not in self.parameters:
    logger.info(f"[ENABLED HANDLER] field_id={self.field_id}, ignoring 'enabled' signal")
    return
```

### Fix 3: Selective Sibling Refresh
Modified `_on_nested_parameter_changed` to only refresh siblings when needed:

```python
# In _on_nested_parameter_changed (line ~2216)
# Only refresh siblings if the changed param is 'enabled'
if param_name == 'enabled' and emitting_manager_name:
    logger.info(f"🔄 Nested 'enabled' field changed in {emitting_manager_name}, refreshing sibling styling")
    self._apply_to_nested_managers(
        lambda name, manager: manager._refresh_enabled_styling()
        if name != emitting_manager_name
        else logger.info(f"⏭️ Skipping enabled refresh of {name}")
    )
```

## Changes Made

### File: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

1. **Line ~2009-2024**: Enhanced `_on_enabled_field_changed_universal` to check for propagated signals
2. **Line ~2127-2155**: Fixed restoration logic to properly restore ALL nested widgets (including reset buttons) when parent is re-enabled
3. **Line ~2216-2226**: Modified sibling refresh logic to be selective
4. **Line ~2227-2244**: Added flag mechanism for signal propagation

### Specific Fixes

#### Fix 1: Prevent Propagated Signal Handling
Added checks to ignore 'enabled' signals that come from nested forms being propagated up.

#### Fix 2: Complete Widget Restoration with State Awareness
When parent form is re-enabled (`enabled=True`), the code now intelligently restores nested forms:

**Before (buggy):** Restored ALL nested widgets unconditionally, then tried to re-dim some

**After (fixed):** 
1. Check each nested form's state:
   - Skip if Optional dataclass with `None` value (checkbox unchecked) → keep dimmed
   - Skip if nested form has its own `enabled=False` → keep dimmed
   - Otherwise → safe to restore
2. For restorable nested forms:
   - Remove dimming from ALL widgets in the GroupBox (including reset buttons)
   - Recursively call `_refresh_enabled_styling()` for deeply nested forms

This ensures:
- Optional dataclasses with `None` stay dimmed when parent is re-enabled ✓
- Nested forms with `enabled=False` stay dimmed when parent is re-enabled ✓
- Other nested forms (without enabled field or with `enabled=True`) are fully restored ✓
- Reset buttons and all widgets in restorable nested forms are properly shown ✓

#### Fix 3: Selective Sibling Refresh
Only refresh sibling styling when specifically needed for `enabled` field changes.

## Testing
Created `test_nested_enabled_styling_fix.py` to verify the fix handles three scenarios:
1. ✓ Nested form changes its own enabled → only nested form styling updates
2. ✓ Parent form changes its own enabled → parent form styling updates correctly
3. ✓ Form without enabled receives signal → correctly ignores it

All tests pass.

## Impact
- **Fixed**: Toggling nested dataclass enabled fields now only affects that specific nested form
- **Fixed**: Parent and sibling forms no longer experience incorrect styling pollution
- **Maintained**: Legitimate enabled field inheritance and propagation still works
- **Maintained**: Parent enabled changes correctly cascade to children (via `_refresh_enabled_styling`)

## Verification
To verify the fix works in the actual application:
1. Open a form with nested dataclasses that both have `enabled` fields
2. Toggle the nested dataclass's `enabled` checkbox
3. Observe that only the nested form's styling changes (dims/undims)
4. Verify parent and sibling forms remain unchanged
