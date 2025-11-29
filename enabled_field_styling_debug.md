# Enabled Field Styling System - Implementation & Current Bug

## Overview

The enabled field styling system provides visual feedback when a form's `enabled` parameter is set to `False`. When `enabled=False`, the form's widgets are dimmed (opacity 0.4) but remain editable, providing a clear visual indication that the configuration is disabled without blocking user interaction.

## Architecture

### Signal Flow

```
User changes widget
    ↓
_emit_parameter_change(param_name, value)
    ↓
parameter_changed.emit(param_name, value)
    ↓
┌─────────────────────────────────────────────────────────┐
│ Connected handlers:                                      │
│ 1. _on_enabled_field_changed_universal (if enabled)     │
│ 2. _refresh_with_live_context (placeholder updates)     │
│ 3. _emit_cross_window_change (cross-window propagation) │
│ 4. Parent's _on_nested_parameter_changed (if nested)    │
└─────────────────────────────────────────────────────────┘
```

### Nested Form Signal Propagation

When a nested form's parameter changes:

```
Nested Form: parameter_changed.emit('enabled', value)
    ↓
    ├─→ Nested Form: _on_enabled_field_changed_universal
    │       └─→ Applies styling to nested form ✅
    │
    └─→ Parent Form: _on_nested_parameter_changed
            ↓
            Refreshes placeholders
            ↓
            parameter_changed.emit('enabled', value)  ← RE-EMITS
                ↓
                Parent Form: _on_enabled_field_changed_universal
                    └─→ Applies styling to parent form ❌ BUG!
```

## Implementation History

### Attempt 1: Direct Widget Filtering (FAILED)

**Approach**: Filter widgets to only include direct children, excluding nested ParameterFormManager widgets.

**Code** (lines 1794-1809):
```python
def get_direct_widgets(parent_widget):
    """Get widgets that belong to this form, excluding nested ParameterFormManager widgets."""
    direct_widgets = []
    for widget in parent_widget.findChildren((QLineEdit, QComboBox, QPushButton, QCheckBox, QLabel)):
        widget_parent = widget.parent()
        while widget_parent is not None:
            if isinstance(widget_parent, ParameterFormManager) and widget_parent != self:
                break  # Widget belongs to nested form, skip it
            if widget_parent == self:
                direct_widgets.append(widget)
                break
            widget_parent = widget_parent.parent()
    return direct_widgets
```

**Why it failed**: This correctly filtered widgets, but didn't prevent the parent form's handler from being triggered when nested forms emitted `parameter_changed('enabled', value)`.

### Attempt 2: Separate Direct Signal (FAILED - TOO STRICT)

**Approach**: Create a separate `_direct_parameter_changed` signal that only fires for direct parameter changes, not propagated ones.

**Code**:
```python
# Added signal
_direct_parameter_changed = pyqtSignal(str, object)

# Connected enabled handler to direct signal
self._direct_parameter_changed.connect(self._on_enabled_field_changed_universal)

# Emitted both signals on direct changes
self._direct_parameter_changed.emit(param_name, converted_value)
self.parameter_changed.emit(param_name, converted_value)
```

**Why it failed**: PyQt signals are class-level, not instance-level. When ANY form emitted `_direct_parameter_changed`, ALL forms received it, causing the same crosstalk issue. Then when we tried to make it instance-specific, it became too strict - only the top-level form could use enabled field styling.

### Attempt 3: Check Widget Existence (FAILED)

**Approach**: Only apply styling if `'enabled'` is a widget in THIS form.

**Code** (lines 1761-1763):
```python
if 'enabled' not in self.widgets:
    return
```

**Why it failed**: Both the step AND the nested configs have `enabled` fields, so this check doesn't distinguish between the parent's own enabled field and a propagated enabled change from a nested form.

### Attempt 4: Propagation Flag (CURRENT - PARTIALLY BROKEN)

**Approach**: Set a flag when propagating nested parameter changes, and skip the enabled handler during propagation.

**Code**:

In `_on_nested_parameter_changed` (lines 1841-1845):
```python
# CRITICAL FIX: Set flag to indicate this is a propagated signal from nested form
self._propagating_nested_change = True
self.parameter_changed.emit(param_name, value)
self._propagating_nested_change = False
```

In `_on_enabled_field_changed_universal` (lines 1760-1763):
```python
# CRITICAL FIX: Only respond to THIS form's enabled field, not propagated changes from nested forms
# If this is a propagated signal from a nested form, ignore it
if getattr(self, '_propagating_nested_change', False):
    return
```

**Current status**: 
- ✅ Step's enabled field works correctly
- ❌ Nested config's enabled fields don't apply styling

## Current Bug Analysis

### What Works

1. **Step-level enabled field**: When you toggle the step's `enabled` checkbox, the step form's styling changes correctly.

2. **Title checkbox (None/Instance toggle)**: When you click the title checkbox to toggle a nested config between None and an instance, only that nested config's styling changes.

### What's Broken

**Nested config enabled fields**: When you toggle a nested config's `enabled` checkbox, the styling doesn't change.

### Expected Signal Flow for Nested Config Enabled Change

```
User clicks nested config's enabled checkbox
    ↓
Nested Form: _emit_parameter_change('enabled', value)
    ↓
Nested Form: parameter_changed.emit('enabled', value)
    ↓
    ├─→ Nested Form: _on_enabled_field_changed_universal
    │       ├─→ Check: param_name == 'enabled' ✅
    │       ├─→ Check: _propagating_nested_change? → False ✅
    │       └─→ Apply styling to nested form ✅ SHOULD WORK
    │
    └─→ Parent Form: _on_nested_parameter_changed
            ├─→ Set _propagating_nested_change = True
            ├─→ Emit parameter_changed('enabled', value)
            │       └─→ Parent Form: _on_enabled_field_changed_universal
            │               ├─→ Check: param_name == 'enabled' ✅
            │               ├─→ Check: _propagating_nested_change? → True ✅
            │               └─→ SKIP (no styling applied) ✅
            └─→ Set _propagating_nested_change = False
```

### Why It's Not Working

**Hypothesis 1**: The nested form's `_on_enabled_field_changed_universal` is somehow checking the parent's `_propagating_nested_change` flag instead of its own.

**Hypothesis 2**: The signal connection isn't set up correctly for nested forms.

**Hypothesis 3**: The `getattr(self, '_propagating_nested_change', False)` is returning True for the nested form when it shouldn't.

## Key Code Locations

### Signal Connection Setup
- **Line 312**: `self.parameter_changed.connect(self._on_enabled_field_changed_universal)`
- **Line 1066**: `nested_manager.parameter_changed.connect(self._on_nested_parameter_changed)`

### Signal Emission
- **Line 1128**: `self.parameter_changed.emit(param_name, converted_value)` in `_emit_parameter_change()`
- **Line 1259**: `self.parameter_changed.emit(param_name, converted_value)` in `update_parameter()`
- **Line 1843**: `self.parameter_changed.emit(param_name, value)` in `_on_nested_parameter_changed()`

### Enabled Field Handler
- **Lines 1746-1810**: `_on_enabled_field_changed_universal()` method

### Nested Parameter Handler
- **Lines 1813-1845**: `_on_nested_parameter_changed()` method

## Questions to Investigate

1. Is the nested form's `_on_enabled_field_changed_universal` being called at all?
2. If yes, is it returning early due to the `_propagating_nested_change` check?
3. If yes, why does the nested form have `_propagating_nested_change = True`?
4. Is there signal crosstalk between parent and nested forms?

## Potential Solutions

### Option 1: Instance-Specific Flag Check
Instead of `getattr(self, '_propagating_nested_change', False)`, explicitly check if the flag is set on THIS instance:
```python
if hasattr(self, '_propagating_nested_change') and self._propagating_nested_change:
    return
```

### Option 2: Don't Propagate 'enabled' Changes
Don't re-emit `parameter_changed` for `enabled` field changes in `_on_nested_parameter_changed`:
```python
# Don't propagate enabled field changes - they're form-specific
if param_name == 'enabled':
    return
```

### Option 3: Use Sender Information
Check which form emitted the signal using PyQt's sender mechanism:
```python
sender = self.sender()
if sender != self:
    return  # Signal came from nested form, ignore it
```

### Option 4: Separate Enabled Styling from Parameter Changes
Don't use `parameter_changed` signal for enabled styling at all. Instead, directly call the styling method when the enabled widget changes.

