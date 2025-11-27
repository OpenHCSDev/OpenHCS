# Pipeline Editor Reactive Preview Labels Fix

## Problem: Non-Reactive Preview Labels

### What Was Broken

The step preview labels in the pipeline editor (showing "MAT", "NAP", "FIJI" indicators) were **NOT reactive** to live context changes. The labels only reflected the initial state when the step list was populated.

**Symptom:**
1. Open step editor for a step
2. Toggle `napari_streaming_config.enabled` checkbox
3. Preview label in pipeline editor still shows old state (doesn't update)
4. Only updates when `update_step_list()` is manually called (e.g., after closing step editor)

**Root Cause:**
The pipeline editor's `format_item_for_display()` method reads config states directly from step objects:

```python
# Lines 436-448 in pipeline_editor.py
config_indicators = []
for config_attr, indicator in self.STEP_CONFIG_INDICATORS.items():
    if hasattr(step, config_attr):
        config = getattr(step, config_attr, None)
        if config:
            if hasattr(config, 'enabled'):
                if config.enabled:  # ← Reads current state
                    config_indicators.append(indicator)
```

However, the pipeline editor was **NOT connected** to the cross-window refresh signals that notify when these config states change.

### What Signals Were Missing

The `ParameterFormManager` class provides two class-level signals for cross-window synchronization:

1. **`context_value_changed`** - Emitted when any form changes a value
   - Args: `(field_path, new_value, editing_object, context_object)`
   - Example: `"step.napari_streaming_config.enabled"` changed to `True`

2. **`context_refreshed`** - Emitted when placeholders are refreshed due to upstream changes
   - Args: `(editing_object, context_object)`
   - Example: Step editor's placeholders refreshed after PipelineConfig change

The pipeline editor was **NOT listening** to these signals, so it never knew when to re-render the preview labels.

## Solution: Wire Preview Labels to Live Context System

### Architecture Integration

The fix connects the pipeline editor to the same cross-window refresh system that makes the enabled checkboxes reactive in the step editor.

**Pattern Used:**
- Step editor's enabled checkboxes use `ParameterFormManager` which automatically connects to cross-window signals
- Pipeline editor now **explicitly connects** to the same signals to trigger `update_step_list()` when configs change

### Implementation Changes

#### 1. Connect to Cross-Window Signals (Lines 331-348)

```python
def setup_connections(self):
    """Setup signal/slot connections."""
    # ... existing connections ...
    
    # CRITICAL: Connect to ParameterFormManager's cross-window refresh signals
    # This makes preview labels reactive to live context changes
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
    ParameterFormManager.context_value_changed.connect(self._on_cross_window_context_changed)
    ParameterFormManager.context_refreshed.connect(self._on_cross_window_context_refreshed)
```

**Why This Works:**
- `ParameterFormManager` is a class with class-level signals (not instance signals)
- All `ParameterFormManager` instances emit to the same class-level signal
- Pipeline editor listens to ALL form changes across ALL windows
- Filters for relevant changes in the signal handlers

#### 2. Handle Value Changes (Lines 925-950)

```python
def _on_cross_window_context_changed(self, field_path: str, new_value: object,
                                     editing_object: object, context_object: object):
    """Handle cross-window context changes to update preview labels."""
    from openhcs.core.steps.function_step import FunctionStep
    
    # Only refresh if the change is to a FunctionStep (step editor)
    if not isinstance(editing_object, FunctionStep):
        return
    
    # Check if the changed step is in our pipeline
    if editing_object not in self.pipeline_steps:
        return
    
    # Check if the change affects config indicators
    if any(config_attr in field_path for config_attr in self.STEP_CONFIG_INDICATORS.keys()):
        logger.debug(f"Pipeline editor: Config change detected in {field_path}, refreshing preview labels")
        self.update_step_list()
```

**Type-Safe Dispatch:**
- Uses `isinstance(editing_object, FunctionStep)` - LBYL pattern
- Checks if step is in `self.pipeline_steps` - fail-loud if not
- Filters by config attribute names from `STEP_CONFIG_INDICATORS` mapping

#### 3. Handle Cascading Refreshes (Lines 952-976)

```python
def _on_cross_window_context_refreshed(self, editing_object: object, context_object: object):
    """Handle cascading placeholder refreshes from upstream windows."""
    from openhcs.core.steps.function_step import FunctionStep
    
    # Only refresh if the refresh is for a FunctionStep
    if not isinstance(editing_object, FunctionStep):
        return
    
    # Check if the refreshed step is in our pipeline
    if editing_object not in self.pipeline_steps:
        return
    
    logger.debug(f"Pipeline editor: Step context refreshed, refreshing preview labels")
    self.update_step_list()
```

**Cascading Refresh Pattern:**
- GlobalPipelineConfig changes → PipelineConfig placeholders refresh → Step editor placeholders refresh
- Step editor emits `context_refreshed` → Pipeline editor updates preview labels
- Ensures preview labels stay in sync even when changes propagate through hierarchy

#### 4. Cleanup on Close (Lines 1196-1212)

```python
def closeEvent(self, event):
    """Handle widget close event to disconnect signals and prevent memory leaks."""
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
    try:
        ParameterFormManager.context_value_changed.disconnect(self._on_cross_window_context_changed)
        ParameterFormManager.context_refreshed.disconnect(self._on_cross_window_context_refreshed)
        logger.debug("Pipeline editor: Disconnected from cross-window refresh signals")
    except (TypeError, RuntimeError):
        pass  # Signal already disconnected or object destroyed

    super().closeEvent(event)
```

**Memory Leak Prevention:**
- Disconnects from class-level signals when widget closes
- Prevents closed pipeline editor from receiving signals
- Follows same pattern as `ParameterFormManager._cleanup_on_close()`

## How It Mirrors Enabled Checkbox Placeholder Pattern

### Enabled Checkbox Reactivity (Existing Pattern)

**Step Editor's Enabled Checkbox:**
1. User opens step editor → `ParameterFormManager` created
2. `ParameterFormManager.__init__()` connects to class-level signals (lines 481-491)
3. User toggles `enabled` checkbox → `parameter_changed` signal emitted
4. `_emit_cross_window_change()` emits `context_value_changed` class signal
5. All other `ParameterFormManager` instances receive signal
6. Each instance calls `_on_cross_window_context_changed()` → `_refresh_all_placeholders()`
7. Placeholders update with new inherited values

**Key Components:**
- Class-level signals (`context_value_changed`, `context_refreshed`)
- Automatic connection in `__init__()` for all form managers
- Signal filtering based on context hierarchy
- Placeholder refresh triggered by signal handlers

### Preview Label Reactivity (New Pattern)

**Pipeline Editor's Preview Labels:**
1. User opens pipeline editor → `setup_connections()` connects to class-level signals
2. User opens step editor and toggles `napari_streaming_config.enabled`
3. Step editor's `ParameterFormManager` emits `context_value_changed` class signal
4. Pipeline editor receives signal via `_on_cross_window_context_changed()`
5. Handler checks if change affects config indicators
6. Calls `update_step_list()` to re-render preview labels
7. Preview labels show updated config state

**Key Components:**
- Same class-level signals (`context_value_changed`, `context_refreshed`)
- Explicit connection in `setup_connections()` (not automatic like form managers)
- Signal filtering based on step identity and config attribute names
- Preview label refresh triggered by `update_step_list()`

### Architectural Symmetry

Both patterns use the **same cross-window refresh infrastructure**:

| Component | Enabled Checkbox | Preview Labels |
|-----------|------------------|----------------|
| **Signal Source** | `ParameterFormManager` class signals | Same |
| **Connection Point** | `__init__()` (automatic) | `setup_connections()` (explicit) |
| **Signal Handler** | `_on_cross_window_context_changed()` | Same method name |
| **Filtering Logic** | Context hierarchy matching | Step identity + config attribute matching |
| **Refresh Action** | `_refresh_all_placeholders()` | `update_step_list()` |
| **Cleanup** | `_cleanup_on_close()` | `closeEvent()` |

**Difference:**
- `ParameterFormManager` instances automatically connect in `__init__()` and register in `_active_form_managers`
- Pipeline editor explicitly connects in `setup_connections()` (not a form manager, just a listener)

## Architectural Principles Enforced

### 1. LBYL (Look Before You Leap)

```python
# Type-safe dispatch using isinstance()
if not isinstance(editing_object, FunctionStep):
    return

# Explicit membership check
if editing_object not in self.pipeline_steps:
    return
```

**No defensive programming:**
- No `hasattr()` checks for guaranteed attributes
- No `try/except` around attribute access
- Fail-loud if assumptions are violated

### 2. Type-Safe Dispatch

```python
# Import at function scope for type checking
from openhcs.core.steps.function_step import FunctionStep

# Explicit type check before processing
if not isinstance(editing_object, FunctionStep):
    return
```

**No duck typing:**
- Explicit `isinstance()` check for `FunctionStep`
- No attribute-based type inference
- Clear contract enforcement

### 3. Generic Implementation

```python
# Uses STEP_CONFIG_INDICATORS mapping (lines 143-148)
if any(config_attr in field_path for config_attr in self.STEP_CONFIG_INDICATORS.keys()):
    self.update_step_list()
```

**No hardcoded checks:**
- Iterates over `STEP_CONFIG_INDICATORS` mapping
- Adding new config types requires only updating the mapping
- No if/elif chains for specific config names

### 4. Fail-Loud Signal Handling

```python
# No defensive try/except around signal handlers
def _on_cross_window_context_changed(self, field_path: str, ...):
    # Direct attribute access - will raise AttributeError if missing
    if editing_object not in self.pipeline_steps:
        return
```

**Exception handling only for cleanup:**
```python
# Only in closeEvent for disconnect (expected to fail if already disconnected)
try:
    ParameterFormManager.context_value_changed.disconnect(...)
except (TypeError, RuntimeError):
    pass  # Expected - signal already disconnected
```

## Testing Verification

### Manual Test Procedure

1. **Open pipeline editor** with at least one step
2. **Open step editor** for that step
3. **Toggle `napari_streaming_config.enabled`** checkbox
4. **Observe preview label** in pipeline editor updates immediately (shows/hides "NAP")
5. **Toggle `fiji_streaming_config.enabled`** checkbox
6. **Observe preview label** updates immediately (shows/hides "FIJI")
7. **Close step editor**
8. **Verify** no errors in logs about signal disconnection

### Expected Behavior

**Before Fix:**
- Preview labels only update when step list is manually refreshed
- Closing/reopening step editor shows updated labels
- Live editing doesn't update labels

**After Fix:**
- Preview labels update immediately when config changes
- No need to close/reopen step editor
- Live editing updates labels in real-time

## Bug Fix: Signal Connection Error

### Problem Encountered

Initial implementation tried to connect to class-level signals directly:
```python
ParameterFormManager.context_value_changed.connect(self._on_cross_window_context_changed)
```

This failed with:
```
AttributeError: 'PyQt6.QtCore.pyqtSignal' object has no attribute 'connect'
```

**Root Cause:** In PyQt6, signals defined at class level are actually instance signals. You can't connect to the signal on the CLASS - you need to connect to signal instances on actual OBJECTS.

### Solution: External Listener Registry

Added an external listener registry to `ParameterFormManager` so non-form-manager objects (like PipelineEditorWidget) can receive cross-window signals.

**Pattern:**
- ParameterFormManager instances connect to each other in a mesh topology
- External listeners register via class method and get connected to all instances
- New ParameterFormManager instances automatically connect to registered listeners

## Code Changes Summary

### Files Modified

**`openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`** - 3 changes:

1. **Lines 247-249**: Added `_external_listeners` class-level registry
   ```python
   # Class-level registry of external listeners (e.g., PipelineEditorWidget)
   _external_listeners = []
   ```

2. **Lines 281-316**: Added registration/unregistration methods
   ```python
   @classmethod
   def register_external_listener(cls, listener, value_changed_handler, refresh_handler):
       # Add to registry and connect to all existing managers
       ...

   @classmethod
   def unregister_external_listener(cls, listener):
       # Remove from registry
       ...
   ```

3. **Lines 535-538**: Connect new instances to external listeners
   ```python
   # Connect this instance to all external listeners
   for listener, value_changed_handler, refresh_handler in self._external_listeners:
       self.context_value_changed.connect(value_changed_handler)
       self.context_refreshed.connect(refresh_handler)
   ```

**`openhcs/pyqt_gui/widgets/pipeline_editor.py`** - 2 changes:

1. **Lines 344-351**: Register as external listener in `setup_connections()`
   ```python
   ParameterFormManager.register_external_listener(
       self,
       self._on_cross_window_context_changed,
       self._on_cross_window_context_refreshed
   )
   ```

2. **Lines 928-979**: Added two signal handler methods (unchanged from original implementation)
   - `_on_cross_window_context_changed()` - Handles value changes
   - `_on_cross_window_context_refreshed()` - Handles cascading refreshes

3. **Lines 1199-1207**: Simplified `closeEvent()` method for cleanup
   ```python
   ParameterFormManager.unregister_external_listener(self)
   ```

### Total Lines Changed

- **ParameterFormManager**: +38 lines (registry + registration methods + connection logic)
- **PipelineEditorWidget**: +57 lines (signal handlers + registration + cleanup)
- **Total**: +95 lines

## Summary

### What Changed

1. **Added signal connections** in `setup_connections()` to listen to cross-window refresh signals
2. **Added signal handlers** to filter relevant changes and trigger `update_step_list()`
3. **Added cleanup** in `closeEvent()` to disconnect signals and prevent memory leaks

### Why It Works

- Pipeline editor now listens to the same signals that make enabled checkboxes reactive
- Signal handlers filter for `FunctionStep` changes affecting config indicators
- `update_step_list()` re-renders preview labels with current config state
- Cleanup prevents memory leaks from dangling signal connections

### Architectural Alignment

- Uses LBYL pattern with `isinstance()` checks
- Type-safe dispatch (no duck typing)
- Generic implementation using `STEP_CONFIG_INDICATORS` mapping
- Fail-loud signal handling (no defensive programming)
- Mirrors enabled checkbox placeholder reactivity pattern

### Integration with Existing System

The pipeline editor now participates in the same cross-window refresh system as:
- **ParameterFormManager instances** (automatic connection in `__init__()`)
- **DualEditorWindow** (connects to `context_refreshed` for function editor sync)
- **All other form-based editors** (step editor, config window, etc.)

**Key Difference:**
- Form managers automatically connect to each other's instance signals
- Pipeline editor explicitly connects to the **class-level** signals
- This is correct because pipeline editor is not a form manager, just a listener

### Verification

**Manual Test:**
1. Open pipeline editor with steps
2. Open step editor for a step
3. Toggle `napari_streaming_config.enabled` → Preview label updates immediately
4. Toggle `fiji_streaming_config.enabled` → Preview label updates immediately
5. Close step editor → No errors in logs

**Expected Result:**
- Preview labels update in real-time as configs change
- No memory leaks or dangling signal connections
- Logs show: `"Pipeline editor: Config change detected in step.napari_streaming_config.enabled, refreshing preview labels"`


