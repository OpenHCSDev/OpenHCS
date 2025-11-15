# Parameter Form Manager Live Context System

OpenHCS allows multiple configuration windows (global config, pipeline config, individual steps) to stay open simultaneously. Each window edits a different layer of the configuration hierarchy, yet every widget must surface the latest effective value after inheritance is applied. The `ParameterFormManager` in `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` implements this live, scope-aware synchronization without forcing users to save between windows.

## Registration and Signal Topology

Only root form managers (windows, not nested group boxes) participate in cross-window sync. During initialization the manager:

1. Appends itself to the class-level `_active_form_managers` registry.
2. Wires its `parameter_changed` signal to `_emit_cross_window_change`.
3. Connects its `context_value_changed` / `context_refreshed` signals to every existing manager and vice versa.

```python
# parameter_form_manager.py
self.parameter_changed.connect(self._emit_cross_window_change)
self.context_value_changed.connect(existing_manager._on_cross_window_context_changed)
existing_manager.context_value_changed.connect(self._on_cross_window_context_changed)
```

Each manager carries a `scope_id` (plate path/orchestrator id). When collecting peers it discards managers whose `scope_id` does not match, except for the global scope (`None`) so that the Global Pipeline editor continues to feed every orchestrator. Nested managers inherit their parent scope automatically.

## Live Context Snapshot Collection

The live context that drives placeholder resolution is built on demand via `_collect_live_context_from_other_windows()`. The algorithm:

1. Iterates over `_active_form_managers`, skipping the current manager and any manager whose type exactly matches the current object (two `PipelineConfig` editors never read from each other).
2. Rejects managers from other scopes unless the manager is global (scope `None`).
3. Pulls only concrete values by calling `get_user_modified_values()`, which filters out `None` fields and flattens nested dataclasses into `(type, dict)` tuples so inheritance is preserved.
4. Records the values under both the concrete type and its lazy/base aliases (via `get_base_type_for_lazy()` and `LazyDefaultPlaceholderService._get_lazy_type_for_base()`), enabling matches between `PipelineConfig` and `LazyPipelineConfig`.

The result is a mapping from type → “user-modified overlay” that contains just enough information to override parent contexts without overwriting unresolved fields.

## Context Stack Layering

`_build_context_stack()` combines thread-local contexts, live overlays, and the current form’s values using nested `config_context()` calls. Order matters:

1. **Global defaults** – If editing `GlobalPipelineConfig`, start with a fresh class instance to mask thread-local state. Otherwise merge live global overrides (if any) into the thread-local global config and push that first.
2. **Parent contexts** – The `context_obj` for a Step editor is its `PipelineConfig`. The manager merges live values for the parent type into the saved instance (using `dataclasses.replace`) so only concrete overrides flow downward.
3. **Parent overlay** – Nested forms (e.g., `napari_streaming_config` group boxes) apply their parent manager’s `get_user_modified_values()` so sibling widgets inherit each other’s edits during the same session.
4. **Current overlay** – Finally the current form’s `get_current_values()` overlay is applied, ensuring the widget’s immediate value always wins.

This layered stack feeds `ParameterFormService` and the placeholder resolvers so every widget shows the effective value that would exist if the pipeline were executed at that moment.

## Refresh Cycle and Debouncing

Parameter changes propagate through the following pipeline:

1. User edits a field → `parameter_changed` fires.
2. `_emit_cross_window_change()` emits `context_value_changed(field_path, value, editing_object, context_obj)` unless cross-window updates are temporarily blocked (e.g., bulk reset).
3. All other managers receive `_on_cross_window_context_changed()`; if the change affects them (`GlobalPipelineConfig` always matches, `PipelineConfig` only matches steps sharing the same `context_obj`), they call `_schedule_cross_window_refresh()`.
4. `_schedule_cross_window_refresh()` debounces with a 200 ms `QTimer` and eventually calls `_do_cross_window_refresh()`.
5. `_do_cross_window_refresh()` rebuilds the live context snapshot, calls `_refresh_all_placeholders()` on itself and every nested manager, and reapplies enabled-state styling. The optional `emit_signal` flag prevents ping-pong when the refresh was triggered by another window’s `context_refreshed`.

```python
def _do_cross_window_refresh(self, emit_signal=True):
    live_context = self._collect_live_context_from_other_windows()
    self._refresh_all_placeholders(live_context=live_context)
    self._apply_to_nested_managers(lambda _, m: m._refresh_all_placeholders(live_context=live_context))
    self._refresh_enabled_styling()
    if emit_signal:
        self.context_refreshed.emit(self.object_instance, self.context_obj)
```

`_refresh_all_placeholders()` rebuilds the context stack, asks `ParameterFormService` to resolve placeholders, and then triggers callbacks that drive enabled/disabled styling so UI dimming follows inherited booleans.

## External Listener Pattern

Some UI components need to react to configuration changes but are not themselves form managers (e.g., the pipeline editor's preview labels showing "MAT", "NAP", "FIJI" indicators). The external listener pattern allows these components to register for cross-window notifications without participating in the full form manager lifecycle.

### Registration

External listeners register via the class method `ParameterFormManager.register_external_listener()`:

```python
# pipeline_editor.py
ParameterFormManager.register_external_listener(
    self,
    self._on_cross_window_context_changed,
    self._on_cross_window_context_refreshed
)
```

The registration stores a tuple `(listener, value_changed_handler, refresh_handler)` in the class-level `_external_listeners` list. Unlike form managers, external listeners:

- Do not participate in the mesh signal topology (no bidirectional connections)
- Do not emit signals themselves
- Receive notifications via direct method calls, not Qt signals
- Are not scoped (they receive all notifications regardless of `scope_id`)

### Notification Points

External listeners are notified at three critical points:

1. **Global refresh** (`trigger_global_cross_window_refresh()`): Called when global config changes or when all managers are unregistered (e.g., after cancel). Notifies all external listeners with `refresh_handler(None, None)`.

2. **Reset operations** (`reset_all_parameters()`): After resetting parameters, both root and nested managers call `_notify_external_listeners_refreshed()` to notify external listeners with `refresh_handler(self.object_instance, self.context_obj)`.

3. **Individual parameter changes**: External listeners can optionally be notified on every parameter change, though this is rarely needed.

### Use Case: Pipeline Editor Preview Labels

The pipeline editor displays config indicators (MAT, NAP, FIJI, FILT) next to each step. These labels must update in real-time when:

- A step editor changes a config's `enabled` field
- The PipelineConfig editor changes a config's `enabled` field
- A user clicks Reset in any config editor
- A user cancels a config editor (labels must revert to stored values)

The pipeline editor registers as an external listener and implements `_on_cross_window_context_refreshed()` to rebuild preview labels by:

1. Collecting live context from all open windows via `_collect_live_context_from_other_windows()`
2. Building a context stack (GlobalPipelineConfig → PipelineConfig → Step)
3. Resolving each config's `enabled` field through lazy resolution
4. Updating the label text based on the resolved values

This ensures preview labels always reflect the current effective state, including unsaved changes in open windows.

## Cleanup and Failure Modes

When a window closes, `unregister_from_cross_window_updates()` disconnects all peer signal connections before removing the manager from `_active_form_managers`. Remaining windows immediately call `_refresh_with_live_context()` to fall back to saved values instead of stale live ones. Skipping this cleanup previously led to runaway placeholder refreshes because destroyed windows still responded to signals.

### Cancel and Reset Refresh Behavior

Two special cases require explicit external listener notification:

1. **Cancel**: When a user cancels a config editor (via Cancel button or Escape key), the window's `reject()` method:
   - Calls `super().reject()` to unregister all form managers
   - Calls `trigger_global_cross_window_refresh()` to notify remaining windows and external listeners
   - This ensures preview labels and placeholders revert to stored values, not the cancelled live values

2. **Reset**: When a user clicks Reset (either for the whole window or for a nested dataclass):
   - The manager calls `reset_all_parameters()` which resets all fields to their signature defaults
   - After resetting, the manager calls `_notify_external_listeners_refreshed()` to notify external listeners
   - This ensures preview labels update to reflect the reset values immediately

Without these explicit notifications, external listeners would continue showing stale values until the next parameter change.

Three additional safeguards keep state consistent:

- `_block_cross_window_updates` gates `_emit_cross_window_change()` during bulk operations such as “Reset All” so intermediate states are not broadcast.
- `_initial_load_complete` ensures nested managers do not push placeholder overlays until widget construction finishes; otherwise optional dataclasses could resolve against incomplete context.
- External listeners are notified directly (not via signals) to ensure they receive updates even when all managers are unregistered.

## Re-implementation Checklist

When refactoring, keep these invariants:

1. Cross-window registration must remain symmetric so every manager both emits and listens, and scoping must continue to respect `scope_id`.
2. Live context snapshots must only include concrete user-set values and must avoid pulling data from another instance of the same config type.
3. Context stacking order (global → parent → parent overlay → current overlay) cannot change without breaking inheritance semantics.
4. Debounced refresh plus `context_refreshed` propagation prevents ping-pong; any new implementation needs equivalent cycle control.
5. Windows must unregister before destruction so future refreshes do not access deleted widgets.
6. External listeners must be notified on cancel, reset, and global refresh operations to ensure non-form-manager UI components stay synchronized.
7. Cancel operations (`reject()`) must call `trigger_global_cross_window_refresh()` AFTER unregistration to ensure external listeners receive the refresh notification.
8. Reset operations (`reset_all_parameters()`) must call `_notify_external_listeners_refreshed()` for both root and nested managers to ensure external listeners update immediately.

These behaviors, not the current method layout, define the “contract” that downstream refactors must satisfy to preserve multi-window live sync.
