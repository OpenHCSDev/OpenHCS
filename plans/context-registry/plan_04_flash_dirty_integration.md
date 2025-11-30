# plan_04_flash_dirty_integration.md
## Component: Flash and Dirty Tracking via Registry

### Objective

Implement flash animations and dirty tracking using ContextStackRegistry signals. This becomes trivial because:
- **Flash**: Registry emits `(scope_id, field_path, old_value, new_value)` - flash if `old != new`
- **Dirty**: Compare `registry.get_resolved_state(scope_id)` to saved baseline

### Rollout and Testing

- Final step in the back-to-back rollout. End-to-end testing happens after this plan is completed; no interim verification is planned before this point.

### Plan

1. **Flash implementation**
   - Listen to `registry.value_changed` signal
   - If `old_value != new_value`, emit flash for affected scope_id
   - Use scope visibility to determine which list items flash
   - No field tracking needed - registry handles propagation

2. **Dirty tracking implementation**
   - **On register_scope()**: Capture initial baseline if none exists (newly opened scope)
   - **On save**: Update baseline to current `registry.get_resolved_state(scope_id)`
   - **On load**: Capture baseline from loaded state
   - **On check**: Compare current resolved state to baseline
   - Emit `item_dirty_changed(scope_id, is_dirty)` signal

3. **Simplify ResolvedItemStateService**
   - Remove field tracking (registry handles it)
   - Remove `_on_context_value_changed()` (use registry signal)
   - Keep scope registration for flash targeting
   - Add baseline storage for dirty tracking

4. **UI integration**
   - AbstractManagerWidget connects to service signals
   - `_on_item_resolved_changed()` triggers flash animation
   - `_on_item_dirty_changed()` updates dirty indicator

### Findings

**User's Exact Specification**:
1. Flash: "only flash if the resolved state changes from before the signal and after the signal"
2. Preview text: "just reads the current resolved state always, simple as"
3. Dirty: "checks if the current resolved state is different from the saved resolved state"

**Current ResolvedItemStateService**:
- Listens to `context_value_changed` from forms
- Uses scope visibility to filter
- Flashes on ANY change (wrong - should only flash if resolved value changes)

**Files to Modify**:
- `openhcs/pyqt_gui/widgets/shared/services/resolved_item_state_service.py`
- `openhcs/pyqt_gui/widgets/shared/abstract_manager_widget.py`

### Implementation Draft

*To be written after plan_03 is implemented and smell loop approved*
