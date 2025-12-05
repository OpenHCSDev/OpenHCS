# plan_02_pfm_integration.md
## Component: ParameterFormManager Integration with ObjectState

### Objective
Modify ParameterFormManager (PFM) to delegate all MODEL concerns to ObjectState, making PFM a pure VIEW that:
- Reads state from ObjectState (`state.parameters`, `state.get_resolved_value()`)
- Writes state via ObjectState (`state.update_parameter()`)
- Renders widgets based on state
- Formats placeholder text for display (VIEW responsibility)

### Findings

#### Current PFM MODEL Attributes (to delegate to ObjectState)
| PFM Attribute | Type | ObjectState Equivalent |
|---------------|------|------------------------|
| `self.parameters` | `Dict[str, Any]` | `state.parameters` |
| `self.parameter_types` | `Dict[str, Type]` | `state.parameter_types` |
| `self.param_defaults` | `Dict[str, Any]` | `state.param_defaults` |
| `self._user_set_fields` | `Set[str]` | `state._user_set_fields` |
| `self.reset_fields` | `Set[str]` | `state.reset_fields` |
| `self.nested_managers` | `Dict[str, PFM]` | VIEW concern (PFM keeps) |
| `self.object_instance` | `Any` | `state.object_instance` |
| `self.context_obj` | `Any` | `state.context_obj` |
| `self.scope_id` | `str` | `state.scope_id` |

#### Current PFM Constructor Flow
```python
def __init__(self, object_instance, field_id, config):
    # 1. Extract parameters from object_instance
    extracted = ParameterExtractionService.build(object_instance, ...)
    # 2. Build form config
    form_config = ConfigBuilderService.build(...)
    # 3. Extract param_defaults for reset
    # 4. Initialize tracking: widgets, nested_managers, _user_set_fields
    # 5. Register with LiveContextService (root only)
    # 6. Setup UI (create widgets)
    # 7. Connect signals
    # 8. Initial refresh
```

#### ObjectState Lifecycle Question
**Who creates ObjectState?**

Current PFM creates its own state during `__init__`. But ObjectState should persist when editor closes.

Options:
1. **PFM creates ObjectState** (simplest migration) - ObjectState created in PFM.__init__, registered with ObjectStateRegistry
2. **Caller creates ObjectState** - ConfigWindow/StepEditor/etc. create and pass to PFM
3. **Hybrid** - If `state` passed, use it; else create new one

Recommendation: **Option 1 (PFM creates)** for initial migration, then evolve to Option 2.

### Plan

#### Phase 1: Add `state` attribute to PFM (backward compatible)
1. Add `self.state: ObjectState` to PFM `__init__`
2. Create ObjectState from `object_instance`, `field_id`, `scope_id`, `context_obj`
3. Register with `ObjectStateRegistry`
4. Keep existing MODEL attributes as pass-through properties initially

#### Phase 2: Create pass-through properties
Convert direct attribute access to delegation:
```python
@property
def parameters(self) -> Dict[str, Any]:
    return self.state.parameters

@property  
def _user_set_fields(self) -> Set[str]:
    return self.state._user_set_fields
```

#### Phase 3: Update FieldChangeDispatcher
Currently dispatcher directly mutates `source.parameters` and `source._user_set_fields`:
```python
# field_change_dispatcher.py line 73-79
source.parameters[event.field_name] = event.value
source._user_set_fields.add(event.field_name)
```

Change to:
```python
source.state.update_parameter(event.field_name, event.value, user_set=True)
```

#### Phase 4: Update placeholder resolution flow
Currently: `ParameterOpsService.refresh_single_placeholder()` → builds context → resolves
New flow: `state.get_resolved_value(field)` → returns cached value

PFM formats for display:
```python
def _get_placeholder_text(self, param_name: str) -> Optional[str]:
    """VIEW formats placeholder for display."""
    resolved = self.state.get_resolved_value(param_name)
    if resolved is None:
        return None
    from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
    return LazyDefaultPlaceholderService._format_placeholder_text(resolved, self.placeholder_prefix)
```

#### Phase 5: Update nested manager creation
Currently `_create_nested_form_inline()` creates new PFM with `parent_manager=self`.

New flow:
1. Create nested ObjectState with `parent_state=self.state`
2. Store in `self.state.nested_states[param_name]`
3. Create nested PFM with `state=nested_state`

#### Phase 6: Update LiveContextService → ObjectStateRegistry
Replace `LiveContextService._active_form_managers` with `ObjectStateRegistry`:
- `LiveContextService.collect()` → `ObjectStateRegistry.collect_live_values()`
- `LiveContextService.get_active_managers()` → `ObjectStateRegistry.get_all()`
- Token management already in ObjectStateRegistry

#### Phase 7: Unregister on destroy
PFM `destroyed` signal → `ObjectStateRegistry.unregister(self.state.scope_id)`

### Signal Handlers - Changes Required

| Current Method | What Changes |
|---------------|--------------|
| `FieldChangeDispatcher.dispatch()` | Call `state.update_parameter()` instead of direct mutation |
| `_schedule_cross_window_refresh()` | Use `ObjectStateRegistry.increment_token()` |
| `_on_live_context_changed()` | Check `state._block_cross_window_updates` |
| `reset_parameter()` | Call `state.reset_parameter()`, then update widget |
| `get_current_values()` | Return `state.get_current_values()` |
| `get_user_modified_values()` | Return `state.get_user_modified_values()` |

### Widget Operations - Read vs Resolved

| Operation | Data Source | Who Formats |
|-----------|-------------|-------------|
| Show concrete value | `state.parameters[field]` | Widget directly |
| Show placeholder | `state.get_resolved_value(field)` | PFM formats as `f"{prefix}: {value}"` |
| User edits widget | Read from widget | PFM → `state.update_parameter()` |
| Reset field | `state.reset_parameter()` | PFM updates widget |

### Backward Compatibility Concerns

1. **Callers accessing `manager.parameters` directly** - Works via property delegation
2. **Callers accessing `manager._user_set_fields`** - Works via property delegation
3. **`get_current_values()` / `get_user_modified_values()`** - Signature unchanged
4. **Nested manager access** - `nested_managers` stays on PFM (VIEW concern)

### Migration Strategy

**Incremental approach** (recommended):
1. Add `self.state` without changing behavior (Phase 1-2)
2. Update dispatcher to use state (Phase 3)
3. Update resolution flow (Phase 4)
4. Update nested creation (Phase 5)
5. Swap LiveContextService → ObjectStateRegistry (Phase 6)

Each phase can be tested independently. Tests should pass at each step.

### Callers to Update (Phase 7+)

| Caller | Current Usage | Change Needed |
|--------|---------------|---------------|
| ConfigWindow | Creates PFM with `object_instance` | No change initially |
| StepEditor | Creates PFM with step overlay | No change initially |
| FunctionPane | Creates PFM with callable | No change initially |
| ImageBrowser | Creates 2 PFMs for napari/fiji | Later: ImageBrowserConfig namespace |

### Risk Mitigations

1. **Property delegation** ensures existing code works during migration
2. **ObjectStateRegistry.collect_live_values()** already implemented and tested
3. **Token-based caching** already works in ObjectState
4. **Phase-by-phase** approach allows rollback

### Implementation Order

1. ✅ ObjectState class (done)
2. ✅ ObjectStateRegistry (done)
3. ✅ Resolution in ObjectState (done)
4. ⬜ Phase 1-2: Add state + properties to PFM
5. ⬜ Phase 3: Update FieldChangeDispatcher
6. ⬜ Phase 4: Update placeholder resolution
7. ⬜ Phase 5: Update nested manager creation
8. ⬜ Phase 6: Replace LiveContextService
9. ⬜ Phase 7+: Update callers (ImageBrowserConfig, etc.)

