# ObjectState Migration Plan

## Goal
Extract the "brain" of ParameterFormManager into `ObjectState` (config_framework/object_state.py) so that:

1. **List items own ObjectState** (~5ms init) instead of PFM (~50ms)
2. **PFM attaches to ObjectState on expand** - only creates widgets
3. **Cross-window coordination uses ObjectState** - works even when UI collapsed

## Current Architecture

```
ParameterFormManager (1204 lines)
├── STATE (moves to ObjectState)
│   ├── parameters: Dict[str, Any]
│   ├── _user_set_fields: Set[str]  
│   ├── reset_fields: Set[str]
│   ├── param_defaults: Dict[str, Any]
│   ├── parameter_types: Dict[str, Type]
│   ├── object_instance: Any
│   ├── context_obj: Any
│   ├── scope_id: str
│   └── nested_managers: Dict[str, PFM]  → nested_states: Dict[str, ObjectState]
│
├── VALUE METHODS (moves to ObjectState)
│   ├── get_current_values()
│   ├── get_user_modified_values()
│   ├── get_current_values_as_instance()
│   ├── get_user_modified_instance()
│   ├── reset_field()
│   └── reset_all()
│
├── UI METHODS (stays in PFM)
│   ├── setup_ui()
│   ├── build_form()
│   ├── update_widget_value()
│   ├── _create_nested_form_inline()
│   └── widgets: Dict[str, QWidget]
│
└── SIGNALS/EVENTS (stays in PFM but delegates to ObjectState)
    ├── _on_parameter_changed() → calls state.set_field()
    └── _on_live_context_changed() → calls state refresh
```

## Target Architecture

```
ObjectState (config_framework/object_state.py)
├── Core State
│   ├── object_instance, field_id, context_obj, scope_id
│   ├── parameters, parameter_types, param_defaults
│   ├── _user_set_fields, reset_fields
│   └── nested_states: Dict[str, ObjectState]
│
├── Value Methods  
│   ├── get_current_values() → returns self.parameters (no widget access)
│   ├── get_user_modified_values()
│   ├── get_current_values_as_instance()
│   └── get_user_modified_instance()
│
├── Field Operations
│   ├── set_field(name, value) → updates parameters, marks user_set
│   ├── reset_field(name) → computes reset value, clears user_set
│   └── reset_all()
│
├── Callbacks (set by UI layer)
│   ├── on_value_changed: Callable[[str, Any], None]
│   ├── on_placeholder_changed: Callable[[str, Any], None]  
│   └── on_reset: Callable[[str], None]
│
└── Factory
    └── from_object_instance(obj, field_id, config) → ObjectState


ParameterFormManager (refactored, ~400 lines)
├── Constructor
│   ├── __init__(state: ObjectState, config) → attach to existing state
│   └── create(obj, field_id, config) → create state + PFM (backward compat)
│
├── Widget Management
│   ├── widgets: Dict[str, QWidget]
│   ├── setup_ui(), build_form()
│   └── update_widget_value()
│
└── Event Handlers
    ├── _on_parameter_changed() → state.set_field()
    └── _on_widget_value_changed() → state.set_field()


LiveContextService (updated)
├── _active_states: WeakSet[ObjectState]  (was _active_form_managers)
├── register(state: ObjectState)
├── collect() → iterates ObjectState instances
└── Same interface, different type
```

## Migration Phases

### Phase 1: Complete ObjectState ✓
Already done. Created `openhcs/config_framework/object_state.py` with:
- All state attributes
- Value collection methods  
- Reset methods
- Callback interface

### Phase 2: Add ObjectState.from_object_instance() Factory
Add factory method that does parameter extraction:
- Uses `UnifiedParameterAnalyzer.analyze()` (framework-agnostic)
- Returns fully initialized ObjectState
- No PyQt6 dependencies

### Phase 3: Update LiveContextService  
Change from PFM to ObjectState:
- Type hints: `ParameterFormManager` → `ObjectState`
- `_active_form_managers` → `_active_states`
- `collect()` uses ObjectState interface (same methods, just different type)
- Add deprecation shim for `register(PFM)` during migration

### Phase 4: Refactor PFM to use ObjectState
Two-phase constructor pattern:
```python
class ParameterFormManager(QWidget):
    def __init__(self, state: ObjectState, config: FormManagerConfig):
        """Attach widgets to existing ObjectState."""
        self.state = state
        self._build_widgets()
        self._connect_callbacks()
    
    @classmethod  
    def create(cls, object_instance, field_id, config=None):
        """Create ObjectState + PFM (backward compatibility)."""
        state = ObjectState.from_object_instance(object_instance, field_id, ...)
        LiveContextService.register(state)  # Register state, not PFM
        return cls(state, config)
```

Delegation pattern:
- `pfm.parameters` → `pfm.state.parameters`
- `pfm.get_current_values()` → `pfm.state.get_current_values()`
- `pfm._user_set_fields` → `pfm.state._user_set_fields`
- etc.

### Phase 5: Update PFM Callers
Major callers to update:
- `PipelineListItem` - create ObjectState upfront
- `ConfigDialog` - create ObjectState upfront  
- `StepEditorDialog` - create ObjectState upfront
- `FunctionPatternEditor` - create ObjectState upfront

Pattern:
```python
class StepListItem:
    def __init__(self, step):
        # Lightweight - just state, no widgets
        self.state = ObjectState.from_object_instance(step, ...)
        LiveContextService.register(self.state)
        
    def on_expand(self):
        # Heavy - create widgets
        self.pfm = ParameterFormManager(self.state, config)
        
    def on_collapse(self):
        # Destroy widgets, keep state
        self.pfm.deleteLater()
        self.pfm = None
        # state survives! Still in LiveContextService
```

## File Changes Summary

### New/Modified Files
1. `openhcs/config_framework/object_state.py` - Add factory method ✓ partial
2. `openhcs/config_framework/__init__.py` - Export ObjectState ✓ done
3. `openhcs/pyqt_gui/widgets/shared/services/live_context_service.py` - Accept ObjectState
4. `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` - Delegate to ObjectState

### Callers to Update
- `openhcs/pyqt_gui/widgets/config_dialog.py`
- `openhcs/pyqt_gui/widgets/pipeline_editor/step_list_item.py`
- `openhcs/pyqt_gui/widgets/step_editor_dialog.py`
- `openhcs/pyqt_gui/widgets/function_pattern_editor.py`
- Any other file that creates ParameterFormManager

## Benefits
1. **10x faster list item init** - ObjectState ~5ms vs PFM ~50ms
2. **Memory efficient** - widgets only created when visible
3. **Cross-window works when collapsed** - ObjectState always registered
4. **Clean separation** - state/logic vs UI
5. **Reusable** - ObjectState works for Textual TUI too
6. **Testable** - ObjectState has no UI dependencies

