# plan_02_form_manager_integration.md
## Component: ParameterFormManager Integration with Registry

### Objective

Migrate ParameterFormManager to use ContextStackRegistry as the single source of truth for resolved values. Forms will:
- **Write** to registry when user edits a field
- **Read** from registry for placeholder resolution
- **No longer** build their own context stacks

### Rollout and Testing

- Applied immediately after plan_01 and before plans 03/04, with no interim compatibility shims; any downstream listeners are expected to be updated in later plans. End-to-end testing happens after plan_04.

### Plan

1. **On form initialization**
   - Call `registry.register_scope(scope_id, context_obj, dataclass_type)`
   - Store registry reference for later use

2. **On user edit (parameter_changed signal) - UNIFIED MUTATION PATH**
   - Call `registry.set(scope_id, field_path, value)` for ALL objects (steps, PipelineConfig, everything)
   - **Remove `setattr(self.step, field_name, value)` from step_parameter_editor.py** (no more in-place mutation)
   - **Remove all `setattr()` patterns that mutate context_obj** (objects are immutable from registry's perspective)
   - Registry stores concrete values, does NOT mutate context_obj
   - Registry handles cache invalidation and signal emission
   - Remove direct `context_value_changed` emission (registry does it; downstream listeners are re-wired in plans 03/04)

3. **On placeholder resolution**
   - Replace `refresh_single_placeholder()` implementation
   - Call `registry.resolve(scope_id, field_path)` instead of building stack
   - Apply resolved value as placeholder text

4. **On form close**
   - Call `registry.unregister_scope(scope_id)`

5. **Code mode integration**
   - When code mode creates new objects, call `registry.register_scope(scope_id, new_obj, ...)` (re-registration)
   - Registry detects re-registration (scope_id exists), replaces context_obj, clears concrete values
   - Registry emits `value_changed` for all fields that changed between old and new object

6. **Materialization for compilation/serialization**
   - When compiling pipeline: `materialized_steps = [registry.get_materialized_object(scope_id) for scope_id in step_scopes]`
   - When generating code: Use `registry.get_materialized_object()` to get concrete instances
   - Objects in `pipeline_editor.pipeline_steps` remain as-is (original from code mode or creation)

7. **Remove deprecated code**
   - Remove `build_context_stack()` calls from ParameterOpsService
   - Remove internal stack building in `refresh_all_placeholders()`
   - Simplify `_schedule_cross_window_refresh()` to just trigger registry update
   - Keep `parameters` dict in ParameterFormManager for LiveContextService compatibility

### Findings

**Current ParameterFormManager Flow**:
- `__init__`: Registers with LiveContextService, connects signals
- `_emit_parameter_change()`: Emits `context_value_changed` signal
- `refresh_single_placeholder()`: Builds context stack, resolves placeholder
- `refresh_all_placeholders()`: Iterates widgets, builds stack, resolves each

**Assumptions/Notes**:
- Registry is the sole ingestion path for live edits: ParameterFormManager calls `registry.set()`
- Forms keep `parameters` dict so LiveContextService can read from it (no circular dependency)
- Registry does NOT read from LiveContextService (avoids loops)
- Objects are immutable from registry's perspective (no setattr on context_obj)

**Files to Modify**:
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`
- `openhcs/pyqt_gui/widgets/shared/services/parameter_ops_service.py`
- `openhcs/pyqt_gui/widgets/shared/services/field_change_dispatcher.py`
- `openhcs/pyqt_gui/widgets/step_parameter_editor.py` (remove setattr mutations)
- `openhcs/pyqt_gui/widgets/plate_manager.py` (code mode re-registration)
- `openhcs/pyqt_gui/widgets/pipeline_editor.py` (code mode re-registration, materialization for compilation)

### Implementation Draft

*To be written after plan_01 is implemented and smell loop approved*
