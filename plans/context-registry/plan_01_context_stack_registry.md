# plan_01_context_stack_registry.md
## Component: Central Context Stack Registry

### Objective

Create a **ContextStackRegistry** service that serves as the single source of truth for all resolved configuration values across the application. This eliminates the current architecture where:
- ParameterFormManager builds its own context stacks
- Preview labels resolve values through a separate path
- Flash/dirty tracking would need yet another resolution path

**Scope**: Works for BOTH plate/orchestrator list items (PlateManager) AND step list items (PipelineEditor).

### Rollout and Testing

- Plans 01-04 will be applied back-to-back with end-to-end testing after the full integration. No interim compatibility shims or partial regression fixes are planned between steps.

### Problem Statement

**Current Architecture (Broken)**:
1. Forms build context stacks internally via `build_context_stack()` in `refresh_single_placeholder()`
2. Preview labels resolve via `_resolve_config_attr()` + `LiveContextResolver`
3. No single source of truth for "what is the resolved value of field X for scope Y"
4. Flash/dirty tracking requires re-resolving values (expensive, complex)

**User's Vision**:
> "why don't we just have the context stacks built for all objects at all time and have the parameter form manager access them rather than build its own and maintain it internally? this way there's a single source of truth for context stacks and ui elements can read from it"

### Plan

1. **Create ContextStackRegistry singleton service**
   - Location: `openhcs/config_framework/context_stack_registry.py`
   - Singleton pattern matching existing services (LiveContextService, ResolvedItemStateService)

2. **Define core API**
   ```python
   class ContextStackRegistry(QObject):
       # Signal: (scope_id, field_path, old_value, new_value)
       value_changed = pyqtSignal(str, str, object, object)

       def register_scope(self, scope_id: str, context_obj: Any, dataclass_type: type) -> None:
           """Register a scope for resolution. Called when form opens or item created.
           If scope_id already exists, REPLACES context_obj and clears concrete values (code mode)."""

       def unregister_scope(self, scope_id: str) -> None:
           """Unregister scope. Called when form closes or item deleted."""

       def set(self, scope_id: str, field_path: str, value: Any) -> None:
           """Set a concrete value override. Does NOT mutate context_obj (immutable).
           Emits value_changed if resolved value changes."""

       def resolve(self, scope_id: str, field_path: str) -> Any:
           """Resolve field value through context hierarchy. Cached."""

       def get_resolved_state(self, scope_id: str) -> Dict[str, Any]:
           """Get all resolved values for a scope. For dirty comparison."""

       def get_materialized_object(self, scope_id: str) -> Any:
           """Get context_obj with all resolved values applied. For compilation/serialization.
           Returns a NEW instance with all fields materialized from resolved state."""
   ```

3. **Internal implementation**
   - Reuse existing `build_context_stack()` from `context_manager.py`
   - Reuse existing `config_context()` for resolution
   - Lazy resolution with caching (resolve on first access)
   - Cache invalidation is field-aware: when `set()` fires or LiveContextService token changes, invalidate only the affected `field_path` for the scope and its descendants
   - **Immutability**: `set()` stores concrete values but does NOT mutate context_obj
   - **Materialization**: `get_materialized_object()` creates new instance with resolved values applied

4. **Scope hierarchy handling**
   - Use existing `get_root_from_scope_key()` for hierarchy
   - When value changes at scope X, invalidate cache for X and all children (same plate root)
   - No explicit parent/child map needed - iterate registered scopes and match roots
   - Scope ID format: `/path/to/plate` (plate), `/path/to/plate::step_token@index` (step)

5. **Integration with LiveContextService**
   - Registry does NOT use LiveContextService.collect() (avoids circular dependency)
   - Registry builds stacks from: registered context_obj + concrete values from registry.set()
   - Forms still register with LiveContextService for cross-window coordination
   - Resolution precedence: concrete values (registry.set) > context_obj values > inherited defaults

### Findings

**Existing Infrastructure to Reuse**:
- `build_context_stack()` in `context_manager.py` - builds complete context stack
- `config_context()` - context manager for resolution
- `get_root_from_scope_key()` - extracts plate root from scope_id
- `LiveContextService` - collects live values from open forms
- `LiveContextResolver` - resolves through context hierarchy with caching

**Key Patterns from Codebase**:
- Singleton services: `ResolvedItemStateService.instance()`, `LiveContextService` (class methods)
- Signal-based reactivity: `context_value_changed`, `item_resolved_changed`
- Scope visibility: `_is_scope_visible()` in ResolvedItemStateService

**State Mutation Paths**:

There are exactly 2 ways configuration state changes:

1. **ParameterFormManager edits** (field-level changes):
   - User edits field in form
   - Form calls `registry.set(scope_id, field_path, value)`
   - Registry stores concrete value (does NOT mutate context_obj - immutable)
   - Registry emits `value_changed` if resolved value changed
   - **For Steps**: Currently uses `setattr(step, field, value)` - will be REMOVED in plan_02
   - **For PipelineConfig**: Creates new instance on save via callback

2. **Code mode edits** (instance replacement):
   - User edits code, saves
   - Code is `exec()`'d, creates **NEW instances** (PipelineConfig or step list)
   - **For PipelineConfig**: Calls `orchestrator.apply_pipeline_config(new_config)` - REPLACES instance
   - **For Steps**: Replaces entire list `pipeline_editor.plate_pipelines[plate_path] = new_steps`
   - Registry handles via re-registration: `register_scope(scope_id, new_obj, ...)` (replaces if exists)

**Unified Mutation Path**:
- Live edits → `registry.set(scope_id, field_path, value)`
- Replacements → `registry.register_scope(scope_id, new_obj, ...)` (re-registration replaces)

**No other mutation paths exist**. If new paths are added later (server pushes, reloads), they must explicitly call `register_scope()` with new objects.

**Current Resolution Flow** (to be replaced):
1. `refresh_single_placeholder()` calls `build_context_stack()`
2. Stack includes: global layer, intermediate layers, context_obj, root form, overlay
3. Resolution happens inside `with stack:` context
4. Placeholder text computed via `service.get_placeholder_text()`

**Materialization Example**:
```python
# Initial step from code mode:
step = FunctionStep(
    func=my_function,
    step_materialization_config=LazyStepMaterializationConfig(
        sub_dir="checkpoints"  # Override
        # output_dir_suffix=None - will inherit from PipelineConfig.path_planning_config
    )
)

# Registry internal state after registration:
# _context_objs[scope_id] = step (the original object)
# _concrete_values[scope_id] = {}  # Empty initially

# User edits output_dir_suffix to "_custom" in form:
registry.set(scope_id, "step_materialization_config.output_dir_suffix", "_custom")

# Registry internal state after edit:
# _context_objs[scope_id] = step (UNCHANGED - immutable)
# _concrete_values[scope_id] = {"step_materialization_config.output_dir_suffix": "_custom"}

# When compiling pipeline:
materialized_step = registry.get_materialized_object(scope_id)
# Returns NEW FunctionStep with:
#   step_materialization_config.sub_dir = "checkpoints" (from original)
#   step_materialization_config.output_dir_suffix = "_custom" (from concrete values)
# All other fields resolved through context hierarchy

orchestrator.compile([materialized_step])
```

**Why Immutability + Materialization**:
- ✅ Single Responsibility: Registry resolves, doesn't mutate
- ✅ No side effects: `set()` is pure
- ✅ Explicit boundary: Materialization makes snapshot clear
- ✅ Testable: Easy to test without object mutation concerns

### Implementation Draft

*To be written after smell loop approval*
