# plan_01_resolved_value_registry.md
## Component: ResolvedValueRegistry - Centralized Resolved Value Service

### Objective

Create a centralized registry that:
1. Proactively computes resolved values for ALL registered objects (not just open forms)
2. Listens to LiveContext changes and recomputes affected scopes
3. Emits signals when resolved values actually change (enables flash animations)
4. Supports snapshotting for unsaved changes detection
5. Provides single source of truth for list items, form managers, and any UI component

### Why Previous Plan Failed

`plan_02_unsaved_reactive.md` attempted to piggyback on form-centric infrastructure:
- `_on_placeholder_changed_callbacks` only fires for OPEN forms
- List items don't have ParameterFormManagers, so they can't use this path
- No standalone resolver that can build context without an open form

This plan inverts the dependency: Registry owns computation, PFM becomes a consumer.

### ⚠️ ZERO REIMPLEMENTATION POLICY

**ALL resolution logic already exists.** The Registry is a THIN COORDINATION LAYER that:
1. Caches results from existing infrastructure
2. Tracks what needs recomputing when LiveContext changes
3. Emits signals for UI updates

**Existing infrastructure to CALL (not reimplement):**

| Component | Location | What it does |
|-----------|----------|--------------|
| `build_context_stack()` | `config_framework.context_manager` | Builds complete context stack for resolution |
| `LiveContextService.collect()` | `services.live_context_service` | Collects live values from all managers with scope filtering |
| `resolve_field_inheritance()` | `config_framework.dual_axis_resolver` | MRO-based resolution within a scope |
| `LazyDefaultPlaceholderService` | `config_framework.placeholder` | Formats resolved value as placeholder text |
| `get_ancestors_from_hierarchy()` | `config_framework.context_manager` | Walks type hierarchy |
| `_is_scope_visible()` | `services.live_context_service` | Scope visibility filtering |
| `get_root_from_scope_key()` | `config_framework.context_manager` | Parses scope_id hierarchy |

### Plan

#### 1. Create ResolvedValueRegistry Service

**File:** `openhcs/pyqt_gui/widgets/shared/services/resolved_value_registry.py`

```python
class ResolvedValueRegistry(QObject):
    """
    Thin coordination layer over existing resolution infrastructure.

    DOES NOT reimplement resolution - calls existing functions.
    """

    # Signals
    value_changed = pyqtSignal(str, str, object, object)  # scope_id, field, old_resolved, new_resolved
    scope_dirty_changed = pyqtSignal(str, bool)  # scope_id, is_dirty

    # Cache (computed via existing infrastructure)
    _current: Dict[str, Dict[str, Any]]      # scope_id -> field -> resolved_value
    _snapshots: Dict[str, Dict[str, Dict[str, Any]]]  # snapshot_name -> scope_id -> field -> value

    # Singleton
    _instance: Optional['ResolvedValueRegistry'] = None
```

**Key Methods:**
- `register_scope(scope_id, context_obj, object_instance)` - Register object for tracking
- `unregister_scope(scope_id)` - Remove from tracking
- `get_resolved(scope_id, field_name) -> Any` - O(1) cache lookup
- `get_placeholder_text(scope_id, field_name) -> str` - Formatted for display
- `save_snapshot(name)` - Capture current state
- `diff_from_snapshot(name) -> Dict[str, Set[str]]` - Find differences
- `is_dirty(scope_id, snapshot_name) -> bool` - Check if scope has unsaved changes

#### 2. Resolution: REUSE ParameterOpsService Pattern

The Registry computes resolved values **exactly like `ParameterOpsService.resolve_single_placeholder()`** already does:

```python
def _compute_resolved(self, scope_id: str, field_name: str) -> Any:
    """
    Compute resolved value using EXISTING infrastructure.

    This is the same pattern as ParameterOpsService.resolve_single_placeholder()
    but without requiring a form manager.
    """
    from openhcs.config_framework.context_manager import build_context_stack
    from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService

    # Get registered info for this scope
    scope_info = self._registered_scopes[scope_id]
    context_obj = scope_info.context_obj
    object_instance = scope_info.object_instance

    # Collect live context (REUSE existing)
    live_snapshot = LiveContextService.collect(
        scope_filter=scope_id,
        for_type=type(context_obj) if context_obj else None
    )

    # Build context stack (REUSE existing)
    stack = build_context_stack(
        context_obj=context_obj,
        overlay=None,  # No overlay - we want resolved value
        object_instance=object_instance,
        live_context=live_snapshot.values if live_snapshot else None,
    )

    # Resolve within context (REUSE existing)
    with stack:
        return getattr(object_instance, field_name)
```

#### 3. Registry Subscribes to LiveContext

```python
def __init__(self):
    super().__init__()
    # Subscribe to ALL LiveContext changes
    LiveContextService.connect_listener(self._on_live_context_changed)

def _on_live_context_changed(self, scope_id: str, field_name: str, raw_value: Any):
    """LiveContext changed → recompute affected resolved values."""
    # 1. Recompute this scope's field
    self._recompute_field(scope_id, field_name)

    # 2. Cascade to children (REUSE existing scope parsing)
    from openhcs.config_framework.context_manager import get_root_from_scope_key

    for child_scope_id in self._registered_scopes:
        if child_scope_id.startswith(f"{scope_id}::"):
            # Check if child inherits this field (raw value is None)
            if self._get_raw_value(child_scope_id, field_name) is None:
                self._recompute_field(child_scope_id, field_name)
```

#### 4. Hierarchy: REUSE Existing Parsing

**NO new hierarchy logic.** Use existing:

```python
def _get_parent_scope_id(self, scope_id: str) -> Optional[str]:
    """REUSE: Same logic as get_root_from_scope_key but for immediate parent."""
    if "::" in scope_id:
        return scope_id.rsplit("::", 1)[0]
    return None  # Root scope
```

Scope IDs already encode hierarchy:
- `plate_001` → orchestrator (root)
- `plate_001::step_0` → step (child of plate_001)

#### 5. Registration Points (Existing Code Hooks)

| Event | Location | Action |
|-------|----------|--------|
| Orchestrator loaded | `PlateManager._load_orchestrator()` | `registry.register_scope(plate_path, pipeline_config, pipeline_config)` |
| Step added | `PipelineEditor.add_step()` | `registry.register_scope(step_scope_id, pipeline_config, step)` |
| Step deleted | `PipelineEditor._perform_delete()` | `registry.unregister_scope(step_scope_id)` |
| Pipeline loaded | `PipelineEditor.load_pipeline()` | Register all steps |
| Plate closed | `PlateManager.close_orchestrator()` | Unregister orchestrator + all steps |

#### 6. Refactor ParameterFormManager

**Before (computes placeholders via ParameterOpsService):**
```python
def _refresh_single_placeholder(self, field_name):
    # ParameterOpsService builds context stack, collects live context, resolves
    self._ops_service.resolve_single_placeholder(self, field_name, ...)
```

**After (reads from registry cache):**
```python
def _refresh_single_placeholder(self, field_name):
    registry = ResolvedValueRegistry.instance()
    placeholder = registry.get_placeholder_text(self.scope_id, field_name)
    PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder)
```

**Writes unchanged** - PFM still writes to LiveContext, registry listens.

#### 7. Placeholder Text: REUSE Existing

```python
def get_placeholder_text(self, scope_id: str, field_name: str) -> str:
    """Format resolved value as placeholder text using EXISTING service."""
    from openhcs.config_framework.placeholder import LazyDefaultPlaceholderService

    resolved = self.get_resolved(scope_id, field_name)
    scope_info = self._registered_scopes[scope_id]

    # REUSE existing placeholder formatting
    return LazyDefaultPlaceholderService.format_placeholder_value(
        resolved,
        prefix="Inherited" if self._is_inherited(scope_id, field_name) else None
    )
```

#### 8. List Item Integration (AbstractManagerWidget)

```python
# In _build_item_label() or similar
def _get_resolved_label(self, item) -> str:
    scope_id = self._get_scope_id_for_item(item)
    registry = ResolvedValueRegistry.instance()
    return registry.get_resolved(scope_id, "name") or "Unnamed"

# Connect to registry for updates
registry.value_changed.connect(self._on_resolved_value_changed)

def _on_resolved_value_changed(self, scope_id, field, old_val, new_val):
    if field == "name" and self._has_item_with_scope(scope_id):
        self._flash_item(scope_id)
        self.update_item_list()
```

### Findings

**Existing Infrastructure (MUST REUSE - NO REIMPLEMENTATION):**

| What | Where | Reuse How |
|------|-------|-----------|
| Context stack building | `build_context_stack()` | Call directly for resolution |
| Live context collection | `LiveContextService.collect()` | Call with scope_filter |
| MRO resolution | `resolve_field_inheritance()` | Called implicitly via `getattr()` on lazy objects |
| Placeholder formatting | `LazyDefaultPlaceholderService` | Call for UI display |
| Scope parsing | `get_root_from_scope_key()` | Already uses `::` separator |
| Type hierarchy | `get_ancestors_from_hierarchy()` | For MRO dependency tracking |
| Scope visibility | `_is_scope_visible()` | Already in LiveContextService |

**Key Insight 1:** scope_id is identity-based (token assigned at creation), not position-based. Reordering steps does NOT change their scope_id, so snapshots/comparisons remain valid.

**Key Insight 2:** Resolution has TWO dimensions:
1. **Scope hierarchy (vertical):** `plate_001::step_0` → `plate_001` → `None` (global)
2. **MRO hierarchy (horizontal):** `StepWellFilterConfig` → `WellFilterConfig` (within same scope)

Both are ALREADY HANDLED by existing infrastructure:
- Scope hierarchy: `build_context_stack()` + `LiveContextService.collect(scope_filter=...)`
- MRO hierarchy: `resolve_field_inheritance()` (called implicitly by lazy `__getattribute__`)

**Key Insight 3:** `ParameterOpsService.resolve_single_placeholder()` already does exactly what we need. The Registry just:
1. Calls the same functions without requiring a form manager
2. Caches results
3. Tracks what to recompute on change
4. Emits signals

### Implementation Draft

*Only write code here after smell loop passes.*

