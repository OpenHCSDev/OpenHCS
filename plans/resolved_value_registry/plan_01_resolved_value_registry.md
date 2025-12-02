# plan_01_resolved_value_registry.md
## Component: ResolvedValueRegistry - Centralized Resolved Value Service

### Objective

Create a centralized registry that is the **single source of truth** for resolved configuration values:
1. Computes resolved values for ALL registered scopes
2. Listens to LiveContext changes and recomputes affected scopes + children
3. Emits signals when resolved values change (for flash animations)
4. Supports snapshotting for unsaved changes detection

**Access patterns:**
- **ParameterFormManager**: reads AND writes (writes to LiveContext → Registry listens)
- **List items**: read-only (display resolved values, react to changes)

### ⚠️ ZERO REIMPLEMENTATION POLICY

**ALL resolution logic already exists.** The Registry is a THIN COORDINATION LAYER that:
1. Caches results from existing infrastructure
2. Tracks what needs recomputing when LiveContext changes
3. Emits signals for UI updates

**Existing infrastructure to CALL (not reimplement):**

| Component | Location | What it does |
|-----------|----------|--------------|
| `build_context_stack()` | `config_framework.context_manager` | Builds complete context stack for resolution |
| `LiveContextService.collect()` | `services.live_context_service` | Collects live values with scope filtering |
| `LazyDefaultPlaceholderService` | `core.lazy_placeholder_simplified` | Formats resolved value as placeholder text |
| `get_root_from_scope_key()` | `config_framework.context_manager` | Parses scope_id hierarchy |

### Plan

#### 1. Create ResolvedValueRegistry Service

**File:** `openhcs/pyqt_gui/widgets/shared/services/resolved_value_registry.py`

```python
@dataclass
class ScopeRegistration:
    """Registration info for a scope."""
    scope_id: str
    context_obj: Any  # Parent context (e.g., pipeline_config for steps)
    object_instance: Any  # The object being tracked

class ResolvedValueRegistry(QObject):
    """
    Single source of truth for resolved configuration values.

    - PFM writes to LiveContext, Registry listens and recomputes
    - PFM reads placeholder text from Registry
    - List items read resolved values from Registry
    """

    # Signals
    value_changed = pyqtSignal(str, str, object, object)  # scope_id, field, old, new
    scope_dirty_changed = pyqtSignal(str, bool)  # scope_id, is_dirty

    # Per-scope registration
    _scopes: Dict[str, ScopeRegistration]

    # Cache: scope_id -> field -> resolved_value
    _current: Dict[str, Dict[str, Any]]
    _snapshots: Dict[str, Dict[str, Dict[str, Any]]]  # snapshot_name -> scope_id -> field -> value

    # Singleton
    _instance: Optional['ResolvedValueRegistry'] = None
```

**Key Methods:**
- `register_scope(scope_id, context_obj, object_instance)` - Register scope for tracking
- `unregister_scope(scope_id)` - Remove from tracking
- `get_resolved(scope_id, field_name) -> Any` - O(1) cache lookup
- `get_placeholder_text(scope_id, field_name) -> str` - Formatted for display
- `save_snapshot(name)` - Capture current state
- `is_dirty(scope_id, snapshot_name) -> bool` - Check if scope has unsaved changes

#### 2. Per-Scope Registration

Registration is **per-scope**, not per-field. The scope knows its object instance:

```python
def register_scope(self, scope_id: str, context_obj: Any, object_instance: Any):
    """Register a scope for tracking."""
    self._scopes[scope_id] = ScopeRegistration(
        scope_id=scope_id,
        context_obj=context_obj,
        object_instance=object_instance,
    )
    # Initial computation happens on first get_resolved() call
```

#### 3. Resolution: Use Existing Services

```python
def _compute_resolved(self, scope_id: str, field_name: str) -> Any:
    """Compute resolved value using EXISTING infrastructure."""
    from openhcs.config_framework.context_manager import build_context_stack
    from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService

    reg = self._scopes[scope_id]

    # Collect live context - use scoped_values for per-scope data
    live_snapshot = LiveContextService.collect(scope_filter=scope_id)

    # Build context stack (same as ParameterOpsService does)
    stack = build_context_stack(
        context_obj=reg.context_obj,
        object_instance=reg.object_instance,
        live_context=live_snapshot.values if live_snapshot else None,
    )

    # getattr triggers lazy resolution
    with stack:
        return getattr(reg.object_instance, field_name)
```

#### 4. Change Detection: Extract + Reuse PFM's Invalidation Logic

**Current PFM approach:** Each PFM receives "something changed" callback and uses `_is_affected_by_context_change()` to decide whether to refresh.

**Extract to reusable function:** Move `_is_affected_by_context_change()` logic to a service function that both PFM and Registry can call.

```python
# NEW: openhcs/pyqt_gui/widgets/shared/services/scope_invalidation_service.py

def is_scope_affected_by_change(
    target_scope_id: str,
    target_object_instance: Any,
    target_context_obj: Any,
    editing_object: Any,
    editing_context_obj: Any,
    editing_scope_id: str,
) -> bool:
    """
    Determine if a scope is affected by a context change.

    EXTRACTED from PFM._is_affected_by_context_change() for reuse.
    Uses existing config_framework hierarchy functions.
    """
    from openhcs.config_framework import is_global_config_instance
    from openhcs.config_framework.context_manager import (
        is_ancestor_in_context,
        is_same_type_in_context,
        get_root_from_scope_key,
    )
    from dataclasses import fields, is_dataclass
    import typing

    # Root isolation: different plate roots don't affect each other
    my_root = get_root_from_scope_key(target_scope_id)
    editing_root = get_root_from_scope_key(editing_scope_id)
    if editing_root and my_root and editing_root != my_root:
        return False

    editing_type = type(editing_object)

    # Global config edits affect all
    if is_global_config_instance(editing_object):
        return True

    # Ancestor/same-type checks for context object
    if target_context_obj is not None:
        context_obj_type = type(target_context_obj)
        if is_ancestor_in_context(editing_type, context_obj_type):
            return True
        if is_same_type_in_context(editing_type, context_obj_type):
            return True

    # Check dataclass fields for direct type match (handles nested configs)
    if is_dataclass(editing_object) and is_dataclass(target_object_instance):
        for field in fields(type(target_object_instance)):
            if field.type == editing_type:
                return True
            origin = typing.get_origin(field.type)
            if origin is typing.Union:
                args = typing.get_args(field.type)
                if editing_type in args:
                    return True

    return False
```

**Registry uses this:**
```python
def _on_live_context_changed(self, editing_object, editing_context_obj, editing_scope_id):
    """LiveContext changed → recompute affected scopes only."""
    from .scope_invalidation_service import is_scope_affected_by_change

    for scope_id, reg in self._scopes.items():
        if is_scope_affected_by_change(
            target_scope_id=scope_id,
            target_object_instance=reg.object_instance,
            target_context_obj=reg.context_obj,
            editing_object=editing_object,
            editing_context_obj=editing_context_obj,
            editing_scope_id=editing_scope_id,
        ):
            self._recompute_scope(scope_id)
```

**PFM refactored to use same function:**
```python
def _is_affected_by_context_change(self, editing_object, context_object, editing_scope_id):
    from .services.scope_invalidation_service import is_scope_affected_by_change
    return is_scope_affected_by_change(
        target_scope_id=self.scope_id,
        target_object_instance=self.object_instance,
        target_context_obj=self.context_obj,
        editing_object=editing_object,
        editing_context_obj=context_object,
        editing_scope_id=editing_scope_id,
    )
```

**Two notification paths exist:**

1. `LiveContextService.connect_listener(callback)` → callback with NO args → "something changed"
   - PFM uses this for bulk refresh (save/cancel/code editor)
   - Registry uses this as fallback: recompute all scopes

2. `ParameterFormManager.context_value_changed` signal → HAS args (field_path, new_value, editing_obj, context_obj, scope_id)
   - PFM uses this for targeted refresh with `_is_affected_by_context_change()` filtering
   - Registry can connect to this for smart invalidation (only affected scopes)

**Registry subscribes to BOTH:**
```python
def __init__(self):
    # Bulk invalidation (something changed, don't know what)
    LiveContextService.connect_listener(self._on_live_context_changed_bulk)

    # Targeted invalidation (know exactly what changed)
    ParameterFormManager.context_value_changed.connect(self._on_context_value_changed)

def _on_live_context_changed_bulk(self):
    """Fallback: recompute all scopes."""
    for scope_id in self._scopes:
        self._recompute_scope(scope_id)

def _on_context_value_changed(self, field_path, new_value, editing_obj, context_obj, scope_id):
    """Targeted: only recompute affected scopes."""
    for target_scope_id, reg in self._scopes.items():
        if is_scope_affected_by_change(...):
            self._recompute_scope(target_scope_id)
```

#### 5. Placeholder Text: Use Existing Service

```python
def get_placeholder_text(self, scope_id: str, field_name: str) -> str:
    """Format resolved value using EXISTING LazyDefaultPlaceholderService."""
    from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

    resolved = self.get_resolved(scope_id, field_name)
    reg = self._scopes[scope_id]

    # Use existing service - it handles all formatting
    return LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
        dataclass_type=type(reg.object_instance),
        field_name=field_name,
    )
```

#### 6. Registration Points

| Event | Location | Action |
|-------|----------|--------|
| Orchestrator loaded | `PlateManager._load_orchestrator()` | `registry.register_scope(plate_path, None, pipeline_config)` |
| Step added | `PipelineEditor.add_step()` | `registry.register_scope(step_scope_id, pipeline_config, step)` |
| Step deleted | `PipelineEditor._perform_delete()` | `registry.unregister_scope(step_scope_id)` |
| Plate closed | `PlateManager.close_orchestrator()` | Unregister orchestrator + all steps |

#### 7. ParameterFormManager Integration

**Reads from Registry (not ParameterOpsService):**
```python
def _refresh_single_placeholder(self, field_name):
    registry = ResolvedValueRegistry.instance()
    placeholder = registry.get_placeholder_text(self.scope_id, field_name)
    PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder)
```

**Writes unchanged** - PFM still writes to LiveContext, Registry listens.

#### 8. List Item Integration

```python
# Read resolved value
def _get_resolved_label(self, item) -> str:
    registry = ResolvedValueRegistry.instance()
    return registry.get_resolved(scope_id, "name") or "Unnamed"

# React to changes
registry.value_changed.connect(self._on_resolved_value_changed)

def _on_resolved_value_changed(self, scope_id, field, old_val, new_val):
    if self._has_item_with_scope(scope_id):
        self._flash_item(scope_id)
        self.update_item_list()
```

### Findings

**Key Insight 1:** `LiveContextSnapshot.scoped_values` gives per-scope data, while `.values` is merged across all scopes. Use `scoped_values` for change detection.

**Key Insight 2:** Token-based invalidation is simpler than diffing. If `snapshot.token` changed, recompute everything. The token increments on ANY LiveContext change.

**Key Insight 3:** Child scopes automatically get correct values because `build_context_stack()` + lazy resolution already handles scope hierarchy. We just need to recompute when parent changes.

### Implementation Draft

*Only write code here after smell loop passes.*

