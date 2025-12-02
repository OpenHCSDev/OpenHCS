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

#### 4. Change Detection: Use scoped_values + Recompute Children

**Fix for review point 2:** Use `scoped_values` (per-scope) instead of `values` (merged).
**Fix for review point 4:** When a scope changes, also recompute child scopes.

```python
def __init__(self):
    super().__init__()
    self._previous_token: int = -1
    LiveContextService.connect_listener(self._on_live_context_changed)

def _on_live_context_changed(self):
    """LiveContext changed → recompute all scopes."""
    # Use token to detect if anything actually changed
    snapshot = LiveContextService.collect()
    if snapshot.token == self._previous_token:
        return
    self._previous_token = snapshot.token

    # Recompute all registered scopes
    # (Token changed = something changed, recompute everything)
    for scope_id in self._scopes:
        self._recompute_scope(scope_id)

def _recompute_scope(self, scope_id: str):
    """Recompute all cached fields for a scope."""
    if scope_id not in self._current:
        return

    for field_name, old_value in list(self._current[scope_id].items()):
        new_value = self._compute_resolved(scope_id, field_name)
        if new_value != old_value:
            self._current[scope_id][field_name] = new_value
            self.value_changed.emit(scope_id, field_name, old_value, new_value)
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

