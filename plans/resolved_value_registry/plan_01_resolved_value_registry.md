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

**IMPORTANT:** Registry represents COMMITTED state (saved values + live context from OTHER open forms). It must EXCLUDE the editing scope's unsaved values to avoid drift as user types.

**Two-layer approach:**
1. `.values` (root-filtered) for ancestor scopes (pipeline/global) - so child sees parent's live edits
2. `.scoped_values[scope_id]` EXCLUDED when computing that scope - so we don't include our own unsaved values

```python
def _compute_resolved(self, scope_id: str, field_name: str, exclude_scope: str = None) -> Any:
    """Compute resolved value using EXISTING infrastructure.

    Two-layer live context:
    1. .values (root-filtered) - sees ancestor edits (pipeline/global)
    2. Exclude the editing scope to avoid including unsaved values

    Args:
        exclude_scope: Scope to exclude from live context (typically the scope being computed
                       or the scope that triggered the change)
    """
    from openhcs.config_framework.context_manager import build_context_stack, get_root_from_scope_key
    from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService

    reg = self._scopes[scope_id]
    my_root = get_root_from_scope_key(scope_id)

    # Collect live context with root filter (sees ancestor edits)
    live_snapshot = LiveContextService.collect(scope_filter=scope_id)

    # Build merged live context:
    # 1. Start with .values (type-keyed, has ancestor data)
    # 2. Filter to same root (plate isolation)
    # 3. EXCLUDE the editing scope's values to get "committed" state
    merged_live = {}
    if live_snapshot:
        for type_key, val in live_snapshot.values.items():
            merged_live[type_key] = val

        # Remove the excluded scope's contributions
        if exclude_scope and exclude_scope in live_snapshot.scoped_values:
            excluded_types = set(live_snapshot.scoped_values[exclude_scope].keys())
            for t in excluded_types:
                merged_live.pop(t, None)

    # Build context stack
    stack = build_context_stack(
        context_obj=reg.context_obj,
        object_instance=reg.object_instance,
        live_context=merged_live,
    )

    # getattr triggers lazy resolution
    with stack:
        return getattr(reg.object_instance, field_name)
```

**When to exclude:**
- `_on_context_value_changed(editing_scope_id)` → exclude `editing_scope_id`
- `is_dirty()` check → exclude the scope being checked (compare saved vs committed-without-self)

#### 4. Change Detection: Scope Hierarchy from scope_id String

**Key insight:** scope_id format encodes the full hierarchy:
- `""` (empty) → global scope
- `"plate_path"` → pipeline scope (PipelineConfig)
- `"plate_path::token"` → step scope (FunctionStep)

No type introspection needed. Just string prefix matching.

```python
# openhcs/config_framework/context_manager.py (add to existing file)

def is_scope_affected(target_scope_id: str, editing_scope_id: str) -> bool:
    """Check if target scope is affected by edit at editing scope.

    Uses scope_id hierarchy - no type introspection needed:
    - "" (global) → affects all
    - "plate_path" (pipeline) → affects same plate + all its steps
    - "plate_path::token" (step) → affects only that step
    """
    # Global edit affects all
    if not editing_scope_id:
        return True

    # Different plate roots = not affected
    target_root = get_root_from_scope_key(target_scope_id)
    editing_root = get_root_from_scope_key(editing_scope_id)
    if target_root != editing_root:
        return False

    # Same root: parent affects children, not vice versa
    # editing="plate" affects target="plate::step" ✓
    # editing="plate::step" affects target="plate" ✗
    return (
        target_scope_id == editing_scope_id or
        target_scope_id.startswith(editing_scope_id + "::")
    )
```

**Registry uses this:**
```python
def _on_context_changed(self, editing_scope_id: str):
    """LiveContext changed → recompute affected scopes."""
    for target_scope_id in self._scopes:
        if is_scope_affected(target_scope_id, editing_scope_id):
            self._recompute_scope(target_scope_id)
```

**PFM refactored:** Delete `_is_affected_by_context_change()`, call `is_scope_affected()` directly at call sites.

**Two signals cover all change sources:**

1. `context_value_changed` → per-field changes (user typing)
2. `context_refreshed` → bulk changes (save/cancel, `trigger_global_refresh()`)

```python
def __init__(self):
    ParameterFormManager.context_value_changed.connect(self._on_context_changed)
    ParameterFormManager.context_refreshed.connect(self._on_context_changed)

def _on_context_changed(self, *args):
    """Extract editing_scope_id (last arg) and recompute affected scopes."""
    editing_scope_id = args[-1]  # Both signals have scope_id as last arg

    for target_scope_id in self._scopes:
        if target_scope_id == editing_scope_id:
            continue  # Don't recompute the scope being edited
        if is_scope_affected(target_scope_id, editing_scope_id):
            self._recompute_scope(target_scope_id, exclude_scope=editing_scope_id)
```

**Why one handler?** Both signals have `editing_scope_id` as last arg. We only need that for affectedness check - the other args (`editing_obj`, `context_obj`) were for type introspection which is now gone.

**`_recompute_scope()` - emit only when value actually changed:**

```python
def _recompute_scope(self, scope_id: str, exclude_scope: str = None):
    """Recompute all tracked fields for a scope, emit value_changed only if different.

    CRITICAL: Only emits value_changed when old != new.
    - Step with override (well_filter=3): resolved stays 3 → NO signal
    - Step inheriting (well_filter=None): resolved changes 5→7 → EMIT signal
    """
    reg = self._scopes.get(scope_id)
    if not reg:
        return

    old_values = self._current.get(scope_id, {})
    new_values = {}

    # Recompute all fields on the object
    for field in fields(type(reg.object_instance)):
        field_name = field.name
        new_val = self._compute_resolved(scope_id, field_name, exclude_scope)
        new_values[field_name] = new_val

        old_val = old_values.get(field_name)

        # Only emit if value actually changed
        if old_val != new_val:
            self.value_changed.emit(scope_id, field_name, old_val, new_val)

    # Update cache
    self._current[scope_id] = new_values
```

This means:
- Step A (`well_filter=3` override): pipeline changes → resolved still 3 → **no flash**
- Step B (`well_filter=None` inheriting): pipeline changes 5→7 → resolved changes → **flash**

#### 5. Placeholder Text: Format Cached Value

**CRITICAL:** Do NOT re-resolve via `LazyDefaultPlaceholderService` - that would do duplicate resolution and could drift from cached value. Instead, format the cached resolved value directly.

```python
def get_placeholder_text(self, scope_id: str, field_name: str) -> str:
    """Format the CACHED resolved value as placeholder text.

    Uses cached value from get_resolved() - NO re-resolution.
    """
    resolved = self.get_resolved(scope_id, field_name)

    if resolved is None:
        return ""  # No placeholder for None

    # Format as "Default: <value>" or "Inherited: <value>"
    # For now use "Default" prefix - can be enhanced later to detect inheritance
    prefix = "Default"
    return f"{prefix}: {resolved}"
```

**Note:** This is simpler than calling `LazyDefaultPlaceholderService` because:
1. We already have the resolved value cached
2. No need to re-resolve (which requires context stack setup)
3. The placeholder text is just a formatted string

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

#### 8. List Item Integration (in AbstractManagerWidget)

**Refactor `_resolve_preview_field_value()` to read from registry:**

```python
# AbstractManagerWidget - concrete classes get this automatically

def _resolve_preview_field_value(
    self,
    item: Any,
    config_source: Any,
    field_path: str,
    live_context_snapshot: Any = None,  # IGNORED after refactor
    fallback_context: Optional[Dict[str, Any]] = None,
) -> Any:
    """Resolve a preview field value - reads from registry instead of building context."""
    registry = ResolvedValueRegistry.instance()
    scope_id = self._get_item_scope_id(item)  # Abstract method, implemented by subclass

    # Just read cached resolved value - no context stack needed
    return registry.get_resolved(scope_id, field_path)

@abstractmethod
def _get_item_scope_id(self, item: Any) -> str:
    """Get scope_id for an item. Subclass implements."""
    # PipelineEditor: return self._build_step_scope_id(step)
    # PlateManager: return plate['path']
    ...
```

**Remove `_get_step_preview_instance()` complexity:**

The current flow builds a merged step copy with live values. After refactor, registry has resolved values - no merging needed.

**React to changes (in AbstractManagerWidget):**

```python
def _init_registry_connection(self):
    """Connect to registry for list updates. Called in __init__."""
    registry = ResolvedValueRegistry.instance()
    registry.value_changed.connect(self._on_registry_value_changed)
    registry.scope_dirty_changed.connect(self._on_scope_dirty_changed)

def _on_registry_value_changed(self, scope_id: str, field: str, old_val: Any, new_val: Any):
    """Registry value changed - update affected list item."""
    if self._has_item_with_scope(scope_id):
        self._refresh_item_by_scope(scope_id)
        self._flash_item(scope_id)  # Optional: visual feedback

def _on_scope_dirty_changed(self, scope_id: str, is_dirty: bool):
    """Scope dirty state changed - update list item visual."""
    if self._has_item_with_scope(scope_id):
        self._update_item_dirty_state(scope_id, is_dirty)
```

**Dirty marking for list items (in AbstractManagerWidget):**

```python
def _update_item_dirty_state(self, scope_id: str, is_dirty: bool):
    """Update visual dirty indicator for list item."""
    # Find item by scope_id and update its visual state
    # e.g., add/remove "•" prefix, change font style, etc.
    item = self._find_item_by_scope(scope_id)
    if item:
        text = item.text()
        if is_dirty and not text.startswith("• "):
            item.setText(f"• {text}")
        elif not is_dirty and text.startswith("• "):
            item.setText(text[2:])

def is_item_dirty(self, item: Any) -> bool:
    """Check if item has unsaved changes (compared to last snapshot)."""
    registry = ResolvedValueRegistry.instance()
    scope_id = self._get_item_scope_id(item)
    return registry.is_dirty(scope_id, snapshot_name="last_save")
```

**Snapshot lifecycle:**

```python
# In save handler (AbstractManagerWidget or subclass)
def _on_save(self):
    self._do_save()  # persist to disk

    # Update snapshot after save - values are now "saved state"
    registry = ResolvedValueRegistry.instance()
    registry.save_snapshot("last_save")  # Captures current resolved values

    # All items now clean (current == snapshot)
    # scope_dirty_changed signals will fire for any that were dirty
```

**Concrete classes just implement `_get_item_scope_id()`:**

```python
# PipelineEditor
def _get_item_scope_id(self, step: FunctionStep) -> str:
    return self._build_step_scope_id(step)

# PlateManager
def _get_item_scope_id(self, plate: Dict) -> str:
    return plate['path']
```

### Findings

**Key Insight 1:** Two-layer live context needed:
- `.values` (type-keyed) for ancestor data - so children see parent's live edits
- EXCLUDE the editing scope's contributions to get "committed" state without own unsaved values

**Key Insight 2:** `LiveContextService.collect(scope_filter=scope_id)` includes the active manager's unsaved values. Must exclude editing scope when computing resolved values, otherwise registry drifts as user types.

**Key Insight 3:** Two signals cover all changes - no token-based fallback needed:
- `context_value_changed` for per-field changes
- `context_refreshed` for bulk changes (save/cancel, `trigger_global_refresh()`)

**Key Insight 4:** `get_placeholder_text()` must format the CACHED value, not re-resolve. Re-resolution requires context stack setup and can drift from cached value.

**Key Insight 5:** Child scopes automatically get correct values because `build_context_stack()` + lazy resolution already handles scope hierarchy. We just need to recompute when parent changes.

### Implementation Draft

*Only write code here after smell loop passes.*

