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

### Plan

#### 1. Create ResolvedValueRegistry Service

**File:** `openhcs/pyqt_gui/widgets/shared/services/resolved_value_registry.py`

```python
class ResolvedValueRegistry(QObject):
    """Single source of truth for all resolved values across all scopes."""
    
    # Signals
    value_changed = pyqtSignal(str, str, object, object)  # scope_id, field, old_resolved, new_resolved
    scope_dirty_changed = pyqtSignal(str, bool)  # scope_id, is_dirty
    
    # State
    _current: Dict[str, Dict[str, Any]]      # scope_id -> field -> resolved_value
    _snapshots: Dict[str, Dict[str, Dict[str, Any]]]  # snapshot_name -> scope_id -> field -> value
    
    # Singleton
    _instance: Optional['ResolvedValueRegistry'] = None
```

**Key Methods:**
- `register_scope(scope_id, dataclass_type, parent_scope_id)` - Register object for tracking
- `unregister_scope(scope_id)` - Remove from tracking
- `get_resolved(scope_id, field_name) -> Any` - O(1) lookup
- `get_placeholder_text(scope_id, field_name) -> str` - Formatted for display
- `save_snapshot(name)` - Capture current state
- `diff_from_snapshot(name) -> Dict[str, Set[str]]` - Find differences
- `is_dirty(scope_id, snapshot_name) -> bool` - Check if scope has unsaved changes

#### 2. Registry Subscribes to LiveContext

```python
def __init__(self):
    super().__init__()
    # Subscribe to ALL LiveContext changes
    LiveContextService.connect_listener(self._on_live_context_changed)

def _on_live_context_changed(self, scope_id: str, field_name: str, raw_value: Any):
    """LiveContext changed → recompute affected resolved values."""
    # 1. Recompute this scope's field
    self._recompute_field(scope_id, field_name)
    
    # 2. Cascade to children that inherit (scope_id prefix match)
    for child_scope_id in self._get_inheriting_children(scope_id, field_name):
        self._recompute_field(child_scope_id, field_name)
```

#### 3. Hierarchy via scope_id Parsing

Scope IDs already encode hierarchy:
- `plate_001` → orchestrator (root)
- `plate_001::step_0` → step (child of plate_001)

```python
def _get_parent_scope_id(self, scope_id: str) -> Optional[str]:
    if "::" in scope_id:
        return scope_id.rsplit("::", 1)[0]
    return None  # Root scope

def _get_inheriting_children(self, parent_scope_id: str, field_name: str) -> List[str]:
    """Find children whose resolved value depends on parent."""
    children = []
    for child_id in self._current:
        if child_id.startswith(f"{parent_scope_id}::"):
            # Check if child has explicit value (doesn't inherit)
            if self._raw_values.get(child_id, {}).get(field_name) is None:
                children.append(child_id)
    return children
```

#### 4. Resolution Logic

```python
def _compute_resolved(self, scope_id: str, field_name: str) -> Any:
    """Walk up hierarchy until non-None value found."""
    # Check this scope's raw value
    raw = self._raw_values.get(scope_id, {}).get(field_name)
    if raw is not None:
        return raw
    
    # Inherit from parent
    parent = self._get_parent_scope_id(scope_id)
    if parent and parent in self._current:
        return self._compute_resolved(parent, field_name)
    
    # Fall back to global config default
    return self._get_static_default(scope_id, field_name)
```

#### 5. Registration Points (Existing Code Hooks)

| Event | Location | Action |
|-------|----------|--------|
| Orchestrator loaded | `PlateManager._load_orchestrator()` | `registry.register_scope(plate_path, PipelineConfig, None)` |
| Step added | `PipelineEditor.add_step()` | `registry.register_scope(step_scope_id, step_type, plate_scope)` |
| Step deleted | `PipelineEditor._perform_delete()` | `registry.unregister_scope(step_scope_id)` |
| Pipeline loaded | `PipelineEditor.load_pipeline()` | Register all steps |
| Plate closed | `PlateManager.close_orchestrator()` | Unregister orchestrator + all steps |

#### 6. Refactor ParameterFormManager

**Before (computes placeholders):**
```python
def _refresh_single_placeholder(self, field_name):
    with build_context_stack(...):
        placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(...)
    PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder)
```

**After (reads from registry):**
```python
def _refresh_single_placeholder(self, field_name):
    registry = ResolvedValueRegistry.instance()
    placeholder = registry.get_placeholder_text(self.scope_id, field_name)
    PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder)
```

**Writes unchanged** - PFM still writes to LiveContext, registry listens.

#### 7. List Item Integration (AbstractManagerWidget)

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

**Existing Infrastructure (reuse):**
- `LiveContextService` - Already handles cross-window change propagation
- `ContextStackRegistry` - Tracks registered objects (can provide dataclass_type info)
- `scope_id` format - Already encodes hierarchy via `::` separator
- `_pipeline_scope_token` - Stable tokens per step (survives reordering)
- `resolve_field_inheritance()` - MRO-based resolution (can be called directly by Registry)
- `extract_all_configs()` - Builds available_configs dict from context object

**Key Insight 1:** scope_id is identity-based (token assigned at creation), not position-based. Reordering steps does NOT change their scope_id, so snapshots/comparisons remain valid.

**Key Insight 2:** Resolution has TWO dimensions:
1. **Scope hierarchy (vertical):** `plate_001::step_0` → `plate_001` → `None` (global)
2. **MRO hierarchy (horizontal):** `StepWellFilterConfig` → `WellFilterConfig` (within same scope)

Even at `scope_id=None` (GlobalPipelineConfig), MRO inheritance applies. When `well_filter_config.well_filter` changes, `step_well_filter_config.well_filter` must be recomputed if it inherits (is None).

**Resolution Algorithm (existing, reuse):**
```python
# From dual_axis_resolver.py - resolve_field_inheritance()
for mro_class in obj_type.__mro__:
    for config_name, config_instance in available_configs.items():
        if type(config_instance) == mro_class:
            value = object.__getattribute__(config_instance, field_name)
            if value is not None:
                return value
```

The Registry can call this directly. It just needs to:
1. Build `available_configs` from LiveContext for each scope
2. Call `resolve_field_inheritance()`
3. Track which scopes have types whose MRO includes the changed type → recompute those

**Dependency Tracking for MRO:**

When `WellFilterConfig.well_filter` changes (in any scope), we must recompute fields for types where:
- `WellFilterConfig` is in their MRO (e.g., `StepWellFilterConfig`, `PathPlanningConfig`)
- Their raw value for that field is `None` (they inherit)

This can be computed once per type and cached:
```python
_mro_dependencies: Dict[str, Set[str]] = {
    'WellFilterConfig': {'StepWellFilterConfig', 'PathPlanningConfig', 'StepMaterializationConfig'},
    # ... auto-generated from class MRO at registration time
}
```

### Implementation Draft

*Only write code here after smell loop passes.*

