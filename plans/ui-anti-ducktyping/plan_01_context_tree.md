# Configuration Tree Refactoring Plan

## Executive Summary

Refactor the configuration resolution system from a "layer-based" abstraction to an explicit tree structure. The current system obscures the fact that configuration resolution is simply walking up a three-level hierarchy: Global → Plate → Step.

---

## Current System Analysis

### The "Layer" Abstraction Problem

The current code uses a "layer" metaphor that doesn't match reality:
```python
class ContextLayerType(Enum):
    GLOBAL_STATIC_DEFAULTS = 1   # Actually: 1 node (singleton)
    GLOBAL_LIVE_VALUES = 2       # Actually: 0-1 nodes (if window open)
    PARENT_CONTEXT = 3            # Actually: 1 node (the context_obj)
    PARENT_OVERLAY = 4            # Actually: 1 node (parent form)
    SIBLING_CONTEXTS = 5          # Actually: N nodes! (all siblings)
    CURRENT_OVERLAY = 6           # Actually: 1 node (self)
```

**The core issue**: "Layers" implies a flat stack, but at each level there are potentially N nodes (especially siblings). The `SiblingContextsBuilder` returns `List[ContextLayer]`, exposing that this isn't really a layer—it's a collection of nodes at the same level.

### Current Architecture
```
context_layer_builders.py (200+ lines)
├─ ContextLayerType enum (6 types)
├─ ContextLayerBuilderMeta (auto-registration)
├─ 6 builder classes (one per layer type)
└─ build_context_stack() orchestrator

Flow:
1. Iterate through ContextLayerType enum
2. For each type, get registered builder
3. Builder queries _active_form_managers to find other windows
4. Builder returns ContextLayer or List[ContextLayer]
5. Flatten all layers into ExitStack
6. Apply contexts bottom-up for lazy resolution
```

**Why it's complex**:
- Builders must query global `_active_form_managers` registry
- Complex scope filtering logic (`scope_id` matching)
- Special cases for `is_global_config_editing`, `skip_parent_overlay`, `use_user_modified_only`
- Sibling discovery via parent's `nested_managers` dict
- Cross-window live value collection

### What's Actually Happening

Despite the "layer" abstraction, the system is actually building a path through a tree:
```
Thread-Local Global (implicit)
    ↓
Plate (PipelineConfig)
    ↓
Step (Step instance)
```

Each node contains all its nested configs (e.g., `well_filter_config`, `path_planning_config`). Sibling inheritance works because they're **part of the same object** in the context stack.

---

## The Reality: Three-Level Hierarchy

### The Actual Structure
```
Global Level (scope_id=None)
└─ GlobalPipelineConfig (thread-local singleton)
    ├─ well_filter_config: WellFilterConfig
    ├─ path_planning_config: PathPlanningConfig
    ├─ napari_streaming_config: NapariStreamingConfig
    └─ ... (all @global_pipeline_config decorated types)

Plate Level (scope_id="plate_A", "plate_B", etc.)
├─ PipelineConfig instance
│   ├─ well_filter_config: WellFilterConfig = None (lazy)
│   ├─ path_planning_config: PathPlanningConfig = None (lazy)
│   └─ ... (same fields as Global, but lazy/None by default)
│
├─ Step1 instance
│   ├─ well_filter_config: WellFilterConfig = None (optional)
│   └─ step_materialization_config: StepMaterializationConfig = None (optional)
│
├─ Step2 instance
│   └─ well_filter_config: WellFilterConfig = None (optional)
│
└─ Step3 instance
    └─ path_planning_config: PathPlanningConfig = None (optional)
```

### Key Insights

1. **Tree nodes are whole objects**, not individual nested configs
   - A node is a `PipelineConfig` or `Step` instance
   - Each node contains multiple nested configs as fields

2. **Sibling inheritance is automatic**
   - `step_materialization_config` inherits from `well_filter_config`
   - They're both fields on the same `Step` instance
   - When you apply `config_context(step_instance)`, both configs are available

3. **Global is implicit**
   - Stored in thread-local storage via `set_base_global_config()`
   - Lazy resolution automatically walks up to thread-local global
   - No need to explicitly add to context stack

4. **Steps are peers, not siblings**
   - Step1 and Step2 don't see each other's values
   - They only see their parent (Plate) and global
   - They're separate branches of the tree, not siblings

---

## Proposed Design

### Tree Structure
```python
@dataclass
class ConfigNode:
    """
    A node in the configuration tree.
    
    Each node represents a whole object (PipelineConfig or Step),
    not an individual nested config.
    """
    
    # Identity
    node_id: str              # "plate_A", "plate_A.step1", etc.
    scope_id: str             # "plate_A", "plate_B" (for cross-window filtering)
    level: Literal["plate", "step"]  # No "global" - it's thread-local
    
    # Data
    object_instance: Any      # PipelineConfig or Step instance
    user_values: Dict[str, Any] = field(default_factory=dict)
    
    # Tree structure (data inheritance hierarchy)
    parent: Optional['ConfigNode'] = None  # Step → Plate, Plate → None
    children: List['ConfigNode'] = field(default_factory=list)  # Plate → [Step1, Step2, ...]
    
    def build_context_stack(self) -> ExitStack:
        """
        Build context stack by walking up tree to root.
        Global is implicit (thread-local), so not included.
        """
        stack = ExitStack()
        
        # Build path from self to root (Plate)
        path = []
        current = self
        while current:
            path.append(current)
            current = current.parent
        
        # Apply root to leaf
        for node in reversed(path):
            stack.enter_context(config_context(node.object_instance))
        
        return stack
    
    def resolve(self, field_name: str) -> Any:
        """
        Resolve a field value using context stack.
        Lazy resolution system handles the actual lookup.
        """
        with self.build_context_stack():
            return getattr(self.object_instance, field_name)
```

### Tree Registry
```python
class ConfigTreeRegistry:
    """
    Registry of all active config trees.
    Replaces _active_form_managers class-level list.
    """
    
    def __init__(self):
        self.trees: Dict[str, ConfigNode] = {}  # scope_id → root (Plate) node
        self.all_nodes: Dict[str, ConfigNode] = {}  # node_id → node
    
    def register_plate(self, scope_id: str, plate_config: Any) -> ConfigNode:
        """Register a new plate (root of a tree)."""
        node = ConfigNode(
            node_id=scope_id,
            scope_id=scope_id,
            level="plate",
            object_instance=plate_config,
            parent=None
        )
        self.trees[scope_id] = node
        self.all_nodes[scope_id] = node
        return node
    
    def register_step(self, scope_id: str, step_id: str, step_instance: Any) -> ConfigNode:
        """Register a step under a plate."""
        plate_node = self.trees[scope_id]
        
        node = ConfigNode(
            node_id=f"{scope_id}.{step_id}",
            scope_id=scope_id,
            level="step",
            object_instance=step_instance,
            parent=plate_node
        )
        
        plate_node.children.append(node)
        self.all_nodes[node.node_id] = node
        return node
    
    def get_plate(self, scope_id: str) -> Optional[ConfigNode]:
        """Get the plate node for a scope."""
        return self.trees.get(scope_id)
    
    def get_node(self, node_id: str) -> Optional[ConfigNode]:
        """Get any node by ID."""
        return self.all_nodes.get(node_id)
```

### Resolution Example

**Question**: What is `Step1.step_materialization_config.well_filter`?

**Current system** (6-layer approach):
```python
1. Check CURRENT_OVERLAY (Step1's user values)
2. Check SIBLING_CONTEXTS (Step1.well_filter_config) ← Found here!
3. Check PARENT_OVERLAY (Plate's user values)
4. Check PARENT_CONTEXT (Plate's lazy values)
5. Check GLOBAL_LIVE_VALUES (other windows editing Global)
6. Check GLOBAL_STATIC_DEFAULTS (fresh GlobalPipelineConfig)
```

**Proposed system** (tree walk):
```python
# Build context stack
step1_node.build_context_stack()
→ Returns: [plate_node, step1_node]

# Apply contexts
with config_context(plate_config):      # Plate level
    with config_context(step1_instance): # Step level (contains both configs!)
        # Lazy resolution walks up automatically:
        # step1_instance.step_materialization_config.well_filter
        # → None? Check step1_instance context
        # → step1_instance.well_filter_config.well_filter = ["A01"]
        # → Found!
```

**Key difference**: Sibling inheritance "just works" because both configs are part of the same `step1_instance` object in the context stack.

---

## Implementation Plan

Implement the tree model directly—no compatibility layer or staged cutover.

1. **Introduce the tree primitives**
    - Add `ConfigNode` plus `ConfigTreeRegistry` (singleton accessor via `instance()`).
    - Each `ParameterFormManager` constructs/registers its node on init and stores `self._config_node`.
    - Tree nodes keep weak refs back to live managers so they can expose user-edited values on demand.

2. **Replace context building**
    - Delete `context_layer_builders.py`; re‑implement `build_context_stack` as a thin wrapper that walks `ConfigNode.build_path_to_root()` and applies `config_context(...)` per ancestor.
    - Update `PlaceholderRefreshService` (and any other call sites) to use `self._config_node.build_context_stack()` plus explicit overlay application for user-modified fields.

3. **Wire cross-window behavior through the tree**
    - Remove `_active_form_managers`; `SignalConnectionService` and `ParameterFormManager` signal handlers look up affected nodes via the registry.
    - Tree traversal handles scope filtering and sibling notifications (plate node → child nodes, nested managers notified through their parent manager as today).

4. **Tidy the UI surface**
    - Keep `nested_managers` for widget orchestration, but ensure data flow uses the tree (parent manager updates node state instead of reconciling through builders).
    - Strip any dead helpers that only served the old layer stack (e.g., `_reconstruct_nested_dataclasses`).

5. **Backfill integrity checks**
    - Add sanity assertions to `ConfigTreeRegistry` (unique node IDs per scope, orphan detection) since we no longer rely on incremental migration safety nets.
    - Update documentation and diagrams to reflect the new single-tree model.

All changes land together so no legacy layer code remains on this branch.

## Benefits

### Code Simplification

| Aspect | Current | Proposed | Improvement |
|--------|---------|----------|-------------|
| Lines of code | 200+ (builders) | ~50 (tree) | 75% reduction |
| Concepts | 6 layer types | 1 tree structure | 6→1 |
| Context building | Builder dispatch | Tree walk | Direct |
| Sibling discovery | Query parent's `nested_managers` dict | Automatic (same object) | Implicit |

### Conceptual Clarity

**Before**: "We have 6 layers that apply in sequence, but actually one of them is a list of layers..."

**After**: "Walk up the tree from leaf to root, apply each node as a context."

### Maintainability

- **Adding new config types**: No builder classes needed
- **Debugging**: Visualize tree structure directly
- **Testing**: Mock tree nodes instead of complex manager setup

### Performance

- **Fewer queries**: No searching through `_active_form_managers`
- **Explicit relationships**: Parent/child links instead of scope filtering
- **Simpler stack building**: Direct path traversal

---

## Special Cases to Handle

### 1. Global Config Editing

When editing `GlobalPipelineConfig` directly, we want to show static defaults (not loaded values).

**Solution**:
```python
if editing_global_config:
    # Don't build tree-based stack
    # Instead, mask thread-local with fresh instance
    with config_context(GlobalPipelineConfig(), mask_with_none=True):
        # Show static defaults
```

### 2. Reset Behavior

When resetting a field, we want to use only user-modified values for sibling inheritance (not all values).

**Current**: `use_user_modified_only` flag in builders

**Proposed**: 
```python
def build_context_stack(self, use_user_modified_only: bool = False) -> ExitStack:
    stack = ExitStack()
    for node in self.build_path_to_root():
        if use_user_modified_only:
            instance = node.get_user_modified_instance()
        else:
            instance = node.object_instance
        stack.enter_context(config_context(instance))
    return stack
```

### 3. Cross-Window Live Values

When another window is editing the same config, we want to see their live values.

**Current**: Query `_active_form_managers` for same type, merge live values

**Proposed**: Query tree registry for same scope, get live values from tree node:
```python
def get_live_instance(self) -> Any:
    """Get instance with current live values from UI."""
    if self._form_manager:
        return self._form_manager.get_current_values_as_instance()
    return self.object_instance
```

### 4. Nested Manager UI

Nested managers (e.g., `well_filter_config` widget within `PipelineConfig` form) are **UI concerns**, not tree concerns.

**Keep**:
- `ParameterFormManager.nested_managers` dict (for UI)
- `parent_manager` reference (for UI hierarchy)

**Use tree for**:
- Context resolution
- Cross-window updates
- Value inheritance

---

## Testing Strategy

### Unit Tests

1. **Tree construction**:
   - Create Plate node → verify structure
   - Add Step node → verify parent/child links
   - Multiple plates → verify scope isolation

2. **Context building**:
   - Step node → stack should be [Plate, Step]
   - Plate node → stack should be [Plate]
   - Verify global is NOT in stack (thread-local)

3. **Resolution**:
   - Step inherits from Plate
   - Step's nested config inherits from sibling nested config
   - Plate inherits from thread-local Global

### Integration Tests

1. **Cross-window updates**:
   - Open Plate editor, change value
   - Open Step editor → verify it sees new value
   - Change in Step → verify Plate doesn't see it

2. **Scope isolation**:
   - Two Plate editors (different scopes)
   - Change in Plate1 → Plate2 unaffected
   - Change in Plate1 → Plate1's Steps see it

3. **Reset behavior**:
   - Set value in Plate → Step sees it
   - Set value in Step → overrides Plate
   - Reset in Step → reverts to Plate value

### Regression Tests

Run full existing test suite once the tree-backed resolution is in place.

---

## Open Questions

### 1. UI Parent vs Data Parent

Currently, `parent_manager` serves two purposes:
- UI hierarchy (who created this nested form?)
- Data inheritance (where do values come from?)

**Proposed split**:
```python
# ParameterFormManager
self._ui_parent_manager = parent_manager  # UI hierarchy
self._config_node.parent = data_parent     # Data hierarchy
```

Do we need this split, or can we derive data parent from UI parent?

### 2. Nested Manager Siblings

Within a form, nested managers need to see each other for sibling inheritance. Currently handled by `SiblingContextsBuilder`.

**With tree model**: Siblings are automatic (part of same object in context). But what about the **UI refresh**—when one nested manager changes, how do we notify its siblings?

**Option A**: Keep hub-and-spoke (child notifies parent, parent broadcasts to all children)
**Option B**: Direct sibling notification (but need to maintain sibling list)

### 3. Registry API Surface

Once `_active_form_managers` disappears, which helper methods should `ConfigTreeRegistry` expose so callers stay simple? Candidates include:
- `iter_scope(scope_id)`
- `get_live_node(node_id)`
- `broadcast(scope_id, event)`

Need to design these upfront since we are switching everything over in one shot.

### 4. Cross-Window Live Value Collection

How do we efficiently get live values from a tree node that has an open editor?

**Option A**: Store weak reference to `ParameterFormManager` in ConfigNode
**Option B**: Registry maps `node_id` → `ParameterFormManager`
**Option C**: Emit signals through tree structure

---

## Success Criteria

### Functional
- [ ] All existing tests pass
- [ ] Cross-window updates work correctly
- [ ] Sibling inheritance works
- [ ] Reset behavior unchanged
- [ ] Global editing shows static defaults

### Non-Functional
- [ ] <50 lines of code for context building (vs 200+)
- [ ] No performance regression (measure with existing benchmarks)
- [ ] Tree structure visualizable for debugging

### Code Quality
- [ ] No `_active_form_managers` global state (replaced with registry)
- [ ] No builder pattern boilerplate
- [ ] Clear separation: tree = data structure, managers = UI

---

## Timeline Estimate

| Task | Estimated Time | Risk |
|------|----------------|------|
| Implement tree primitives and registry | 2-3 days | Medium (new core objects) |
| Rip out context builders and rewire placeholder refresh | 3-4 days | Medium (touches hot path) |
| Replace cross-window plumbing with registry lookups | 2-3 days | Medium (signal choreography) |
| Cleanup + integrity guards + docs | 1-2 days | Low |
| **Total** | **8-12 days** | |

Additional time for:
- Comprehensive testing: +2-3 days
- Documentation updates: +1 day
- Code review and iteration: +2-3 days

**Total with buffer**: 13-18 days

---

## Conclusion

The current "layer" abstraction obscures a simple truth: configuration resolution is walking up a three-level tree (Global → Plate → Step). By making this explicit, we can:

1. **Reduce complexity**: 200+ lines → 50 lines
2. **Improve clarity**: One tree structure vs. six layer types
3. **Simplify maintenance**: No builder pattern boilerplate
4. **Enable debugging**: Visualize tree structure directly

The refactoring is low-risk because we can build the tree structure alongside the existing system, verify equivalence, then cut over.