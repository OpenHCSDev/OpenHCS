# Context Tree Refactoring

## Problem

`context_layer_builders.py` (200+ lines) obscures tree structure (Global→Plate→Step). Magic strings, global `_active_form_managers`.

## Solution

Generic tree. Node discovery via type introspection. No hardcoded levels.

## Design

### ConfigNode (Generic)

```python
@dataclass
class ConfigNode:
    """Generic tree node. Depth-agnostic."""
    node_id: str
    object_instance: Any
    parent: Optional['ConfigNode'] = None
    children: List['ConfigNode'] = field(default_factory=list)
    _form_manager: Optional[weakref.ref] = None
    # scope_id derived from parent chain, stored on node after creation
    
    def ancestors(self) -> List['ConfigNode']:
        """Root → self."""
        path, cur = [], self
        while cur:
            path.append(cur)
            cur = cur.parent
        return list(reversed(path))
    
    def siblings(self) -> List['ConfigNode']:
        """Siblings exclude self."""
        return [n for n in (self.parent.children if self.parent else []) if n != self]
    
    def descendants(self) -> List['ConfigNode']:
        """Recursive descent."""
        result = []
        for child in self.children:
            result.append(child)
            result.extend(child.descendants())
        return result
    
    def _get_from_manager(self, method_name: str) -> Any:
        """Template method: get value from manager or fallback to object_instance."""
        if not self._form_manager:
            return self.object_instance
        manager = self._form_manager()
        return getattr(manager, method_name)() if manager else self.object_instance
    
    def get_live_instance(self) -> Any:
        """Get instance with current form values (if form is open)."""
        return self._get_from_manager('get_current_values_as_instance')
    
    def get_user_modified_instance(self) -> Any:
        """Get instance with only user-edited fields (for reset behavior)."""
        return self._get_from_manager('get_user_modified_instance')
    
    def get_affected_nodes(self) -> List['ConfigNode']:
        """Get nodes that should be notified when this node changes."""
        # Root of tree (Global): notify all descendants
        if self.parent is None:
            return self.descendants()

        # Plate: notify children (steps)
        if self.parent.parent is None:
            return self.children

        # Step (or deeper): notify siblings
        return self.siblings()

    def build_context_stack(self, use_user_modified_only: bool = False) -> ExitStack:
        """Apply config_context() for each ancestor. Tree provides structure, config_context() provides mechanics."""
        stack = ExitStack()
        for node in self.ancestors():
            if use_user_modified_only:
                instance = node.get_user_modified_instance()
            else:
                instance = node.get_live_instance()
            stack.enter_context(config_context(instance))
        return stack
```

### ConfigTreeRegistry (Singleton)

```python
class ConfigTreeRegistry:
    """Singleton registry. Depth-agnostic."""
    _instance = None
    
    def __init__(self):
        self.trees: Dict[Optional[str], ConfigNode] = {}  # scope_id → root (None for Global)
        self.all_nodes: Dict[str, ConfigNode] = {}        # node_id → node

    @classmethod
    def instance(cls):
        if not cls._instance:
            cls._instance = cls()
        return cls._instance

    def register(self, node_id: str, obj: Any, parent: Optional[ConfigNode] = None) -> ConfigNode:
        """
        Generic registration. Simplified signature - no redundant parameters.

        Args:
            node_id: Unique ID constructed by caller.
                     Convention:
                     - Global: "global"
                     - Plate: "plate_A", "plate_B", etc.
                     - Step: "{plate_node_id}.step_{index}" (e.g., "plate_A.step_0")
            obj: Configuration object (GlobalPipelineConfig, PipelineConfig, Step, etc.)
            parent: Parent ConfigNode object (None for root)

        Returns:
            The created ConfigNode

        Note:
            scope_id is derived from parent chain:
            - Global: scope_id = None
            - Plate: scope_id = node_id
            - Step: scope_id = parent.scope_id
        """
        # Derive scope_id from parent chain
        if parent is None:
            scope_id = None  # Global
        elif parent.parent is None:
            scope_id = node_id  # Plate (direct child of Global)
        else:
            scope_id = parent.scope_id  # Step or deeper (inherit)

        # Create and register node
        node = ConfigNode(node_id, obj, parent)
        node.scope_id = scope_id
        self.all_nodes[node_id] = node

        if not parent:
            self.trees[scope_id] = node
        else:
            parent.children.append(node)

        return node
    
    def get_node(self, node_id: str) -> Optional[ConfigNode]:
        """Get node by ID."""
        return self.all_nodes.get(node_id)
    
    def get_scope_nodes(self, scope_id: Optional[str]) -> List[ConfigNode]:
        """Root + descendants."""
        root = self.trees.get(scope_id)
        return [root] + root.descendants() if root else []
    
    def find_nodes_by_type(self, obj_type: Type) -> List[ConfigNode]:
        """Find all nodes holding instances of given type (for cross-scope updates)."""
        return [n for n in self.all_nodes.values() if isinstance(n.object_instance, obj_type)]
    
    def unregister(self, node_id: str):
        """Recursive removal."""
        node = self.all_nodes.pop(node_id, None)
        if not node:
            return
        if not node.parent:
            self.trees.pop(node.scope_id, None)
        else:
            node.parent.children.remove(node)
        for child in list(node.children):
            self.unregister(child.node_id)
```

### Integration with config_context()

Tree provides structure (what/order), `config_context()` provides mechanics (lazy resolution, context stacking).

```python
# Before: Manual stacking
with config_context(plate):
    with config_context(step):
        resolve_placeholders()

# After: Tree determines stack
with step_node.build_context_stack():
    resolve_placeholders()
```

Sibling inheritance automatic: both `step_materialization_config` and `well_filter_config` are fields on same `step_instance` object.

### Tree Structure

```
global (node_id="global", scope_id=None)
├─ plate_A (node_id="plate_A", scope_id="plate_A")
│   ├─ step_0 (node_id="plate_A.step_0", scope_id="plate_A")
│   └─ step_1 (node_id="plate_A.step_1", scope_id="plate_A")
└─ plate_B (node_id="plate_B", scope_id="plate_B")
    └─ step_0 (node_id="plate_B.step_0", scope_id="plate_B")
```

Note: Step node_id uses position index (e.g., "step_0", "step_1") rather than step name.
This handles duplicate names and step reordering (re-register nodes with updated indices).

### Cross-Window Notification

```python
# When a node changes, notify affected nodes:
def _emit_cross_window_change(self, param_name, value):
    affected = self._config_node.get_affected_nodes()
    for node in affected:
        manager = node._form_manager() if node._form_manager else None
        if manager:
            manager.refresh_placeholders()

# Or keep Qt signals and use registry for discovery:
def _emit_cross_window_change(self, param_name, value):
    affected = self._config_node.get_affected_nodes()
    for node in affected:
        manager = node._form_manager() if node._form_manager else None
        if manager:
            self.context_value_changed.emit(param_name, value, self.object_instance, self.context_obj)
```

## Implementation

1. **Add tree primitives**: `ConfigNode`, `ConfigTreeRegistry` in `openhcs/config_framework/config_tree_registry.py` ✅
2. **Ensure Global node**: Create singleton Global node on app startup or first GlobalPipelineConfig edit
3. **Wire to ParameterFormManager**: Store `self._config_node`, register on init
   - Global editor: `parent=None` (root of tree)
   - Plate editor: `parent=global_node`
   - Step editor: `parent=plate_node`, `node_id=f"{plate_node_id}.step_{index}"`
4. **Update StepParameterEditorWidget**: Pass unique `field_id` based on step position index
5. **Delete context_layer_builders.py**: Replace with `node.build_context_stack()`
6. **Remove _active_form_managers**: Use `registry.find_nodes_by_type()` or `node.get_affected_nodes()`
7. **Keep nested_managers**: UI orchestration only, tree handles data flow

## Special Cases

- **Global editing**: Mask thread-local with fresh `GlobalPipelineConfig()`
- **Reset**: Pass `use_user_modified_only=True` to `build_context_stack()`
- **Nested UI**: Keep `nested_managers` dict, tree handles inheritance

## Testing

- Tree construction (parent/child links, scope isolation)
- Context stacks correct (root→leaf order)
- Cross-window updates (change propagation, scope filtering)
- Regression suite with tree-backed resolution