"""
Context Tree Registry

Generic tree structure for managing configuration hierarchy (Global→Plate→Step).
Replaces hardcoded layer-based context builders with introspection-driven tree.

This module provides:
- ConfigNode: Generic tree node with parent/child links and weakref to form manager
- ConfigTreeRegistry: Singleton registry for node registration and discovery

The tree structure is depth-agnostic and uses type introspection instead of magic strings.
Tree provides structure (what/order), config_context() provides mechanics (lazy resolution).

Architecture:
- Similar to React Context API + Redux for state management
- Tree determines context stack order, existing config_context() handles resolution
- Weak references to form managers prevent memory leaks when forms close
"""

import weakref
from contextlib import ExitStack
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Type

from openhcs.config_framework.context_manager import config_context


@dataclass
class ConfigNode:
    """
    Generic tree node for configuration hierarchy.

    Depth-agnostic design - no hardcoded assumptions about tree levels.
    Works for any hierarchy: Global→Plate→Step or deeper structures.

    Attributes:
        node_id: Unique identifier for this node (e.g., "global", "plate_A", "plate_A.step_0")
        object_instance: The configuration object this node represents
        parent: Parent node (None for root)
        children: Child nodes (empty for leaves)
        _form_manager: Weak reference to ParameterFormManager (if form is open)

    Example tree structure:
        global (node_id="global")
        ├─ plate_A (node_id="plate_A")
        │   ├─ step_0 (node_id="plate_A.step_0")
        │   └─ step_1 (node_id="plate_A.step_1")
        └─ plate_B (node_id="plate_B")
            └─ step_0 (node_id="plate_B.step_0")
    """
    node_id: str
    object_instance: Any
    parent: Optional['ConfigNode'] = None
    children: List['ConfigNode'] = field(default_factory=list)
    _form_manager: Optional[weakref.ref] = None

    def ancestors(self) -> List['ConfigNode']:
        """
        Get all ancestor nodes from root to self (inclusive).

        Returns nodes in root→self order, suitable for building context stacks.

        Returns:
            List of nodes from root to self

        Example:
            For step_0 in plate_A:
            Returns: [global_node, plate_A_node, step_0_node]
        """
        path, cur = [], self
        while cur:
            path.append(cur)
            cur = cur.parent
        return list(reversed(path))

    def siblings(self) -> List['ConfigNode']:
        """
        Get sibling nodes (excludes self).

        Returns:
            List of sibling nodes (empty if no parent or no siblings)

        Example:
            For step_0 in plate_A with steps [step_0, step_1]:
            Returns: [step_1_node]
        """
        return [n for n in (self.parent.children if self.parent else []) if n != self]

    def descendants(self) -> List['ConfigNode']:
        """
        Get all descendant nodes (recursive).

        Returns nodes in depth-first order.

        Returns:
            List of all descendant nodes

        Example:
            For plate_A with steps [step_0, step_1]:
            Returns: [step_0_node, step_1_node]
        """
        result = []
        for child in self.children:
            result.append(child)
            result.extend(child.descendants())
        return result

    def _get_from_manager(self, method_name: str) -> Any:
        """
        Template method: get value from manager or fallback to object_instance.

        If a form is open for this node, delegates to the form manager method.
        Otherwise returns the static object_instance.

        Args:
            method_name: Method to call on form manager

        Returns:
            Result from form manager method, or object_instance if no form is open
        """
        if not self._form_manager:
            return self.object_instance
        manager = self._form_manager()
        return getattr(manager, method_name)() if manager else self.object_instance

    def get_live_instance(self) -> Any:
        """
        Get instance with current form values (if form is open).

        Returns live values from the form if open, otherwise returns static instance.
        This is used for placeholder resolution to show current form state.

        Returns:
            Instance with current form values or static instance
        """
        return self._get_from_manager('get_current_values_as_instance')

    def get_user_modified_instance(self) -> Any:
        """
        Get instance with only user-edited fields (for reset behavior).

        Returns instance containing only fields the user has explicitly edited.
        Used for reset button logic to preserve user edits while resetting defaults.

        Returns:
            Instance with only user-modified fields or static instance
        """
        return self._get_from_manager('get_user_modified_instance')

    def get_affected_nodes(self) -> List['ConfigNode']:
        """
        Get nodes that should be notified when this node changes.

        Implements cross-window update policy:
        - Root (Global): notify all descendants (plates and steps)
        - Plate: notify children (steps within this plate)
        - Step (or deeper): notify siblings (other steps in same plate)

        Returns:
            List of nodes that should refresh when this node changes
        """
        # Root of tree (Global): notify all descendants
        if self.parent is None:
            return self.descendants()

        # Plate (parent is Global): notify children (steps)
        if self.parent.parent is None:
            return self.children

        # Step (or deeper): notify siblings
        return self.siblings()

    def build_context_stack(self, use_user_modified_only: bool = False) -> ExitStack:
        """
        Build context stack by applying config_context() for each ancestor.

        Tree provides structure (what configs, in what order).
        config_context() provides mechanics (lazy resolution, context stacking).

        This replaces the manual context stacking logic in context_layer_builders.py.
        The tree automatically knows the correct order: root→leaf.

        Args:
            use_user_modified_only: If True, use only user-edited fields (for reset logic)

        Returns:
            ExitStack with all ancestor contexts entered

        Example:
            # Before (manual stacking):
            with config_context(global_config):
                with config_context(plate):
                    with config_context(step):
                        resolve_placeholders()

            # After (tree determines stack):
            with step_node.build_context_stack():
                resolve_placeholders()
        """
        stack = ExitStack()
        for node in self.ancestors():
            if use_user_modified_only:
                instance = node.get_user_modified_instance()
            else:
                instance = node.get_live_instance()
            stack.enter_context(config_context(instance))
        return stack


class ConfigTreeRegistry:
    """
    Singleton registry for configuration tree nodes.

    Manages the global tree structure and provides node discovery methods.
    Replaces _active_form_managers class variable with proper registry pattern.

    Design is depth-agnostic - no hardcoded assumptions about tree levels.
    Uses type introspection instead of magic strings for node discovery.

    Thread Safety:
        This singleton is NOT thread-safe. It assumes single-threaded GUI operation.
        If multi-threading is needed, add appropriate locking mechanisms.
    """
    _instance: Optional['ConfigTreeRegistry'] = None

    def __init__(self):
        """Initialize empty registry. Use instance() classmethod to get singleton."""
        self.trees: Dict[Optional[str], ConfigNode] = {}  # scope_id → root (None for Global)
        self.all_nodes: Dict[str, ConfigNode] = {}        # node_id → node

    @classmethod
    def instance(cls) -> 'ConfigTreeRegistry':
        """
        Get singleton instance of ConfigTreeRegistry.

        Creates instance on first call, returns same instance on subsequent calls.

        Returns:
            The singleton ConfigTreeRegistry instance
        """
        if not cls._instance:
            cls._instance = cls()
        return cls._instance

    @classmethod
    def reset(cls):
        """
        Reset singleton instance (primarily for testing).

        Creates a fresh registry instance, discarding all registered nodes.
        USE WITH CAUTION in production code.
        """
        cls._instance = cls()

    def register(
        self,
        node_id: str,
        obj: Any,
        parent: Optional[ConfigNode] = None
    ) -> ConfigNode:
        """
        Register a configuration node in the tree.

        Simplified signature - no redundant parameters.
        Scope is derived from parent chain, not passed separately.

        Args:
            node_id: Unique identifier for this node.
                     Convention:
                     - Global: "global"
                     - Plate: "plate_A", "plate_B", etc.
                     - Step: "{plate_node_id}.step_{index}" (e.g., "plate_A.step_0")
            obj: Configuration object instance (GlobalPipelineConfig, PipelineConfig, Step, etc.)
            parent: Parent ConfigNode object (None for root nodes)

        Returns:
            The created ConfigNode

        Example:
            # Register global node (root)
            global_node = registry.register("global", global_config)

            # Register plate node under global
            plate_node = registry.register("plate_A", plate_config, parent=global_node)

            # Register step node under plate
            step_node = registry.register("plate_A.step_0", step_instance, parent=plate_node)
        """
        # Derive scope_id from parent chain
        # Global has scope_id=None, everything under a plate shares that plate's scope
        if parent is None:
            # Root node (Global)
            scope_id = None
        elif parent.parent is None:
            # Direct child of Global (Plate) - scope_id is the node_id
            scope_id = node_id
        else:
            # Deeper node (Step or beyond) - inherit parent's scope_id
            scope_id = parent.scope_id if hasattr(parent, 'scope_id') else None

        # Create node
        node = ConfigNode(node_id, obj, parent)

        # Store scope_id on node for later use
        node.scope_id = scope_id

        # Register in all_nodes dict
        self.all_nodes[node_id] = node

        # If root node, add to trees dict
        if not parent:
            self.trees[scope_id] = node
        else:
            # Add as child of parent
            parent.children.append(node)

        return node

    def get_node(self, node_id: str) -> Optional[ConfigNode]:
        """
        Get node by ID.

        Args:
            node_id: Unique node identifier

        Returns:
            ConfigNode if found, None otherwise
        """
        return self.all_nodes.get(node_id)

    def get_scope_nodes(self, scope_id: Optional[str]) -> List[ConfigNode]:
        """
        Get all nodes in a scope (root + descendants).

        Args:
            scope_id: Scope identifier (None for Global, "plate_A" for plate A scope)

        Returns:
            List of nodes in scope (root + all descendants)
        """
        root = self.trees.get(scope_id)
        return [root] + root.descendants() if root else []

    def find_nodes_by_type(self, obj_type: Type) -> List[ConfigNode]:
        """
        Find all nodes holding instances of given type.

        Used for cross-scope updates (e.g., when Global changes, find all affected plates).

        Args:
            obj_type: Type to search for (e.g., GlobalPipelineConfig)

        Returns:
            List of nodes holding instances of obj_type
        """
        return [n for n in self.all_nodes.values() if isinstance(n.object_instance, obj_type)]

    def unregister(self, node_id: str):
        """
        Unregister a node and all its descendants (recursive removal).

        Automatically cleans up parent/child links and removes from trees dict if root.

        Args:
            node_id: Unique node identifier to remove
        """
        node = self.all_nodes.pop(node_id, None)
        if not node:
            return

        # Remove from trees dict if root
        if not node.parent:
            self.trees.pop(node.scope_id, None)
        else:
            # Remove from parent's children list
            node.parent.children.remove(node)

        # Recursively unregister all children
        for child in list(node.children):
            self.unregister(child.node_id)
