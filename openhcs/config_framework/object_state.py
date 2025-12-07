"""
ObjectState: Extracted MODEL from ParameterFormManager.

This class holds configuration state independently of UI widgets.
Lifecycle: Created when object added to pipeline, persists until removed.
PFM attaches to ObjectState when editor opens, detaches when closed.

ObjectStateRegistry: Singleton registry of all ObjectState instances.
Replaces LiveContextService._active_form_managers as the single source of truth.
"""
import dataclasses
from dataclasses import is_dataclass, fields as dataclass_fields
import logging
from typing import Any, Dict, List, Optional, TYPE_CHECKING
import copy

if TYPE_CHECKING:
    pass  # Forward references if needed

logger = logging.getLogger(__name__)


class ObjectStateRegistry:
    """Singleton registry of all ObjectState instances.

    Replaces LiveContextService._active_form_managers as the single source of truth
    for all configuration state. Keyed by scope_id for efficient lookup.

    Lifecycle ownership:
    - PipelineEditor: registers when step added, unregisters when step removed
    - ImageBrowser: registers when opened, unregisters when closed
    - Config window: registers PipelineConfig/GlobalPipelineConfig

    Thread safety: Not thread-safe (all operations expected on main thread).
    """
    _states: Dict[str, 'ObjectState'] = {}  # Keys are always strings (None normalized to "")

    @classmethod
    def _normalize_scope_id(cls, scope_id: Optional[str]) -> str:
        """Normalize scope_id: None and "" both represent global scope."""
        return scope_id if scope_id is not None else ""

    @classmethod
    def register(cls, state: 'ObjectState') -> None:
        """Register an ObjectState in the registry.

        Args:
            state: The ObjectState to register.
                   scope_id=None/"" for GlobalPipelineConfig (global scope).
                   scope_id=plate_path for PipelineConfig.
                   scope_id=plate_path::step_N for steps.
        """
        key = cls._normalize_scope_id(state.scope_id)

        if key in cls._states:
            logger.warning(f"Overwriting existing ObjectState for scope: {key}")

        cls._states[key] = state
        logger.debug(f"Registered ObjectState: scope={key}, type={type(state.object_instance).__name__}")

    @classmethod
    def unregister(cls, state: 'ObjectState') -> None:
        """Unregister an ObjectState from the registry.

        Args:
            state: The ObjectState to unregister.
        """
        key = cls._normalize_scope_id(state.scope_id)
        if key in cls._states:
            del cls._states[key]
            logger.debug(f"Unregistered ObjectState: scope={key}")

    @classmethod
    def get_by_scope(cls, scope_id: Optional[str]) -> Optional['ObjectState']:
        """Get ObjectState by scope_id.

        Args:
            scope_id: The scope identifier (e.g., "/path::step_0", or None/"" for global scope).

        Returns:
            ObjectState if found, None otherwise.
        """
        return cls._states.get(cls._normalize_scope_id(scope_id))

    @classmethod
    def get_all(cls) -> List['ObjectState']:
        """Get all registered ObjectStates.

        Returns:
            List of all ObjectState instances. Used by LiveContextService.collect().
        """
        return list(cls._states.values())

    @classmethod
    def clear(cls) -> None:
        """Clear all registered states. For testing only."""
        cls._states.clear()
        logger.debug("Cleared all ObjectStates from registry")

    # ========== TOKEN MANAGEMENT ==========
    # Delegate to LiveContextService - single source of truth for cache invalidation
    # Deferred imports required to avoid circular dependency (config_framework → pyqt_gui)

    @classmethod
    def get_token(cls) -> int:
        """Get current cache invalidation token from LiveContextService."""
        from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
        return LiveContextService.get_token()

    @classmethod
    def increment_token(cls, notify: bool = False) -> None:
        """Increment cache invalidation token.

        Args:
            notify: If True, notify listeners. Default False (caller handles notification).
        """
        from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
        LiveContextService.increment_token(notify=notify)




class ObjectState:
    """
    Extracted MODEL from ParameterFormManager - pure Python state without PyQt dependencies.

    Lifecycle:
    - Created when object added to pipeline (before any UI)
    - Persists until object removed from pipeline
    - PFM attaches to ObjectState when editor opens, detaches when closed

    Core Attributes (8 total):
    - object_instance: Backing object (updated on Save)
    - parameters: Mutable working copy (None = unset, value = user-set)
    - _saved_resolved: Resolved snapshot at save time
    - _live_resolved: Resolved snapshot using live hierarchy
    - _live_token: Token when _live_resolved was computed
    - nested_states: Recursive containment
    - _parent_state: Parent for context derivation
    - scope_id: Scope for registry lookup

    Everything else is derived:
    - context_obj → _parent_state.object_instance
    - is_dirty() → _saved_resolved != _live_resolved
    - user_set_fields → {k for k,v in parameters.items() if v is not None}
    """

    def __init__(
        self,
        object_instance: Any,
        scope_id: Optional[str] = None,
        parent_state: Optional['ObjectState'] = None,
        exclude_params: Optional[List[str]] = None,
        initial_values: Optional[Dict[str, Any]] = None,
    ):
        """
        Initialize ObjectState with minimal attributes.

        Args:
            object_instance: The object being edited (dataclass, callable, etc.)
            scope_id: Scope identifier for filtering (e.g., "/path::step_0")
            parent_state: Parent ObjectState for nested forms
            exclude_params: Parameters to exclude from extraction (e.g., ['func'] for FunctionStep)
            initial_values: Initial values to override extracted defaults (e.g., saved kwargs)
        """
        # === Core State (3 attributes) ===
        self.object_instance = object_instance
        # Use passed scope_id if provided, otherwise inherit from parent
        # FunctionPane passes explicit scope_id for functions (step_scope::function_N)
        # Nested dataclass configs may omit scope_id and inherit from parent
        self.scope_id = scope_id if scope_id is not None else (parent_state.scope_id if parent_state else None)

        # Extract parameters using UnifiedParameterAnalyzer
        # UnifiedParameterAnalyzer uses object.__getattribute__ to get raw values
        # (bypasses lazy resolution - returns None for unset lazy fields)
        from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer

        param_info_dict = UnifiedParameterAnalyzer.analyze(object_instance, exclude_params=exclude_params or [])
        self.parameters: Dict[str, Any] = {name: info.default_value for name, info in param_info_dict.items()}

        # Store signature defaults for reset (separate from current instance values)
        # Use use_signature_defaults=True to get CLASS defaults, not instance values
        signature_info = UnifiedParameterAnalyzer.analyze(object_instance, exclude_params=exclude_params or [], use_signature_defaults=True)
        self._signature_defaults: Dict[str, Any] = {name: info.default_value for name, info in signature_info.items()}

        # Apply initial_values overrides (e.g., saved kwargs for functions)
        if initial_values:
            self.parameters.update(initial_values)

        # === Structure (2 attributes) ===
        self._parent_state: Optional['ObjectState'] = parent_state
        self.nested_states: Dict[str, 'ObjectState'] = {}
        self._create_nested_states()

        # === Cache (2 attributes) ===
        self._live_resolved: Dict[str, Any] = {}
        self._live_token: int = -1  # Force recompute on first access

        # === Saved baseline (1 attribute) ===
        self._saved_resolved: Dict[str, Any] = {}

        # === Flags (kept for batch operations) ===
        self._in_reset = False
        self._block_cross_window_updates = False

        # Initialize baselines
        self._ensure_live_resolved()
        self._saved_resolved = copy.deepcopy(self._live_resolved)

    @property
    def context_obj(self) -> Optional[Any]:
        """Derive context_obj from parent_state (no separate attribute needed)."""
        return self._parent_state.object_instance if self._parent_state else None

    def _ensure_live_resolved(self) -> None:
        """Recompute _live_resolved if cache is stale."""
        token = ObjectStateRegistry.get_token()
        if self._live_token != token:
            self._live_resolved = self._compute_resolved_snapshot()
            self._live_token = token

    def _create_nested_states(self) -> None:
        """Recursively create nested ObjectStates for nested dataclass parameters.

        Uses UnifiedParameterAnalyzer to get param info - works for ANY object type.
        """
        from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer

        param_info_dict = UnifiedParameterAnalyzer.analyze(self.object_instance)

        for param_name, info in param_info_dict.items():
            if param_name not in self.parameters:
                continue

            # Detect nested dataclass type
            nested_type = self._get_nested_dataclass_type(info.param_type)
            if nested_type is None:
                continue

            # Get current value for this parameter
            current_value = self.parameters.get(param_name)

            # Determine object instance for nested state
            if current_value is not None:
                # If current_value is a dict (saved config), convert to dataclass
                if isinstance(current_value, dict) and is_dataclass(nested_type):
                    nested_instance = nested_type(**current_value)
                else:
                    nested_instance = current_value
            else:
                # Create default instance
                nested_instance = nested_type() if is_dataclass(nested_type) else nested_type

            # Create nested ObjectState (recursive)
            # Nested states inherit parent's scope_id for proper live context collection
            nested_state = ObjectState(
                object_instance=nested_instance,
                scope_id=self.scope_id,  # Inherit parent's scope_id
                parent_state=self,
            )
            self.nested_states[param_name] = nested_state

    def _get_nested_dataclass_type(self, param_type: Any) -> Optional[type]:
        """Get the nested dataclass type if param_type is a nested dataclass.

        Args:
            param_type: The parameter type to check

        Returns:
            The dataclass type if nested, None otherwise
        """
        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils

        # Check Optional[dataclass]
        if ParameterTypeUtils.is_optional_dataclass(param_type):
            return ParameterTypeUtils.get_optional_inner_type(param_type)

        # Check direct dataclass (but not the type itself)
        if is_dataclass(param_type) and not isinstance(param_type, type):
            # param_type is an instance, not a type - shouldn't happen but handle it
            return type(param_type)

        if is_dataclass(param_type):
            return param_type

        return None

    def reset_all_parameters(self) -> None:
        """Reset all parameters to defaults."""
        self._in_reset = True
        try:
            for param_name in list(self.parameters.keys()):
                self.reset_parameter(param_name)
        finally:
            self._in_reset = False

    def update_parameter(self, param_name: str, value: Any) -> None:
        """Update parameter value in state.

        Enforces invariant: state mutation → global cache invalidation.
        Controllers don't need to remember to invalidate - ObjectState handles it.

        Args:
            param_name: Name of parameter to update
            value: New value
        """
        if param_name not in self.parameters:
            return

        # Update state directly (no type conversion - that's VIEW responsibility)
        self.parameters[param_name] = value

        # Invalidate local cache (will be recomputed on next access)
        self._live_token = -1

        # Enforce invariant: state mutation → global cache invalidation
        # This ensures all other ObjectStates know to recompute their resolved values
        # notify=False: Controller handles when/how to trigger UI refresh
        ObjectStateRegistry.increment_token(notify=False)

    def get_resolved_value(self, param_name: str) -> Any:
        """Get resolved value for a field from the bulk snapshot.

        Args:
            param_name: Field name to resolve

        Returns:
            Resolved value from _live_resolved snapshot
        """
        self._ensure_live_resolved()
        return self._live_resolved.get(param_name)

    def _resolve_value(self, param_name: str) -> Any:
        """Internal resolver - builds context stack and resolves raw value.

        Args:
            param_name: Field name to resolve

        Returns:
            Raw resolved value
        """
        from openhcs.config_framework.context_manager import build_context_stack
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
        from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService

        # Collect live values via LiveContextService (single source of truth)
        snapshot = LiveContextService.collect()
        live_values = LiveContextService.merge_ancestor_values(
            snapshot.scopes,
            self.scope_id
        )

        # Build context stack
        stack = build_context_stack(
            context_obj=self.context_obj,
            object_instance=self.object_instance,
            live_values=live_values,
        )

        with stack:
            obj_type = type(self.object_instance)
            try:
                instance = obj_type()
                return getattr(instance, param_name)
            except Exception:
                # Fallback to class default
                return LazyDefaultPlaceholderService._get_class_default_value(obj_type, param_name)

    def invalidate_cache(self) -> None:
        """Invalidate resolved cache by resetting token."""
        self._live_token = -1

    def reset_parameter(self, param_name: str) -> None:
        """Reset parameter to signature default (None for lazy dataclasses)."""
        if param_name not in self.parameters:
            return

        # Use signature defaults (CLASS defaults), not instance values
        # This ensures reset goes back to None for lazy fields, not saved concrete values
        default_value = self._signature_defaults.get(param_name)
        self.parameters[param_name] = default_value
        self._live_token = -1  # Invalidate cache



    def get_current_values(self) -> Dict[str, Any]:
        """
        Get current parameter values from state.

        For ObjectState, this reads directly from self.parameters.
        PFM overrides this to also read from widgets.

        For nested configs, returns reconstructed dataclass instances (not stale instances
        from self.parameters) so that None values in nested_state.parameters are preserved.
        """
        current_values = dict(self.parameters)

        # Replace nested values with properly reconstructed dataclass instances
        for name, nested_state in self.nested_states.items():
            nested_vals = nested_state.get_current_values()
            # Get the nested type from the original instance
            original_instance = self.parameters.get(name)
            if original_instance is not None and is_dataclass(original_instance):
                # Filter to non-None values to preserve lazy resolution
                filtered_vals = {k: v for k, v in nested_vals.items() if v is not None}
                # Reconstruct dataclass with current values
                nested_type = type(original_instance)
                current_values[name] = nested_type(**filtered_vals) if filtered_vals else nested_type()
            else:
                # Fallback to dict if no original instance
                current_values[name] = nested_vals

        return current_values



    # ==================== SAVED STATE / DIRTY TRACKING ====================

    def _compute_resolved_snapshot(self) -> Dict[str, Any]:
        """Resolve all fields for this state and nested states into a snapshot dict."""
        snapshot: Dict[str, Any] = {}
        for name in self.parameters.keys():
            snapshot[name] = self._resolve_value(name)

        for nested_name, nested_state in self.nested_states.items():
            snapshot[nested_name] = nested_state._compute_resolved_snapshot()

        return snapshot

    def mark_saved(self) -> None:
        """Mark current state as saved baseline.

        CRITICAL: Save nested states FIRST, then collect their updated object_instance values.
        """
        # Save nested states first (they update their object_instance)
        for nested_state in self.nested_states.values():
            nested_state.mark_saved()

        # Now update our object_instance with current parameters
        if is_dataclass(self.object_instance) and not isinstance(self.object_instance, type):
            current_values = self.get_current_values()
            self.object_instance = dataclasses.replace(self.object_instance, **current_values)

        # Capture resolved snapshot as baseline
        self._ensure_live_resolved()
        self._saved_resolved = copy.deepcopy(self._live_resolved)

    def restore_saved(self) -> None:
        """Restore parameters to the last saved baseline (from object_instance)."""
        # Restore nested states first
        for nested_state in self.nested_states.values():
            nested_state.restore_saved()

        # Restore parameters from object_instance (the saved baseline)
        if is_dataclass(self.object_instance) and not isinstance(self.object_instance, type):
            for field in dataclass_fields(self.object_instance):
                if field.name in self.parameters:
                    self.parameters[field.name] = object.__getattribute__(self.object_instance, field.name)

        self.invalidate_cache()

    def is_dirty(self) -> bool:
        """Return True if resolved state differs from saved baseline."""
        self._ensure_live_resolved()
        return self._live_resolved != self._saved_resolved

    def should_skip_updates(self) -> bool:
        """Check if updates should be skipped due to batch operations."""
        if self._in_reset or self._block_cross_window_updates:
            return True
        for nested_state in self.nested_states.values():
            if nested_state._in_reset or nested_state._block_cross_window_updates:
                return True
        return False

    def update_thread_local_global_config(self):
        """Update thread-local GlobalPipelineConfig with current form values.

        LIVE UPDATES ARCHITECTURE:
        Called on every parameter change when editing GlobalPipelineConfig.
        Updates thread-local storage so other windows see changes immediately.
        Original config is stored by ConfigWindow and restored on Cancel.
        """
        import dataclasses
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.config_framework.global_config import set_global_config_for_editing
        from openhcs.config_framework.context_manager import get_base_global_config
        from openhcs.pyqt_gui.widgets.shared.services.value_collection_service import ValueCollectionService

        current_values = self.get_current_values()
        base_config = get_base_global_config()
        reconstructed_values = ValueCollectionService.reconstruct_nested_dataclasses(current_values)

        try:
            new_config = dataclasses.replace(base_config, **reconstructed_values)
            set_global_config_for_editing(GlobalPipelineConfig, new_config)
            logger.debug(f"🔍 LIVE_UPDATES: Updated thread-local GlobalPipelineConfig")
        except Exception as e:
            logger.warning(f"🔍 LIVE_UPDATES: Failed to update thread-local GlobalPipelineConfig: {e}")
