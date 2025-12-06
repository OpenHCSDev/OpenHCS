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
from typing import Any, Dict, List, Optional, Set, Callable, TYPE_CHECKING
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
    _states: Dict[Optional[str], 'ObjectState'] = {}

    @classmethod
    def register(cls, state: 'ObjectState') -> None:
        """Register an ObjectState in the registry.

        Args:
            state: The ObjectState to register.
                   scope_id=None is valid for GlobalPipelineConfig (global scope).
                   scope_id=plate_path for PipelineConfig.
                   scope_id=plate_path::step_N for steps.
        """
        # Use scope_id as key (None is valid for global scope)

        if state.scope_id in cls._states:
            logger.warning(f"Overwriting existing ObjectState for scope: {state.scope_id}")

        cls._states[state.scope_id] = state
        logger.debug(f"Registered ObjectState: scope={state.scope_id}, field_id={state.field_id}")

    @classmethod
    def unregister(cls, state: 'ObjectState') -> None:
        """Unregister an ObjectState from the registry.

        Args:
            state: The ObjectState to unregister.
        """
        # scope_id can be None (global scope) - use 'in' check directly
        if state.scope_id in cls._states:
            del cls._states[state.scope_id]
            logger.debug(f"Unregistered ObjectState: scope={state.scope_id}")

    @classmethod
    def get_by_scope(cls, scope_id: Optional[str]) -> Optional['ObjectState']:
        """Get ObjectState by scope_id.

        Args:
            scope_id: The scope identifier (e.g., "/path::step_0", or None for global scope).

        Returns:
            ObjectState if found, None otherwise.
        """
        return cls._states.get(scope_id)

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

    @classmethod
    def get_token(cls) -> int:
        """Get current cache invalidation token from LiveContextService."""
        from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
        return LiveContextService.get_token()




class ObjectState:
    """
    Extracted MODEL from ParameterFormManager - pure Python state without PyQt dependencies.

    Lifecycle:
    - Created when object added to pipeline (before any UI)
    - Persists until object removed from pipeline
    - PFM attaches to ObjectState when editor opens, detaches when closed

    Responsibilities:
    - Store parameter values (self.parameters)
    - Track user modifications (self._user_set_fields)
    - Manage nested states (self.nested_states)
    - Provide scope_id for filtering
    """

    def __init__(
        self,
        object_instance: Any,
        field_id: str,
        scope_id: Optional[str] = None,
        context_obj: Optional[Any] = None,
        parent_state: Optional['ObjectState'] = None,
        exclude_params: Optional[List[str]] = None,
        initial_values: Optional[Dict[str, Any]] = None,
    ):
        """
        Initialize ObjectState with extracted MODEL from ParameterFormManager.

        Args:
            object_instance: The object being edited (dataclass, callable, etc.)
            field_id: Unique identifier for this state
            scope_id: Scope identifier for filtering (e.g., "/path::step_0")
            context_obj: Parent object for inheritance resolution
            parent_state: Parent ObjectState for nested forms
            exclude_params: Parameters to exclude from extraction (e.g., ['func'] for FunctionStep)
            initial_values: Initial values to override extracted defaults (e.g., saved kwargs)
        """
        # Core identity
        self.object_instance = object_instance
        self.field_id = field_id
        self.scope_id = parent_state.scope_id if parent_state else scope_id
        self.context_obj = context_obj
        self._parent_state: Optional['ObjectState'] = parent_state

        # Extract parameters using UnifiedParameterAnalyzer (handles dataclasses, callables, etc.)
        # Lazy import to avoid circular dependency
        from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer
        from openhcs.introspection.signature_analyzer import SignatureAnalyzer

        self.parameters: Dict[str, Any] = {}
        self.parameter_types: Dict[str, Any] = {}  # Can be Type or str (forward ref)
        self.param_defaults: Dict[str, Any] = {}

        param_info_dict = UnifiedParameterAnalyzer.analyze(object_instance, exclude_params=exclude_params or [])
        for name, info in param_info_dict.items():
            self.parameters[name] = info.default_value
            self.parameter_types[name] = info.param_type

        # param_defaults = SIGNATURE defaults (analyze TYPE, not instance)
        sig_info = SignatureAnalyzer.analyze(type(object_instance))
        for name in self.parameters:
            if name in sig_info:
                self.param_defaults[name] = sig_info[name].default_value

        # Apply initial_values overrides (e.g., saved kwargs for functions)
        if initial_values:
            self.parameters.update(initial_values)

        # Tracking
        self._user_set_fields: Set[str] = set()
        self.reset_fields: Set[str] = set()

        # Load user-set fields from object if present
        if hasattr(object_instance, '_explicitly_set_fields'):
            explicitly_set = getattr(object_instance, '_explicitly_set_fields')
            if isinstance(explicitly_set, set):
                self._user_set_fields = explicitly_set.copy()

        # Nested states (for nested dataclasses) - recursively created
        self.nested_states: Dict[str, 'ObjectState'] = {}
        self._create_nested_states()

        # Resolved value cache with token-based invalidation
        # Key: field_name, Value: (token, resolved_value)
        # Token is from ObjectStateRegistry - when it changes, cache is stale
        self._resolved_cache: Dict[str, tuple] = {}
        # Live-context overlay cache (token -> reconstructed overlay with nested dataclasses)
        self._overlay_cache: tuple[int | None, Dict[str, Any]] = (None, {})
        # Saved state baselines
        self.saved_parameters: Dict[str, Any] = self._snapshot_object_instance()
        self.saved_resolved_state: Dict[str, Any] = {}
        self.saved_user_set_fields: Set[str] = set(self._user_set_fields)
        self.saved_reset_fields: Set[str] = set(self.reset_fields)
        self._dirty = False

        # Flags
        self._in_reset = False
        self._block_cross_window_updates = False

        # Initialize saved_resolved_state baseline
        self.saved_resolved_state = self._compute_resolved_snapshot()

    def _create_nested_states(self) -> None:
        """Recursively create nested ObjectStates for nested dataclass parameters.

        This is a MODEL concern - ObjectState manages its own nested structure.
        PFM just traverses nested_states to create VIEW components.
        """
        for param_name, param_type in self.parameter_types.items():
            # Detect nested dataclass (direct or Optional[dataclass])
            nested_type = self._get_nested_dataclass_type(param_type)
            if nested_type is None:
                continue

            # Get current value for this parameter
            current_value = self.parameters.get(param_name)

            # Determine object instance for nested state
            if current_value is not None:
                # If current_value is a dict (saved config), convert to dataclass
                if isinstance(current_value, dict) and is_dataclass(nested_type):
                    object_instance = nested_type(**current_value)
                else:
                    object_instance = current_value
            else:
                # Create default instance
                object_instance = nested_type() if is_dataclass(nested_type) else nested_type

            # Create nested ObjectState (recursive - it will create its own nested states)
            # Nested states inherit parent's scope_id for proper live context collection
            nested_state = ObjectState(
                object_instance=object_instance,
                field_id=f"{self.field_id}.{param_name}",
                scope_id=self.scope_id,  # Inherit parent's scope_id
                # CRITICAL: use the parent object as context so nested lazy fields
                # see the immediate container (e.g., FunctionStep) during resolution
                context_obj=self.object_instance,
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

    def update_parameter(self, param_name: str, value: Any, user_set: bool = True) -> None:
        """Update parameter value in state.

        Args:
            param_name: Name of parameter to update
            value: New value
            user_set: If True, mark as user-modified (default). If False, don't track as user edit.
        """
        if param_name not in self.parameters:
            return

        # Capture baseline resolved state on first mutation to support cancel/dirty tracking
        if not self._dirty:
            self.saved_resolved_state = self._compute_resolved_snapshot()
            self._dirty = True

        # Update state directly (no type conversion - that's VIEW responsibility)
        self.parameters[param_name] = value

        # Invalidate cache for this field (resolved value may change)
        self._resolved_cache.pop(param_name, None)

        # Track user modification
        if user_set:
            self._user_set_fields.add(param_name)

    def get_resolved_value(self, param_name: str) -> Any:
        """Get raw resolved value for a field, using cache if valid.

        This is the MODEL's responsibility - ObjectState owns resolution logic.
        Uses ObjectStateRegistry for sibling values and builds context stack.

        Args:
            param_name: Field name to resolve

        Returns:
            Raw resolved value (e.g., '/some/path'), not formatted text
        """
        # Get current token for cache validation
        token = ObjectStateRegistry.get_token()
        logger.info(f"🔬 RESET_TRACE: get_resolved_value({param_name}) token={token}")
        logger.info(f"🔬 RESET_TRACE: _user_set_fields={self._user_set_fields}")

        # Check cache validity
        if param_name in self._resolved_cache:
            cached_token, cached_value = self._resolved_cache[param_name]
            logger.info(f"🔬 RESET_TRACE: cache entry exists: cached_token={cached_token}, cached_value={repr(cached_value)[:50]}")
            if cached_token == token:
                logger.info(f"🔬 RESET_TRACE: CACHE HIT - returning cached value")
                return cached_value
            else:
                logger.info(f"🔬 RESET_TRACE: CACHE STALE - token mismatch")
        else:
            logger.info(f"🔬 RESET_TRACE: CACHE MISS - no entry for {param_name}")

        # Cache miss or stale - resolve and cache
        logger.info(f"🔬 RESET_TRACE: Calling _resolve_value...")
        resolved = self._resolve_value(param_name)
        self._resolved_cache[param_name] = (token, resolved)
        logger.info(f"🔬 RESET_TRACE: Cached resolved={repr(resolved)[:50]} with token={token}")
        return resolved

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



        logger.info(f"� RESET_TRACE: _resolve_value: {self.field_id}.{param_name} (scope={self.scope_id})")
        logger.info(f"🔬 RESET_TRACE: _user_set_fields={self._user_set_fields}")

        # Collect live values via LiveContextService (single source of truth)
        logger.info(f"🔬 RESET_TRACE: Calling LiveContextService.collect()...")
        snapshot = LiveContextService.collect()
        logger.info(f"🔬 RESET_TRACE: snapshot.token={snapshot.token}, scopes={list(snapshot.scopes.keys())}")

        live_values = LiveContextService.merge_ancestor_values(
            snapshot.scopes,
            self.scope_id
        )
        logger.info(f"� RESET_TRACE: live_values after merge: {len(live_values)} types")
        for obj_type, values in live_values.items():
            logger.info(f"🔬 RESET_TRACE:   {obj_type.__name__}: {list(values.keys())} = {values}")

        # Build context stack
        stack = build_context_stack(
            context_obj=self.context_obj,
            object_instance=self.object_instance,
            live_values=live_values,
        )
        logger.info(f"🔍 Built context stack with context_obj={type(self.context_obj).__name__ if self.context_obj else None}")

        with stack:
            # Concrete classes now have __getattribute__ via bind_lazy_resolution_to_class()
            # No need to lookup lazy type - just use the concrete type directly
            obj_type = type(self.object_instance)

            # Create instance and get raw resolved value
            try:
                instance = obj_type()
                resolved = getattr(instance, param_name)
                logger.info(f"🔍 Resolved {obj_type.__name__}.{param_name} = {repr(resolved)[:50]}")
                return resolved
            except Exception as e:
                logger.debug(f"Failed to resolve {obj_type.__name__}.{param_name}: {e}")
                # Fallback to class default
                fallback = LazyDefaultPlaceholderService._get_class_default_value(obj_type, param_name)
                logger.info(f"🔍 Fallback to class default: {repr(fallback)[:50]}")
                return fallback

    def invalidate_cache(self, param_name: Optional[str] = None) -> None:
        """Invalidate resolved cache.

        Args:
            param_name: If provided, invalidate only this field. Otherwise invalidate all.
        """
        if param_name:
            self._resolved_cache.pop(param_name, None)
        else:
            self._resolved_cache.clear()

    def reset_parameter(self, param_name: str) -> None:
        """Reset parameter to signature default."""
        if param_name not in self.parameters:
            return

        # Reset to default value
        default_value = self.param_defaults.get(param_name)
        self.parameters[param_name] = default_value

        # Remove from user-set tracking
        self._user_set_fields.discard(param_name)
        self.reset_fields.add(param_name)



    def get_current_values(self) -> Dict[str, Any]:
        """
        Get current parameter values from state.

        For ObjectState, this reads directly from self.parameters.
        PFM overrides this to also read from widgets.
        """
        current_values = dict(self.parameters)

        # Include nested state values
        for name, nested_state in self.nested_states.items():
            current_values[name] = nested_state.get_current_values()

        return current_values

    def get_user_modified_values(self) -> Dict[str, Any]:
        """
        Get only values that were explicitly set by the user.

        For lazy dataclasses, this preserves lazy resolution for unmodified fields
        by only returning fields that are in self._user_set_fields (tracked when user edits widgets).

        For nested dataclasses, only include them if they have user-modified fields inside.

        CRITICAL: This method uses self._user_set_fields to distinguish between:
        1. Values that were explicitly set by the user (in _user_set_fields)
        2. Values that were inherited from parent or set during initialization (not in _user_set_fields)
        """
        # ANTI-DUCK-TYPING: Use isinstance check against LazyDataclass base class
        # Lazy import to avoid circular dependency
        from openhcs.config_framework.lazy_factory import is_lazy_dataclass
        is_lazy = is_lazy_dataclass(self.object_instance)
        logger.info(f"🔍 GET_USER_MODIFIED: {self.field_id} is_lazy={is_lazy}, type={type(self.object_instance).__name__}")

        if not is_lazy:
            # For non-lazy dataclasses, return all current values
            result = self.get_current_values()
            logger.info(f"🔍 GET_USER_MODIFIED: {self.field_id} returning ALL values: {list(result.keys())}")
            return result

        # PERFORMANCE OPTIMIZATION: Only read values for user-set fields
        # Instead of calling get_current_values() which reads ALL widgets,
        # we only need values for fields in _user_set_fields
        user_modified = {}

        # Fast path: if no user-set fields, return empty dict
        if not self._user_set_fields:
            return user_modified

        # DEBUG: Log what fields are tracked as user-set
        logger.info(f"🔍 GET_USER_MODIFIED: {self.field_id} - _user_set_fields = {self._user_set_fields}")

        # Only include fields that were explicitly set by the user
        # PERFORMANCE: Read directly from self.parameters instead of calling get_current_values()
        for field_name in self._user_set_fields:
            # For user-set fields, self.parameters is always the source of truth
            # (updated by FieldChangeDispatcher before any refresh happens)
            value = self.parameters.get(field_name)

            # CRITICAL FIX: Include None values for user-set fields
            # When user clears a field (backspace/delete), the None value must propagate
            # to live context so other windows can update their placeholders
            if value is not None:
                # CRITICAL: For nested dataclasses, we need to extract only user-modified fields
                # by recursively calling get_user_modified_values() on the nested manager
                if is_dataclass(value) and not isinstance(value, type):
                    # Check if there's a nested manager for this field
                    nested_state = self.nested_states.get(field_name)
                    if nested_state and hasattr(nested_state, 'get_user_modified_values'):
                        # Recursively get user-modified values from nested manager
                        nested_user_modified = nested_state.get_user_modified_values()

                        if nested_user_modified:
                            # Reconstruct nested dataclass instance from user-modified values
                            user_modified[field_name] = type(value)(**nested_user_modified)
                    else:
                        # No nested manager, extract raw field values from nested dataclass
                        nested_user_modified = {}
                        for field in dataclass_fields(value):
                            raw_value = object.__getattribute__(value, field.name)
                            if raw_value is not None:
                                nested_user_modified[field.name] = raw_value

                        # Only include if nested dataclass has user-modified fields
                        if nested_user_modified:
                            user_modified[field_name] = type(value)(**nested_user_modified)
                else:
                    # Non-dataclass field, include if user set it
                    user_modified[field_name] = value
            else:
                # User explicitly set this field to None (cleared it)
                # Include it so live context updates propagate to other windows
                user_modified[field_name] = None

        # Also include nested manager edits even if parent field not in _user_set_fields
        # This ensures nested edits are captured without requiring the parent to track them
        for field_name, nested_state in self.nested_states.items():
            if field_name not in user_modified:  # Not already included from _user_set_fields
                nested_values = nested_state.get_user_modified_values()
                if nested_values and nested_state.object_instance:
                    try:
                        user_modified[field_name] = type(nested_state.object_instance)(**nested_values)
                    except Exception:
                        pass  # Skip if reconstruction fails

        # DEBUG: Log what's being returned
        logger.debug(f"🔍 GET_USER_MODIFIED: {self.field_id} - returning user_modified = {user_modified}")

        return user_modified

    # ==================== TREE REGISTRY INTEGRATION ====================

    def get_current_values_as_instance(self) -> Any:
        """
        Get current form values reconstructed as an instance.

        Used by ConfigNode.get_live_instance() for context stack building.
        Returns the object instance with current form values applied.

        Returns:
            Instance with current form values
        """
        current_values = self.get_current_values()

        # For dataclasses, reconstruct instance with current values
        if is_dataclass(self.object_instance) and not isinstance(self.object_instance, type):
            return dataclasses.replace(self.object_instance, **current_values)

        # For non-dataclass objects, return object_instance as-is
        # (current values are tracked in self.parameters)
        return self.object_instance

    # ==================== LIVE CONTEXT OVERLAY ====================

    def get_user_modified_overlay(self) -> Dict[str, Any]:
        """
        Get user-modified values plus reconstructed nested dataclasses for live context.

        This keeps container layers (e.g., FunctionStep) visible to build_context_stack
        without rebuilding them in the collector on every call.
        """
        token = ObjectStateRegistry.get_token()
        cached_token, cached_overlay = self._overlay_cache
        logger.info(f"🔬 RESET_TRACE: get_user_modified_overlay({self.field_id}): token={token}, cached_token={cached_token}")
        if cached_token == token:
            logger.info(f"🔬 RESET_TRACE: OVERLAY CACHE HIT: {list(cached_overlay.keys())}")
            return cached_overlay

        logger.info(f"🔬 RESET_TRACE: OVERLAY CACHE MISS - computing...")
        logger.info(f"🔬 RESET_TRACE: _user_set_fields={self._user_set_fields}")
        overlay = dict(self.get_user_modified_values() or {})
        logger.info(f"🔬 RESET_TRACE: get_user_modified_values returned: {list(overlay.keys())}")

        for field_name, nested_state in self.nested_states.items():
            nested_overlay = nested_state.get_user_modified_overlay()
            if not nested_overlay:
                continue

            if is_dataclass(nested_state.object_instance):
                try:
                    overlay[field_name] = type(nested_state.object_instance)(**nested_overlay)
                except Exception:
                    overlay[field_name] = nested_overlay
            else:
                overlay[field_name] = nested_overlay

        self._overlay_cache = (token, overlay)
        logger.info(f"🔬 RESET_TRACE: Cached overlay: {list(overlay.keys())}")
        return overlay

    # ==================== SAVED STATE / DIRTY TRACKING ====================

    def _snapshot_object_instance(self) -> Dict[str, Any]:
        """Capture raw parameters from the backing object (pre-edit baseline)."""
        if is_dataclass(self.object_instance) and not isinstance(self.object_instance, type):
            raw = {}
            for f in dataclass_fields(self.object_instance):
                try:
                    raw[f.name] = object.__getattribute__(self.object_instance, f.name)
                except AttributeError:
                    raw[f.name] = None
            return raw
        if isinstance(self.object_instance, dict):
            return dict(self.object_instance)
        return dict(self.parameters)

    def _compute_resolved_snapshot(self) -> Dict[str, Any]:
        """Resolve all fields for this state and nested states into a snapshot dict."""
        snapshot: Dict[str, Any] = {}
        for name in self.parameters.keys():
            snapshot[name] = self.get_resolved_value(name)

        for nested_name, nested_state in self.nested_states.items():
            snapshot[nested_name] = nested_state._compute_resolved_snapshot()

        return snapshot

    def mark_saved(self) -> None:
        """Mark current state as saved baseline."""
        self.saved_parameters = copy.deepcopy(self.get_current_values())
        self.saved_resolved_state = self._compute_resolved_snapshot()
        self.saved_user_set_fields = set(self._user_set_fields)
        self.saved_reset_fields = set(self.reset_fields)
        self._dirty = False
        self.invalidate_cache()
        self._overlay_cache = (None, {})

        for nested_state in self.nested_states.values():
            nested_state.mark_saved()

    def restore_saved(self) -> None:
        """Restore parameters to the last saved baseline."""
        self.parameters = copy.deepcopy(self.saved_parameters)
        self._user_set_fields = set(self.saved_user_set_fields)
        self.reset_fields = set(self.saved_reset_fields)
        self._dirty = False
        self.invalidate_cache()
        self._overlay_cache = (None, {})

        for nested_state in self.nested_states.values():
            nested_state.restore_saved()

    def is_dirty(self) -> bool:
        """Return True if state has been modified since last saved baseline."""
        return self._dirty

    def get_user_modified_instance(self) -> Any:
        """
        Get instance with only user-edited fields.

        Used by ConfigNode.get_user_modified_instance() for reset logic.
        Only includes fields that the user has explicitly edited.

        Returns:
            Instance with only user-modified fields
        """
        user_modified = self.get_user_modified_values()

        # For dataclasses, create instance with only user-modified fields
        if is_dataclass(self.object_instance) and not isinstance(self.object_instance, type):
            # Start with None for all fields, only set user-modified ones
            all_fields = {f.name: None for f in dataclass_fields(self.object_instance)}
            all_fields.update(user_modified)
            return dataclasses.replace(self.object_instance, **all_fields)

        # For non-dataclass objects, return object_instance
        return self.object_instance

    # ==================== UPDATE CHECKING ====================

    def _should_skip_updates(self) -> bool:
        """
        Check if updates should be skipped due to batch operations.

        REFACTORING: Consolidates duplicate flag checking logic.
        Returns True if in reset mode or blocking cross-window updates.
        """
        # ANTI-DUCK-TYPING: Use direct attribute access (all flags initialized in __init__)
        # Check self flags
        if self._in_reset:
            logger.info(f"🚫 SKIP_CHECK: {self.field_id} has _in_reset=True")
            return True
        if self._block_cross_window_updates:
            logger.info(f"🚫 SKIP_CHECK: {self.field_id} has _block_cross_window_updates=True")
            return True

        # Check nested manager flags (nested managers are also ParameterFormManager instances)
        for nested_name, nested_state in self.nested_states.items():
            if nested_state._in_reset:
                logger.info(f"🚫 SKIP_CHECK: {self.field_id} nested manager {nested_name} has _in_reset=True")
                return True
            if nested_state._block_cross_window_updates:
                logger.info(f"🚫 SKIP_CHECK: {self.field_id} nested manager {nested_name} has _block_cross_window_updates=True")
                return True

        return False

    # DELETED: _on_nested_parameter_changed - replaced by FieldChangeDispatcher

    def _apply_to_nested_states(self, operation_func: Callable[[str, 'ObjectState'], None]) -> None:
        """Apply operation to all nested states."""
        for param_name, nested_state in self.nested_states.items():
            operation_func(param_name, nested_state)

    def _apply_callbacks_recursively(self, callback_list_name: str) -> None:
        """REFACTORING: Unified recursive callback application - eliminates duplicate methods.

        Args:
            callback_list_name: Name of the callback list attribute (e.g., '_on_build_complete_callbacks')
        """
        callback_list = getattr(self, callback_list_name)
        for callback in callback_list:
            callback()
        callback_list.clear()

        # Recursively apply nested managers' callbacks
        for nested_state in self.nested_states.values():
            nested_state._apply_callbacks_recursively(callback_list_name)


    # DELETED: _emit_cross_window_change - moved to FieldChangeDispatcher
