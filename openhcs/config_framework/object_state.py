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

from openhcs.config_framework.lazy_factory import is_lazy_dataclass

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
    _states: Dict[str, 'ObjectState'] = {}

    @classmethod
    def register(cls, state: 'ObjectState') -> None:
        """Register an ObjectState in the registry.

        Args:
            state: The ObjectState to register. Must have a scope_id.

        Raises:
            ValueError: If state has no scope_id.
        """
        if not state.scope_id:
            raise ValueError(f"Cannot register ObjectState without scope_id: {state.field_id}")

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
        if state.scope_id and state.scope_id in cls._states:
            del cls._states[state.scope_id]
            logger.debug(f"Unregistered ObjectState: scope={state.scope_id}")

    @classmethod
    def get_by_scope(cls, scope_id: str) -> Optional['ObjectState']:
        """Get ObjectState by scope_id.

        Args:
            scope_id: The scope identifier (e.g., "/path::step_0").

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
    def get_by_scope_prefix(cls, prefix: str) -> List['ObjectState']:
        """Get all ObjectStates whose scope_id starts with prefix.

        Useful for collecting all states for a specific plate, e.g.:
        get_by_scope_prefix("/plate_path") → all states for that plate

        Args:
            prefix: Scope prefix to match.

        Returns:
            List of matching ObjectState instances.
        """
        return [state for scope_id, state in cls._states.items() if scope_id.startswith(prefix)]

    @classmethod
    def clear(cls) -> None:
        """Clear all registered states. For testing only."""
        cls._states.clear()
        logger.debug("Cleared all ObjectStates from registry")


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
    ):
        """
        Initialize ObjectState with extracted MODEL from ParameterFormManager.

        Args:
            object_instance: The object being edited (dataclass instance, etc.)
            field_id: Unique identifier for this state
            scope_id: Scope identifier for filtering (e.g., "/path::step_0")
            context_obj: Parent object for inheritance resolution
            parent_state: Parent ObjectState for nested forms
        """
        # Core identity
        self.object_instance = object_instance
        self.field_id = field_id
        self.scope_id = parent_state.scope_id if parent_state else scope_id
        self.context_obj = context_obj
        self._parent_state: Optional['ObjectState'] = parent_state

        # Extract parameters from object instance
        self.parameters: Dict[str, Any] = {}
        self.parameter_types: Dict[str, Any] = {}  # Can be Type or str (forward ref)
        self.param_defaults: Dict[str, Any] = {}

        if is_dataclass(object_instance) and not isinstance(object_instance, type):
            for f in dataclass_fields(object_instance):
                self.parameters[f.name] = getattr(object_instance, f.name)
                self.parameter_types[f.name] = f.type
                self.param_defaults[f.name] = f.default if f.default is not dataclasses.MISSING else None

        # Tracking
        self._user_set_fields: Set[str] = set()
        self.reset_fields: Set[str] = set()

        # Load user-set fields from object if present
        if hasattr(object_instance, '_explicitly_set_fields'):
            explicitly_set = getattr(object_instance, '_explicitly_set_fields')
            if isinstance(explicitly_set, set):
                self._user_set_fields = explicitly_set.copy()

        # Nested states (for nested dataclasses)
        self.nested_states: Dict[str, 'ObjectState'] = {}

        # Flags
        self._in_reset = False
        self._block_cross_window_updates = False



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

        # Update state directly (no type conversion - that's VIEW responsibility)
        self.parameters[param_name] = value

        # Track user modification
        if user_set:
            self._user_set_fields.add(param_name)

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
        if not is_lazy_dataclass(self.object_instance):
            # For non-lazy dataclasses, return all current values
            result = self.get_current_values()

            return result

        # PERFORMANCE OPTIMIZATION: Only read values for user-set fields
        # Instead of calling get_current_values() which reads ALL widgets,
        # we only need values for fields in _user_set_fields
        user_modified = {}

        # Fast path: if no user-set fields, return empty dict
        if not self._user_set_fields:
            return user_modified

        # DEBUG: Log what fields are tracked as user-set
        logger.debug(f"🔍 GET_USER_MODIFIED: {self.field_id} - _user_set_fields = {self._user_set_fields}")

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

