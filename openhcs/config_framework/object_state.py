"""
ObjectState: Extracted MODEL from ParameterFormManager.

This class holds configuration state independently of UI widgets.
Lifecycle: Created when object added to pipeline, persists until removed.
PFM attaches to ObjectState when editor opens, detaches when closed.

ObjectStateRegistry: Singleton registry of all ObjectState instances.
Replaces LiveContextService._active_form_managers as the single source of truth.
"""
from dataclasses import is_dataclass, fields as dataclass_fields
import logging
from typing import Any, Callable, Dict, List, Optional, Set, TYPE_CHECKING
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

    # ========== TOKEN MANAGEMENT AND CHANGE NOTIFICATION ==========

    _token: int = 0  # Cache invalidation token
    _change_callbacks: List[Callable[[], None]] = []  # Change listeners

    @classmethod
    def get_token(cls) -> int:
        """Get current cache invalidation token."""
        return cls._token

    @classmethod
    def increment_token(cls, notify: bool = True) -> None:
        """Increment cache invalidation token.

        Args:
            notify: If True (default), notify listeners of the change.
                   Set to False when you need to invalidate caches but will
                   notify listeners later (e.g., after sibling refresh completes).
        """
        cls._token += 1
        if notify:
            cls._notify_change()

    @classmethod
    def _notify_change(cls) -> None:
        """Notify all listeners that something changed.

        UI-agnostic: No PyQt imports. If a callback's object was deleted,
        the RuntimeError is caught and the callback is removed.
        """
        logger.debug(f"🔔 _notify_change: notifying {len(cls._change_callbacks)} listeners")
        dead_callbacks = []
        for callback in cls._change_callbacks:
            try:
                callback()
            except RuntimeError as e:
                # "wrapped C/C++ object has been deleted" - mark for removal
                if "deleted" in str(e).lower():
                    logger.debug(f"  ⚠️  Callback's object was deleted, removing: {e}")
                    dead_callbacks.append(callback)
                else:
                    logger.warning(f"Change callback failed: {e}")
            except Exception as e:
                logger.warning(f"Change callback failed: {e}")

        # Clean up dead callbacks
        for cb in dead_callbacks:
            cls._change_callbacks.remove(cb)

    @classmethod
    def connect_listener(cls, callback: Callable[[], None]) -> None:
        """Connect a listener callback that's called on any change.

        The callback should debounce and call collect() to get fresh values.
        """
        if callback not in cls._change_callbacks:
            cls._change_callbacks.append(callback)
            logger.debug(f"Connected change listener: {callback}")

    @classmethod
    def disconnect_listener(cls, callback: Callable[[], None]) -> None:
        """Disconnect a change listener."""
        if callback in cls._change_callbacks:
            cls._change_callbacks.remove(callback)
            logger.debug(f"Disconnected change listener: {callback}")

    # ========== ANCESTOR OBJECT COLLECTION ==========

    @classmethod
    def get_ancestor_objects(cls, scope_id: Optional[str], use_saved: bool = False) -> List[Any]:
        """Get objects from this scope and all ancestors, least→most specific.

        Replaces LiveContextService.collect() + merge_ancestor_values() for simpler
        context stack building.

        Args:
            scope_id: The scope to get ancestors for (e.g., "/plate::step_0")
            use_saved: If True, return saved baseline (object_instance) instead of
                       live state (to_object()). Used when computing _saved_resolved
                       to ensure saved baseline only depends on other saved baselines.

        Returns:
            List of objects from ancestor scopes, ordered least→most specific.
            Each object is from state.object_instance (saved) or state.to_object() (live).
        """
        scope_key = cls._normalize_scope_id(scope_id)

        # Build list of ancestor scope keys (least-specific to most-specific)
        # e.g., "/plate::step_0" -> ["", "/plate", "/plate::step_0"]
        ancestors = [""]  # Global scope always included
        if scope_key:
            parts = scope_key.split("::")
            for i in range(len(parts)):
                ancestors.append("::".join(parts[:i+1]))

        # Get objects from ancestor scopes
        objects = []
        for ancestor_key in ancestors:
            state = cls._states.get(ancestor_key)
            if state:
                if use_saved:
                    # Return saved baseline (object_instance is updated in mark_saved)
                    objects.append(state.object_instance)
                else:
                    # Return live state with current edits
                    objects.append(state.to_object())

        return objects

    # ========== SCOPE + TYPE + FIELD AWARE INVALIDATION ==========

    @classmethod
    def invalidate_by_type_and_scope(
        cls,
        scope_id: Optional[str],
        changed_type: type,
        field_name: str
    ) -> None:
        """Invalidate a specific field in states that could inherit from changed_type at scope_id.

        PERFORMANCE: Three-tier filtering:
        1. SCOPE: State must be at or below changed scope (descendants inherit)
        2. TYPE: State's type tree must include changed_type
        3. FIELD: Only invalidate the specific field that changed

        If changing GlobalPipelineConfig.napari_streaming_config.window_size:
        - Only states with napari_streaming_config in their tree
        - Only the 'window_size' field is invalidated, not all 20+ fields
        - Steps without napari_streaming_config are NOT touched

        Args:
            scope_id: The scope that changed (None/"" for global scope)
            changed_type: The type of the ObjectState that was modified
            field_name: The specific field that changed
        """
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy

        changed_scope = cls._normalize_scope_id(scope_id)

        # Normalize to base type for comparison (LazyX → X)
        base_changed_type = get_base_type_for_lazy(changed_type) or changed_type

        for state in cls._states.values():
            state_scope = cls._normalize_scope_id(state.scope_id)

            # SCOPE CHECK: must be at or below changed scope
            # Global scope (empty string) affects ALL states
            if changed_scope == "":
                # Global scope - always a descendant (or self if also global)
                pass
            else:
                # Non-global: check exact match or descendant
                is_self = (state_scope == changed_scope)
                prefix = changed_scope + "::"
                is_descendant = state_scope.startswith(prefix)
                if not (is_self or is_descendant):
                    continue

            # TYPE + FIELD CHECK: find matching nested state and invalidate field
            cls._invalidate_field_in_matching_states(state, base_changed_type, field_name)

    @classmethod
    def _invalidate_field_in_matching_states(
        cls,
        state: 'ObjectState',
        target_base_type: type,
        field_name: str
    ) -> None:
        """Find fields in state that could inherit from target_base_type and invalidate them.

        With flat storage, we scan _path_to_type to find all dotted paths whose
        container type matches or inherits from target_base_type.

        A field should be invalidated if:
        1. Its container type matches target_base_type exactly, OR
        2. Its container type inherits from target_base_type (has target_base_type in MRO)

        This handles sibling inheritance: when WellFilterConfig.well_filter changes,
        both 'well_filter_config.well_filter' and 'step_well_filter_config.well_filter'
        are invalidated (since StepWellFilterConfig inherits from WellFilterConfig).

        Args:
            state: ObjectState to check
            target_base_type: Normalized base type to match
            field_name: Field to invalidate
        """
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy

        invalidated_paths: set[str] = set()

        # Scan _path_to_type for matching container types
        for dotted_path, container_type in state._path_to_type.items():
            # Normalize container type
            container_base_type = get_base_type_for_lazy(container_type) or container_type

            # Check if target_base_type is in the MRO (container inherits the field)
            type_matches = False
            for mro_class in container_base_type.__mro__:
                mro_base = get_base_type_for_lazy(mro_class) or mro_class
                if mro_base == target_base_type:
                    type_matches = True
                    break

            # If type matches and path ends with the field_name, invalidate it
            if type_matches and (dotted_path.endswith(f'.{field_name}') or dotted_path == field_name):
                if dotted_path in state.parameters:
                    state.invalidate_field(dotted_path)
                    invalidated_paths.add(dotted_path)

        # Fire on_resolved_changed for descendant states so list items flash
        # (This is triggered by cross-scope inheritance, not direct edit)
        if invalidated_paths and state._on_resolved_changed_callbacks:
            for callback in state._on_resolved_changed_callbacks:
                try:
                    callback(invalidated_paths)
                except Exception as e:
                    logger.warning(f"Error in resolved_changed callback during invalidation: {e}")


class FieldProxy:
    """Type-safe proxy for accessing ObjectState fields via dotted attribute syntax.

    Provides IDE autocomplete while using flat internal storage:
    - External API: state.fields.well_filter_config.well_filter (type-safe)
    - Internal: state.parameters['well_filter_config.well_filter'] (flat dict)
    """

    def __init__(self, state: 'ObjectState', path: str, field_type: type):
        """Initialize FieldProxy.

        Args:
            state: The ObjectState this proxy accesses
            path: Current dotted path (empty for root)
            field_type: Type of the object at this path
        """
        object.__setattr__(self, '_state', state)
        object.__setattr__(self, '_path', path)
        object.__setattr__(self, '_type', field_type)

    def __getattr__(self, name: str) -> Any:
        """Get field value or nested FieldProxy.

        Args:
            name: Field name to access

        Returns:
            FieldProxy for nested dataclass fields, or resolved value for leaf fields
        """
        new_path = f'{self._path}.{name}' if self._path else name

        # Get field info from the type
        if not is_dataclass(self._type):
            type_name = getattr(self._type, '__name__', str(self._type))
            raise AttributeError(f"{type_name} is not a dataclass")

        field_info = None
        for f in dataclass_fields(self._type):
            if f.name == name:
                field_info = f
                break

        if field_info is None:
            type_name = getattr(self._type, '__name__', str(self._type))
            raise AttributeError(f"{type_name} has no field '{name}'")

        # Check if field is a nested dataclass
        field_type = field_info.type

        # Handle Optional[DataclassType]
        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
        if isinstance(field_type, type) and ParameterTypeUtils.is_optional_dataclass(field_type):
            nested_type = ParameterTypeUtils.get_optional_inner_type(field_type)
            if isinstance(nested_type, type):
                return FieldProxy(self._state, new_path, nested_type)

        # Handle direct dataclass type
        if isinstance(field_type, type) and is_dataclass(field_type):
            return FieldProxy(self._state, new_path, field_type)

        # Leaf field - get resolved value
        return self._state.get_resolved_value(new_path)

    def __setattr__(self, name: str, value: Any) -> None:
        """Prevent attribute setting - use state.update_parameter() instead."""
        _ = (name, value)  # Suppress unused warnings
        raise AttributeError("FieldProxy is read-only. Use state.update_parameter(path, value) to set values.")


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
    - _live_resolved: Resolved snapshot using live hierarchy (None = needs compute)
    - _invalid_fields: Fields needing partial recompute
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

        # === Flat Storage (NEW - for flattened architecture) ===
        self._path_to_type: Dict[str, type] = {}  # Maps dotted paths to their container types
        self._cached_object: Optional[Any] = None  # Cached result of to_object()

        # Extract parameters using FLAT extraction (dotted paths)
        # This replaces the old UnifiedParameterAnalyzer + _create_nested_states() approach
        self.parameters: Dict[str, Any] = {}
        self._signature_defaults: Dict[str, Any] = {}

        # Store excluded params and their original values for reconstruction
        # e.g., FunctionStep excludes 'func' but we need it for to_object()
        self._exclude_param_names: List[str] = list(exclude_params or [])  # For restore_saved()
        self._excluded_params: Dict[str, Any] = {}
        for param_name in self._exclude_param_names:
            if hasattr(object_instance, param_name):
                self._excluded_params[param_name] = getattr(object_instance, param_name)

        # Flatten parameter extraction - walk nested dataclasses recursively
        self._extract_all_parameters_flat(object_instance, prefix='', exclude_params=self._exclude_param_names)

        # NOTE: Signature defaults are now populated by _extract_all_parameters_flat()
        # for all fields including nested ones (flattened dotted paths).

        # Apply initial_values overrides (e.g., saved kwargs for functions)
        if initial_values:
            self.parameters.update(initial_values)

        # === Structure (1 attribute) ===
        self._parent_state: Optional['ObjectState'] = parent_state
        # NOTE: nested_states DELETED - flat storage eliminates nested ObjectState instances

        # === Cache (2 attributes) ===
        self._live_resolved: Optional[Dict[str, Any]] = None  # None = needs full compute
        self._invalid_fields: Set[str] = set()  # Fields needing partial recompute

        # === Saved baseline (2 attributes) ===
        self._saved_resolved: Dict[str, Any] = {}
        self._saved_parameters: Dict[str, Any] = {}  # Immutable snapshot for diff on restore

        # === Flags (kept for batch operations) ===
        self._in_reset = False
        self._block_cross_window_updates = False

        # === Resolved Change Callbacks ===
        # Callbacks notified when resolved values actually change (for UI flashing)
        self._on_resolved_changed_callbacks: List[Callable[[Set[str]], None]] = []

        # Initialize baselines (suppress notifications during init)
        self._ensure_live_resolved(notify=False)
        # Compute saved baseline using SAVED ancestor values (use_saved=True)
        # This ensures new ObjectStates are immediately dirty if live context differs from saved
        self._saved_resolved = self._compute_resolved_snapshot(use_saved=True)
        self._saved_parameters = copy.deepcopy(self.parameters)

    @property
    def context_obj(self) -> Optional[Any]:
        """Derive context_obj from parent_state (no separate attribute needed)."""
        return self._parent_state.object_instance if self._parent_state else None

    @property
    def fields(self) -> FieldProxy:
        """Type-safe field access via FieldProxy.

        Returns:
            FieldProxy for accessing fields with IDE autocomplete:
            state.fields.well_filter_config.well_filter → resolved value
        """
        return FieldProxy(self, '', type(self.object_instance))

    # === Resolved Change Subscription ===

    def on_resolved_changed(self, callback: Callable[[Set[str]], None]) -> None:
        """Subscribe to resolved value change notifications.

        The callback is called when resolved values actually change (not just when
        cache is invalidated). This enables UI components to flash/highlight
        specific fields when their resolved values change.

        Args:
            callback: Function that takes a Set[str] of changed dotted paths.
                      E.g., {'processing_config.group_by', 'well_filter_config.well_filter'}
        """
        if callback not in self._on_resolved_changed_callbacks:
            self._on_resolved_changed_callbacks.append(callback)

    def off_resolved_changed(self, callback: Callable[[Set[str]], None]) -> None:
        """Unsubscribe from resolved value change notifications."""
        if callback in self._on_resolved_changed_callbacks:
            self._on_resolved_changed_callbacks.remove(callback)

    def _ensure_live_resolved(self, notify: bool = True) -> None:
        """Ensure _live_resolved cache is populated.

        PERFORMANCE: Field-level invalidation only.
        - First access: full compute to populate cache
        - After update_parameter(): only recompute invalid fields
        - Cross-window access: return cached values directly (no work)

        Args:
            notify: If True, notify callbacks when resolved values change.
                    Set to False during initialization to suppress notifications.

        NOTE: Global token is for LiveContextService.collect(), NOT for _live_resolved.
        """
        # First access - populate cache
        if self._live_resolved is None:
            self._live_resolved = self._compute_resolved_snapshot()
            self._invalid_fields.clear()
            return

        # Partial recompute for invalid fields only
        if self._invalid_fields:
            changed_paths = self._recompute_invalid_fields()
            self._invalid_fields.clear()

            # Notify subscribers of which paths actually changed
            if notify and changed_paths and self._on_resolved_changed_callbacks:
                for callback in self._on_resolved_changed_callbacks:
                    try:
                        callback(changed_paths)
                    except Exception as e:
                        logger.warning(f"Error in resolved_changed callback: {e}")

    # DELETED: _create_nested_states() - No longer needed with flat storage
    # Nested ObjectStates are no longer created - flat storage handles all parameters

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

        Enforces invariants:
        1. State mutation → scope+type+field aware cache invalidation
        2. State mutation → global token increment (for live context cache)

        PERFORMANCE: Three-tier filtering for minimal invalidation:
        - SCOPE: Only descendants of this scope (they inherit from us)
        - TYPE: Only states with this type in their tree
        - FIELD: Only the specific field that changed

        Args:
            param_name: Name of parameter to update
            value: New value
        """
        if param_name not in self.parameters:
            return

        # Update state directly (no type conversion - that's VIEW responsibility)
        self.parameters[param_name] = value

        # SELF-INVALIDATION: Mark this field as needing recompute in our own cache
        self._invalid_fields.add(param_name)
        self._cached_object = None  # Invalidate cached reconstructed object

        # SCOPE + TYPE + FIELD AWARE INVALIDATION:
        # Get the CONTAINER type for this field (e.g., WellFilterConfig for 'well_filter_config.well_filter')
        # This is critical for sibling inheritance: when WellFilterConfig.well_filter changes,
        # we need to invalidate PathPlanningConfig.well_filter (which inherits from WellFilterConfig)
        container_type = self._path_to_type.get(param_name, type(self.object_instance))

        # Extract leaf field name for invalidation matching
        leaf_field_name = param_name.split('.')[-1] if '.' in param_name else param_name

        ObjectStateRegistry.invalidate_by_type_and_scope(
            scope_id=self.scope_id,
            changed_type=container_type,
            field_name=leaf_field_name
        )

        # Increment global token for LiveContextService.collect() cache invalidation
        ObjectStateRegistry.increment_token(notify=False)

    def get_resolved_value(self, param_name: str) -> Any:
        """Get resolved value for a field from the bulk snapshot.

        Args:
            param_name: Field name to resolve (can be dotted path like 'path_planning_config.well_filter')

        Returns:
            Resolved value from _live_resolved snapshot
        """
        self._ensure_live_resolved()
        assert self._live_resolved is not None  # Guaranteed by _ensure_live_resolved
        return self._live_resolved.get(param_name)

    def find_path_for_type(self, container_type: type) -> Optional[str]:
        """Find the path prefix for a container type in this ObjectState.

        With flat storage, nested configs are identified by their path prefix.
        Given a container type (e.g., PathPlanningConfig), returns the path prefix
        (e.g., 'path_planning_config').

        Args:
            container_type: The type to find the path for

        Returns:
            Path prefix for the type, or None if not found
        """
        # Look for paths where the TYPE is the container type (not a child of it)
        # The path for a nested config is the one WITHOUT a dot suffix that has the type
        for path, typ in self._path_to_type.items():
            if typ == container_type and '.' not in path:
                return path
        return None

    def resolve_for_type(self, container_type: type, field_name: str) -> Any:
        """Resolve a field value given the container type and field name.

        Convenience method for callers who have a config object but don't know
        its path in the flat storage. Finds the path prefix for the container type
        and constructs the full dotted path.

        Args:
            container_type: Type of the containing config (e.g., PathPlanningConfig)
            field_name: Field name within that config (e.g., 'well_filter')

        Returns:
            Resolved value, or None if not found
        """
        path_prefix = self.find_path_for_type(container_type)
        if path_prefix is None:
            # Type not found - try the field_name directly (top-level field)
            return self.get_resolved_value(field_name)

        full_path = f'{path_prefix}.{field_name}'
        return self.get_resolved_value(full_path)

    def invalidate_cache(self) -> None:
        """Invalidate resolved cache - forces full recompute on next access."""
        self._live_resolved = None
        self._cached_object = None  # Also invalidate cached object

    def invalidate_self_and_nested(self) -> None:
        """Invalidate this state's cache.

        With flat storage, no nested states to invalidate.
        """
        self._live_resolved = None
        self._invalid_fields.clear()  # Full invalidation, not field-level
        self._cached_object = None

    def invalidate_field(self, field_name: str) -> None:
        """Mark a specific field as needing recomputation.

        PERFORMANCE: Field-level invalidation - only the changed field
        needs recomputation, not all 20+ fields in the config.
        """
        if field_name in self.parameters:
            self._invalid_fields.add(field_name)

    def _recompute_invalid_fields(self) -> Set[str]:
        """Recompute only the invalid fields, not the entire snapshot.

        PERFORMANCE: For explicitly set values, use parameters directly.
        Only build context stack for inherited (None) values.

        Returns:
            Set of paths whose resolved values actually changed (for UI notification).
        """
        from openhcs.config_framework.context_manager import build_context_stack

        changed_paths: Set[str] = set()

        # _live_resolved must exist when this is called (from _ensure_live_resolved)
        if self._live_resolved is None:
            return changed_paths

        # Separate explicit vs inherited fields, skipping container entries
        explicit_fields = []
        inherited_fields = []
        for name in self._invalid_fields:
            if name not in self.parameters:
                continue
            # Skip container entries (value is a dataclass instance)
            # Container entries are kept in parameters for UI rendering but excluded from snapshots
            raw_value = self.parameters[name]
            is_container = raw_value is not None and is_dataclass(type(raw_value))
            if is_container:
                continue
            if raw_value is not None:
                explicit_fields.append(name)
            else:
                inherited_fields.append(name)

        # Explicit values: use parameters directly (no resolution needed)
        for name in explicit_fields:
            old_val = self._live_resolved.get(name)
            explicit_val = self.parameters[name]
            if old_val != explicit_val:
                changed_paths.add(name)
            self._live_resolved[name] = explicit_val
            logger.debug(
                f"RECOMPUTE EXPLICIT [{self.scope_id}] {name}: "
                f"value={explicit_val!r} (type={type(explicit_val).__name__})"
            )

        # Inherited values: need context stack for lazy resolution
        if inherited_fields:
            ancestor_objects = ObjectStateRegistry.get_ancestor_objects(self.scope_id)

            # CRITICAL: Use to_object() to get CURRENT state with user edits,
            # not object_instance which is the original/saved baseline.
            # This ensures sibling field inheritance sees updated values.
            current_obj = self.to_object()

            stack = build_context_stack(
                object_instance=current_obj,
                ancestor_objects=ancestor_objects,
            )

            with stack:
                # For each inherited field, create a fresh instance of its CONTAINER type
                # (the lazy dataclass), not the root object type
                for dotted_path in inherited_fields:
                    container_type = self._path_to_type.get(dotted_path)
                    if container_type is None:
                        continue
                    # Skip non-dataclass container types (e.g., built-in 'function' type
                    # for primitive parameters of functions - these don't have lazy resolution)
                    if not is_dataclass(container_type):
                        continue
                    parts = dotted_path.split('.')
                    field_name = parts[-1]
                    # Create fresh lazy dataclass instance - triggers lazy resolution
                    container_instance = container_type()
                    old_val = self._live_resolved.get(dotted_path)
                    value = getattr(container_instance, field_name)
                    # DEBUG: Catch the bug where we get the whole GlobalPipelineConfig
                    if is_dataclass(type(value)) and dotted_path == 'num_workers':
                        logger.error(
                            f"BUG DETECTED: num_workers resolved to dataclass {type(value).__name__}! "
                            f"container_type={container_type.__name__}, field_name={field_name}, "
                            f"container_instance.__class__={container_instance.__class__.__name__}"
                        )
                        # Debug: what was in available_configs?
                        from openhcs.config_framework.context_manager import current_temp_global, extract_all_configs
                        try:
                            ctx = current_temp_global.get()
                            configs = extract_all_configs(ctx)
                            logger.error(f"  available_configs keys: {list(configs.keys())}")
                            for k, v in configs.items():
                                logger.error(f"    {k}: {type(v).__name__} (id={id(v)})")
                        except Exception as e:
                            logger.error(f"  Failed to get configs: {e}")
                    if old_val != value:
                        changed_paths.add(dotted_path)
                    self._live_resolved[dotted_path] = value

        return changed_paths

    def reset_parameter(self, param_name: str) -> None:
        """Reset parameter to signature default (None for lazy dataclasses).

        Delegates to update_parameter() to ensure consistent invalidation behavior.
        """
        if param_name not in self.parameters:
            return

        # Use signature defaults (CLASS defaults), not instance values
        # This ensures reset goes back to None for lazy fields, not saved concrete values
        default_value = self._signature_defaults.get(param_name)
        self.update_parameter(param_name, default_value)



    def get_current_values(self) -> Dict[str, Any]:
        """
        Get current parameter values from state.

        With flat storage, this returns the flat dict with dotted paths.
        Callers needing nested structure should use to_object() instead.

        For ObjectState, this reads directly from self.parameters.
        PFM overrides this to also read from widgets.
        """
        return dict(self.parameters)



    # ==================== SAVED STATE / DIRTY TRACKING ====================

    def _compute_resolved_snapshot(self, use_saved: bool = False) -> Dict[str, Any]:
        """Resolve all fields for this state into a snapshot dict.

        PERFORMANCE: Build context stack ONCE and resolve ALL fields in bulk (not per-field).

        UNIFIED: Works for ANY object_instance type (dataclass, class instance, callable).
        Root object type doesn't matter - we iterate paths and check _path_to_type for each.

        Args:
            use_saved: If True, resolve using saved baselines (object_instance) instead of
                       live state (to_object()). Used for computing _saved_resolved to ensure
                       saved baseline only depends on other saved baselines.
        """
        from openhcs.config_framework.context_manager import build_context_stack

        # Get ancestor objects for context stack
        # use_saved=True returns object_instance (saved), False returns to_object() (live)
        ancestor_objects = ObjectStateRegistry.get_ancestor_objects(self.scope_id, use_saved=use_saved)

        # Use saved baseline or live state for this object
        if use_saved:
            current_obj = self.object_instance
        else:
            # CRITICAL: Use to_object() to get CURRENT state with user edits,
            # not object_instance which is the original/saved baseline.
            current_obj = self.to_object()

        # Build context stack ONCE
        stack = build_context_stack(
            object_instance=current_obj,
            ancestor_objects=ancestor_objects,
        )

        snapshot: Dict[str, Any] = {}

        # UNIFIED: Resolve ALL fields in single context stack
        # For each path, check if it has a lazy dataclass container type
        with stack:
            for dotted_path in self.parameters.keys():
                raw_value = self.parameters[dotted_path]
                container_type = self._path_to_type.get(dotted_path)
                parts = dotted_path.split('.')

                # Check if this path is a CONTAINER entry (value is a nested dataclass)
                # vs a LEAF field (value is primitive, even if container_type is a dataclass)
                is_container_entry = raw_value is not None and is_dataclass(type(raw_value))

                if is_container_entry:
                    # Container-level entry - SKIP from snapshot
                    # Containers are kept in parameters for UI rendering but excluded from
                    # dirty comparison since we compare leaf fields instead
                    pass
                elif container_type is not None and is_dataclass(container_type):
                    # Leaf field inside a lazy dataclass - create container and resolve
                    # This handles both:
                    # - Nested fields (processing_config.group_by) where parts > 1
                    # - Top-level fields on root (num_workers on PipelineConfig) where parts == 1
                    container_instance = container_type()
                    field_name = parts[-1]
                    resolved_val = getattr(container_instance, field_name)
                    snapshot[dotted_path] = resolved_val
                    logger.debug(
                        f"SNAPSHOT [{self.scope_id}] {dotted_path}: "
                        f"raw={raw_value!r} -> resolved={resolved_val!r} (type={type(resolved_val).__name__})"
                    )
                else:
                    # Non-dataclass field - use raw value directly
                    snapshot[dotted_path] = raw_value

        return snapshot

    def mark_saved(self) -> None:
        """Mark current state as saved baseline.

        UNIFIED: Works for any object_instance type.

        CRITICAL: Invalidates descendant caches for any parameters that changed.
        This ensures that when saving, other windows that inherited from the
        old saved values get their caches invalidated so they pick up new values.
        This mirrors what restore_saved() does but in the opposite direction.
        """
        if not isinstance(self.object_instance, type):
            # Update object_instance with current parameters
            # to_object() already handles all types uniformly
            self.object_instance = self.to_object()

        # Update saved parameters FIRST (before computing saved snapshot)
        self._saved_parameters = copy.deepcopy(self.parameters)

        # Compute new saved resolved using SAVED ancestor baselines (use_saved=True)
        # This ensures saved baseline is computed relative to other saved baselines
        new_saved_resolved = self._compute_resolved_snapshot(use_saved=True)

        # Find parameters that differ between old saved and new saved
        changed_params = []
        for param_name in set(self._saved_resolved.keys()) | set(new_saved_resolved.keys()):
            old_saved = self._saved_resolved.get(param_name)
            new_value = new_saved_resolved.get(param_name)
            if old_saved != new_value:
                changed_params.append(param_name)

        # Invalidate descendant caches for each changed parameter
        # This mirrors what restore_saved() does
        for param_name in changed_params:
            container_type = self._path_to_type.get(param_name, type(self.object_instance))
            leaf_field_name = param_name.split('.')[-1] if '.' in param_name else param_name

            ObjectStateRegistry.invalidate_by_type_and_scope(
                scope_id=self.scope_id,
                changed_type=container_type,
                field_name=leaf_field_name
            )

        # NOW update saved resolved baseline
        self._saved_resolved = new_saved_resolved

        # Invalidate cached object so next to_object() call rebuilds
        self._cached_object = None

    def restore_saved(self) -> None:
        """Restore parameters to the last saved baseline (from object_instance).

        UNIFIED: Works for any object_instance type.

        CRITICAL: Invalidates descendant caches for any parameters that changed.
        This ensures that when closing a window without saving, other windows
        that inherited from the unsaved values get their caches invalidated.

        Also emits on_resolved_changed for THIS state so same-level observers
        (like list items subscribed to this ObjectState) flash when values revert.
        """
        if isinstance(self.object_instance, type):
            self.invalidate_cache()
            return

        # Find parameters that differ from saved baseline
        changed_params = []
        for param_name, current_value in self.parameters.items():
            saved_value = self._saved_parameters.get(param_name)
            if current_value != saved_value:
                changed_params.append(param_name)

        # Invalidate descendant caches for each changed parameter
        # This mirrors what update_parameter() does when a value changes
        for param_name in changed_params:
            container_type = self._path_to_type.get(param_name, type(self.object_instance))
            leaf_field_name = param_name.split('.')[-1] if '.' in param_name else param_name

            ObjectStateRegistry.invalidate_by_type_and_scope(
                scope_id=self.scope_id,
                changed_type=container_type,
                field_name=leaf_field_name
            )

        # Clear and re-extract from object_instance (the saved version)
        # CRITICAL: Pass exclude_params to ensure excluded fields stay excluded
        self.parameters.clear()
        self._path_to_type.clear()
        self._extract_all_parameters_flat(self.object_instance, prefix='', exclude_params=self._exclude_param_names)

        self.invalidate_cache()

        # Emit on_resolved_changed for changed params so SAME-LEVEL observers flash
        # (e.g., list item subscribed to this ObjectState sees the revert as a change)
        if changed_params and self._on_resolved_changed_callbacks:
            changed_paths = set(changed_params)
            for callback in self._on_resolved_changed_callbacks:
                try:
                    callback(changed_paths)
                except Exception as e:
                    logger.warning(f"Error in resolved_changed callback during restore: {e}")

    def is_dirty(self) -> bool:
        """Return True if resolved state differs from saved baseline."""
        self._ensure_live_resolved()
        is_dirty = self._live_resolved != self._saved_resolved
        if is_dirty:
            # Log which fields differ
            for key in set(self._live_resolved.keys()) | set(self._saved_resolved.keys()):
                live_val = self._live_resolved.get(key)
                saved_val = self._saved_resolved.get(key)
                if live_val != saved_val:
                    logger.debug(
                        f"DIRTY FIELD [{self.scope_id}] {key}: "
                        f"live={live_val!r} (type={type(live_val).__name__}) != "
                        f"saved={saved_val!r} (type={type(saved_val).__name__})"
                    )
        return is_dirty

    def should_skip_updates(self) -> bool:
        """Check if updates should be skipped due to batch operations."""
        return self._in_reset or self._block_cross_window_updates

    def update_thread_local_global_config(self):
        """Update thread-local GlobalPipelineConfig with current form values.

        LIVE UPDATES ARCHITECTURE:
        Called on every parameter change when editing GlobalPipelineConfig.
        Updates thread-local storage so other windows see changes immediately.
        Original config is stored by ConfigWindow and restored on Cancel.
        """
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.config_framework.global_config import set_global_config_for_editing
        from openhcs.config_framework.context_manager import get_base_global_config
        from openhcs.pyqt_gui.widgets.shared.services.value_collection_service import ValueCollectionService

        current_values = self.get_current_values()
        base_config = get_base_global_config()
        reconstructed_values = ValueCollectionService.reconstruct_nested_dataclasses(current_values)

        try:
            # Use replace_raw to preserve None values (dataclasses.replace triggers lazy resolution)
            from openhcs.config_framework.lazy_factory import replace_raw
            new_config = replace_raw(base_config, **reconstructed_values)
            set_global_config_for_editing(GlobalPipelineConfig, new_config)
            logger.debug(f"🔍 LIVE_UPDATES: Updated thread-local GlobalPipelineConfig")
        except Exception as e:
            logger.warning(f"🔍 LIVE_UPDATES: Failed to update thread-local GlobalPipelineConfig: {e}")

    # ==================== FLAT STORAGE METHODS (NEW) ====================

    def _extract_all_parameters_flat(self, obj: Any, prefix: str = '', exclude_params: Optional[List[str]] = None) -> None:
        """Recursively extract parameters into flat dict with dotted paths.

        Populates self.parameters and self._path_to_type with dotted path keys.

        UNIFIED PATH: Uses UnifiedParameterAnalyzer for ALL object types.
        UnifiedParameterAnalyzer already handles both dataclasses and non-dataclasses
        via its internal routing (MRO traversal for regular classes, dataclass_fields for dataclasses).

        Args:
            obj: Object to extract from (dataclass instance OR regular object like FunctionStep)
            prefix: Current path prefix (e.g., 'well_filter_config')
            exclude_params: List of top-level parameter names to exclude
        """
        from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer

        exclude_params = exclude_params or []
        obj_type = type(obj)
        is_function = obj_type.__name__ == 'function'

        # UNIFIED: Use UnifiedParameterAnalyzer for ALL object types
        # It already handles dataclasses vs non-dataclasses internally
        param_info = UnifiedParameterAnalyzer.analyze(obj, exclude_params=exclude_params if not prefix else [])

        for param_name, info in param_info.items():
            # Skip excluded parameters (only at top level)
            if not prefix and param_name in exclude_params:
                continue

            # Build dotted path
            dotted_path = f'{prefix}.{param_name}' if prefix else param_name

            # Get current value
            if is_function:
                # For functions: use signature default from UnifiedParameterAnalyzer
                # (functions don't have instance attributes)
                current_value = info.default_value
            else:
                # For class instances: bypass lazy resolution via object.__getattribute__
                try:
                    current_value = object.__getattribute__(obj, param_name)
                except AttributeError:
                    current_value = info.default_value

            # Check if this is a nested dataclass
            # First try from type annotation, then fall back to checking actual value
            nested_type = self._get_nested_dataclass_type(info.param_type)

            # For functions with injected params, param_type may be Any but value is dataclass
            # Use is_dataclass on the TYPE, not the value (to avoid triggering lazy resolution)
            if nested_type is None and current_value is not None:
                value_type = type(current_value)
                if is_dataclass(value_type):
                    nested_type = value_type

            if nested_type is not None and current_value is not None:
                # Store the nested config type reference at this path
                self._path_to_type[dotted_path] = nested_type

                # Store the nested dataclass instance in parameters (needed for UI rendering)
                self.parameters[dotted_path] = current_value

                # Recurse into nested dataclass for child fields
                self._extract_all_parameters_flat(current_value, prefix=dotted_path, exclude_params=[])
            else:
                # Leaf field - store value and container type
                self.parameters[dotted_path] = current_value
                # Store the CONTAINER type (the type that has this field)
                self._path_to_type[dotted_path] = obj_type
                # Store signature default for reset functionality (flattened)
                self._signature_defaults[dotted_path] = info.default_value

    def to_object(self) -> Any:
        """Reconstruct object from flat parameters with updated nested configs.

        BOUNDARY METHOD - EXPENSIVE - only call at system boundaries:
        - Save operation
        - Execute operation
        - Serialization

        UNIFIED: Works for ANY object_instance type.
        - Python functions: can't copy, return original
        - Everything else: shallow copy + reconstruct nested dataclass fields
        """
        if self._cached_object is not None:
            return self._cached_object

        # UNIFIED: reconstruct nested dataclass fields
        # Works for dataclass, non-dataclass class instances, AND functions
        import copy

        # Collect ALL top-level field updates from self.parameters
        # This includes both primitive fields AND nested dataclass fields
        field_updates = {}
        for field_name in self._path_to_type:
            if '.' not in field_name:
                # Check if the stored value is a dataclass instance
                value = self.parameters.get(field_name)
                if value is not None and is_dataclass(type(value)):
                    # Nested dataclass: recursively reconstruct
                    field_updates[field_name] = self._reconstruct_from_prefix(field_name)
                else:
                    # Primitive field: use value directly from parameters
                    field_updates[field_name] = value

        # Python functions can't be copied, but we CAN update their attributes
        # This is critical for MRO resolution to see edited config values
        if type(self.object_instance).__name__ == 'function':
            for field_name, field_value in field_updates.items():
                setattr(self.object_instance, field_name, field_value)
            self._cached_object = self.object_instance
        elif is_dataclass(self.object_instance):
            # CRITICAL: Use replace_raw to preserve raw None values!
            # dataclasses.replace triggers lazy resolution via __getattribute__,
            # which resolves None -> concrete defaults and breaks inheritance.
            from openhcs.config_framework.lazy_factory import replace_raw
            self._cached_object = replace_raw(self.object_instance, **field_updates)
        else:
            # Non-dataclass class instance - shallow copy + setattr
            obj_copy = copy.copy(self.object_instance)
            for field_name, field_value in field_updates.items():
                setattr(obj_copy, field_name, field_value)
            self._cached_object = obj_copy

        return self._cached_object

    def _reconstruct_from_prefix(self, prefix: str) -> Any:
        """Recursively reconstruct dataclass from flat parameters.

        Args:
            prefix: Current path prefix (e.g., 'well_filter_config')

        Returns:
            Reconstructed dataclass instance
        """
        # Determine the type to reconstruct
        if not prefix:
            # Root level - use object_instance type
            obj_type = type(self.object_instance)
        else:
            # Nested level - look up type from _path_to_type
            obj_type = self._path_to_type.get(prefix)
            if obj_type is None:
                raise ValueError(f"No type mapping for prefix: {prefix}")

        prefix_dot = f'{prefix}.' if prefix else ''

        # Collect direct fields and nested prefixes
        direct_fields = {}
        nested_prefixes = set()

        for path, value in self.parameters.items():
            if not path.startswith(prefix_dot):
                continue

            remainder = path[len(prefix_dot):]

            if '.' in remainder:
                # This is a nested field - collect the first component
                first_component = remainder.split('.')[0]
                nested_prefixes.add(first_component)
            else:
                # Direct field of this object
                direct_fields[remainder] = value

        # Reconstruct nested dataclasses first
        for nested_name in nested_prefixes:
            nested_path = f'{prefix_dot}{nested_name}'
            nested_obj = self._reconstruct_from_prefix(nested_path)
            direct_fields[nested_name] = nested_obj

        # Filter out None values for lazy resolution
        filtered_fields = {k: v for k, v in direct_fields.items() if v is not None}

        # At root level, include excluded params (e.g., 'func' for FunctionStep)
        # These are required for construction but excluded from editing
        if not prefix:
            filtered_fields.update(self._excluded_params)

        # Instantiate the dataclass
        return obj_type(**filtered_fields)
