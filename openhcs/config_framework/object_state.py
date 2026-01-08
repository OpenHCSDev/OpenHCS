"""
ObjectState: Extracted MODEL from ParameterFormManager.

This class holds configuration state independently of UI widgets.
Lifecycle: Created when object added to pipeline, persists until removed.
PFM attaches to ObjectState when editor opens, detaches when closed.

ObjectStateRegistry: Singleton registry of all ObjectState instances.
Replaces LiveContextService._active_form_managers as the single source of truth.
"""
from contextlib import contextmanager
from dataclasses import is_dataclass, fields as dataclass_fields
import logging
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, TYPE_CHECKING, Generator
import copy

from openhcs.config_framework.snapshot_model import Snapshot, StateSnapshot, Timeline

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

    # Registration lifecycle callbacks - UI subscribes to sync list items with ObjectState lifecycle
    # Callbacks receive (scope_id: str, object_state: ObjectState)
    _on_register_callbacks: List[Callable[[str, 'ObjectState'], None]] = []
    _on_unregister_callbacks: List[Callable[[str, 'ObjectState'], None]] = []

    # Time-travel completion callbacks - UI subscribes to reopen windows for dirty states
    # Callbacks receive (dirty_states, triggering_scope) where:
    # - dirty_states: list of (scope_id, ObjectState) tuples with unsaved changes
    # - triggering_scope: scope_id that triggered the snapshot (may be None)
    _on_time_travel_complete_callbacks: List[Callable[[List[Tuple[str, 'ObjectState']], Optional[str]], None]] = []

    # History changed callbacks - fired when history is modified (snapshot added or time-travel)
    # Used by TimeTravelWidget to stay in sync without polling
    _on_history_changed_callbacks: List[Callable[[], None]] = []

    @classmethod
    def add_register_callback(cls, callback: Callable[[str, 'ObjectState'], None]) -> None:
        """Subscribe to ObjectState registration events."""
        if callback not in cls._on_register_callbacks:
            cls._on_register_callbacks.append(callback)

    @classmethod
    def remove_register_callback(cls, callback: Callable[[str, 'ObjectState'], None]) -> None:
        """Unsubscribe from ObjectState registration events."""
        if callback in cls._on_register_callbacks:
            cls._on_register_callbacks.remove(callback)

    @classmethod
    def add_unregister_callback(cls, callback: Callable[[str, 'ObjectState'], None]) -> None:
        """Subscribe to ObjectState unregistration events."""
        if callback not in cls._on_unregister_callbacks:
            cls._on_unregister_callbacks.append(callback)

    @classmethod
    def remove_unregister_callback(cls, callback: Callable[[str, 'ObjectState'], None]) -> None:
        """Unsubscribe from ObjectState unregistration events."""
        if callback in cls._on_unregister_callbacks:
            cls._on_unregister_callbacks.remove(callback)

    @classmethod
    def add_time_travel_complete_callback(cls, callback: Callable[[List[Tuple[str, 'ObjectState']], Optional[str]], None]) -> None:
        """Subscribe to time-travel completion events.

        Callback receives (dirty_states, triggering_scope) where:
        - dirty_states: list of (scope_id, ObjectState) tuples with unsaved changes
        - triggering_scope: scope_id that triggered the snapshot (may be None)
        """
        if callback not in cls._on_time_travel_complete_callbacks:
            cls._on_time_travel_complete_callbacks.append(callback)

    @classmethod
    def remove_time_travel_complete_callback(cls, callback: Callable[[List[Tuple[str, 'ObjectState']], Optional[str]], None]) -> None:
        """Unsubscribe from time-travel completion events."""
        if callback in cls._on_time_travel_complete_callbacks:
            cls._on_time_travel_complete_callbacks.remove(callback)

    @classmethod
    def add_history_changed_callback(cls, callback: Callable[[], None]) -> None:
        """Subscribe to history change events (snapshot added or time-travel)."""
        if callback not in cls._on_history_changed_callbacks:
            cls._on_history_changed_callbacks.append(callback)

    @classmethod
    def remove_history_changed_callback(cls, callback: Callable[[], None]) -> None:
        """Unsubscribe from history change events."""
        if callback in cls._on_history_changed_callbacks:
            cls._on_history_changed_callbacks.remove(callback)

    @classmethod
    def _fire_history_changed_callbacks(cls) -> None:
        """Fire all history changed callbacks."""
        for callback in cls._on_history_changed_callbacks:
            try:
                callback()
            except Exception as e:
                logger.warning(f"Error in history_changed callback: {e}")

    @classmethod
    def _fire_register_callbacks(cls, scope_key: str, state: 'ObjectState') -> None:
        """Fire all registered callbacks for ObjectState registration."""
        for callback in cls._on_register_callbacks:
            try:
                callback(scope_key, state)
            except Exception as e:
                logger.warning(f"Error in register callback: {e}")

    @classmethod
    def _fire_unregister_callbacks(cls, scope_key: str, state: 'ObjectState') -> None:
        """Fire all registered callbacks for ObjectState unregistration."""
        for callback in cls._on_unregister_callbacks:
            try:
                callback(scope_key, state)
            except Exception as e:
                logger.warning(f"Error in unregister callback: {e}")

    @classmethod
    def _normalize_scope_id(cls, scope_id: Optional[str]) -> str:
        """Normalize scope_id: None and "" both represent global scope."""
        return scope_id if scope_id is not None else ""

    @classmethod
    def register(cls, state: 'ObjectState', _skip_snapshot: bool = False) -> None:
        """Register an ObjectState in the registry.

        Args:
            state: The ObjectState to register.
                   scope_id=None/"" for GlobalPipelineConfig (global scope).
                   scope_id=plate_path for PipelineConfig.
                   scope_id=plate_path::step_N for steps.
            _skip_snapshot: Internal flag for time-travel (don't record snapshot).
        """
        key = cls._normalize_scope_id(state.scope_id)

        if key in cls._states:
            logger.warning(f"Overwriting existing ObjectState for scope: {key}")

        cls._states[key] = state
        logger.debug(f"Registered ObjectState: scope={key}, type={type(state.object_instance).__name__}")

        # Fire callbacks for UI binding
        cls._fire_register_callbacks(key, state)

        # Record snapshot for time-travel (captures new ObjectState in registry)
        if not _skip_snapshot:
            cls.record_snapshot(f"register {type(state.object_instance).__name__}", key)

    @classmethod
    def unregister(cls, state: 'ObjectState', _skip_snapshot: bool = False) -> None:
        """Unregister an ObjectState from the registry.

        Args:
            state: The ObjectState to unregister.
            _skip_snapshot: Internal flag for time-travel (don't record snapshot).
        """
        key = cls._normalize_scope_id(state.scope_id)
        if key in cls._states:
            obj_type_name = type(state.object_instance).__name__
            removed_state = cls._states.pop(key)

            # Move to graveyard instead of deleting - enables time travel to past snapshots
            # that reference this ObjectState. Graveyard persists for session lifetime.
            cls._graveyard[key] = removed_state
            logger.debug(f"Unregistered ObjectState: scope={key} (moved to graveyard)")

            # Fire callbacks for UI binding
            cls._fire_unregister_callbacks(key, state)

            # Record snapshot for time-travel (captures ObjectState removal)
            if not _skip_snapshot:
                cls.record_snapshot(f"unregister {obj_type_name}", key)

    @classmethod
    def unregister_scope_and_descendants(cls, scope_id: Optional[str], _skip_snapshot: bool = False) -> int:
        """Unregister an ObjectState and all its descendants from the registry.

        This is used when deleting a plate - we need to cascade delete all child
        ObjectStates (steps, functions) to prevent memory leaks.

        Example:
            When deleting plate "/path/to/plate", this unregisters:
            - "/path/to/plate" (the plate's PipelineConfig)
            - "/path/to/plate::step_0" (step ObjectStates)
            - "/path/to/plate::step_0::func_0" (function ObjectStates)
            - etc.

        Args:
            scope_id: The scope to unregister (along with all descendants).
            _skip_snapshot: Internal flag for time-travel (don't record snapshot).

        Returns:
            Number of ObjectStates unregistered.
        """
        scope_key = cls._normalize_scope_id(scope_id)

        # Find all scopes to delete: exact match + descendants
        scopes_to_delete = []
        for key in cls._states.keys():
            # Exact match
            if key == scope_key:
                scopes_to_delete.append(key)
            # Descendant (starts with scope_key::)
            elif scope_key and key.startswith(scope_key + "::"):
                scopes_to_delete.append(key)

        # Delete all matching scopes and fire callbacks
        for key in scopes_to_delete:
            state = cls._states.pop(key)
            logger.debug(f"Unregistered ObjectState (cascade): scope={key}")
            # Fire callbacks for UI binding
            cls._fire_unregister_callbacks(key, state)

        if scopes_to_delete:
            logger.info(f"Cascade unregistered {len(scopes_to_delete)} ObjectState(s) for scope={scope_key}")
            # Record single snapshot for cascade unregister (captures all removals at once)
            if not _skip_snapshot:
                cls.record_snapshot(f"unregister_cascade ({len(scopes_to_delete)} scopes)", scope_key)

        return len(scopes_to_delete)

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
        """Clear all registered states, limbo, and graveyard. For testing only."""
        cls._states.clear()
        cls._time_travel_limbo.clear()
        cls._graveyard.clear()
        logger.debug("Cleared all ObjectStates from registry, limbo, and graveyard")

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

    @classmethod
    def get_ancestor_objects_with_scopes(cls, scope_id: Optional[str], use_saved: bool = False) -> List[Tuple[str, Any]]:
        """Get (scope_id, object) tuples from this scope and all ancestors.

        Similar to get_ancestor_objects() but includes the scope_id for each object.
        Used for provenance tracking to determine which scope provided a resolved value.

        Args:
            scope_id: The scope to get ancestors for (e.g., "/plate::step_0")
            use_saved: If True, return saved baseline (object_instance) instead of
                       live state (to_object()). Used when computing _saved_resolved.

        Returns:
            List of (scope_id, object) tuples from ancestor scopes, ordered least→most specific.
        """
        scope_key = cls._normalize_scope_id(scope_id)

        # Build list of ancestor scope keys (least-specific to most-specific)
        ancestors = [""]  # Global scope always included
        if scope_key:
            parts = scope_key.split("::")
            for i in range(len(parts)):
                ancestors.append("::".join(parts[:i+1]))

        # Get (scope_id, object) tuples from ancestor scopes
        results: List[Tuple[str, Any]] = []
        for ancestor_key in ancestors:
            state = cls._states.get(ancestor_key)
            if state:
                obj = state.object_instance if use_saved else state.to_object()
                results.append((ancestor_key, obj))

        return results

    # ========== SCOPE + TYPE + FIELD AWARE INVALIDATION ==========

    @classmethod
    def invalidate_by_type_and_scope(
        cls,
        scope_id: Optional[str],
        changed_type: type,
        field_name: str,
        invalidate_saved: bool = False
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
            invalidate_saved: If True, also invalidate saved_resolved cache for descendants
        """
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
        from openhcs.config_framework.dual_axis_resolver import invalidate_mro_cache_for_field

        # PERFORMANCE: Targeted cache invalidation - only clear entries for this field/type
        invalidate_mro_cache_for_field(changed_type, field_name)

        changed_scope = cls._normalize_scope_id(scope_id)

        # Normalize to base type for comparison (LazyX → X)
        base_changed_type = get_base_type_for_lazy(changed_type) or changed_type

        # DEBUG: Log invalidation for well_filter
        if field_name == 'well_filter':
            logger.debug(f"🔍 invalidate_by_type_and_scope: scope={changed_scope!r}, type={base_changed_type.__name__}, field={field_name}, total_states={len(cls._states)}")

        for state in cls._states.values():
            state_scope = cls._normalize_scope_id(state.scope_id)

            # SCOPE CHECK: must be at or below changed scope
            # Global scope (empty string) affects ALL states
            if changed_scope == "":
                # Global scope - always a descendant (or self if also global)
                if field_name == 'well_filter':
                    logger.debug(f"🔍   Checking state: scope={state_scope!r}, obj_type={type(state.object_instance).__name__}")
                logger.debug(f"[SCOPE] Global change affects state scope={state_scope!r}")
            else:
                # Non-global: check exact match or descendant
                is_self = (state_scope == changed_scope)
                prefix = changed_scope + "::"
                is_descendant = state_scope.startswith(prefix)
                if not (is_self or is_descendant):
                    logger.debug(f"[SCOPE] SKIP: changed_scope={changed_scope!r} does not affect state_scope={state_scope!r}")
                    continue
                logger.debug(f"[SCOPE] MATCH: changed_scope={changed_scope!r} affects state_scope={state_scope!r}")

            # TYPE + FIELD CHECK: find matching nested state and invalidate field
            cls._invalidate_field_in_matching_states(state, base_changed_type, field_name, invalidate_saved)

    @classmethod
    def _invalidate_field_in_matching_states(
        cls,
        state: 'ObjectState',
        target_base_type: type,
        field_name: str,
        invalidate_saved: bool = False
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
            invalidate_saved: If True, also invalidate saved_resolved cache for this field
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

                    # If invalidating saved baseline, remove from saved_resolved so it recomputes
                    if invalidate_saved and dotted_path in state._saved_resolved:
                        del state._saved_resolved[dotted_path]
                        logger.debug(f"Invalidated saved_resolved cache for {dotted_path}")

        # Trigger recompute immediately to detect if resolved values actually changed.
        # This ensures callbacks fire only when values change, not just when fields are invalidated.
        # Prevents false flashes when Reset is clicked on already-reset fields.
        if invalidated_paths:
            state._ensure_live_resolved(notify_flash=True)

            # If we invalidated saved baseline, recompute it now with fresh ancestor values
            if invalidate_saved:
                # Recompute entire saved_resolved snapshot to pick up new ancestor saved values
                old_saved_resolved = state._saved_resolved
                state._saved_resolved = state._compute_resolved_snapshot(use_saved=True)
                logger.debug(f"Recomputed saved_resolved baseline after invalidation")

                if old_saved_resolved != state._saved_resolved:
                    state._sync_materialized_state()
            else:
                state._sync_materialized_state()

    # ========== REGISTRY-LEVEL TIME-TRAVEL (DAG Model) ==========

    # Snapshots: Dict of all snapshots by ID (the DAG - snapshots are NEVER deleted)
    # Each Snapshot contains id, timestamp, label, triggering_scope, parent_id, all_states
    # The parent_id forms the DAG edges
    _snapshots: Dict[str, Snapshot] = {}

    # Current head: None = at branch head (live), snapshot_id = time-traveling to that snapshot
    _current_head: Optional[str] = None

    _history_enabled: bool = True
    _max_history_size: int = 1000  # Max snapshots in DAG (increased since we don't truncate branches)
    _in_time_travel: bool = False  # Flag for PFM to know to refresh widget values

    # Atomic operation state - when >0, snapshots are deferred until operation completes
    _atomic_depth: int = 0
    _atomic_label: Optional[str] = None  # Label for the coalesced snapshot

    # Limbo: ObjectStates temporarily removed during time-travel
    # When traveling to a snapshot, ObjectStates not in that snapshot are moved here.
    # When traveling forward or to head, they're restored from here.
    _time_travel_limbo: Dict[str, 'ObjectState'] = {}

    # Graveyard: ObjectStates that were unregistered (deleted) but may be needed for time travel
    # Unlike limbo (cleared on diverge), graveyard persists for the session lifetime.
    # This allows time travel to snapshots that reference deleted objects.
    _graveyard: Dict[str, 'ObjectState'] = {}

    # Timelines (branches): Named branches that point to a head snapshot
    # "main" is always created automatically on first snapshot
    # head_id always points to a valid key in _snapshots (guaranteed by construction)
    _timelines: Dict[str, Timeline] = {}
    _current_timeline: str = "main"

    @classmethod
    @contextmanager
    def atomic(cls, label: str) -> Generator[None, None, None]:
        """Context manager for atomic operations that should be a single undo step.

        All ObjectState changes within this context are coalesced into a single
        snapshot when the context exits. Nested atomic blocks are supported -
        only the outermost block records the snapshot.

        Example:
            with ObjectStateRegistry.atomic("add step"):
                # Register step ObjectState
                ObjectStateRegistry.register(step_state)
                # Update pipeline's step_scope_ids
                pipeline_state.update_parameter("step_scope_ids", new_ids)
                # Register function ObjectState
                ObjectStateRegistry.register(func_state)
            # Single snapshot recorded here with label "add step"

        Args:
            label: Human-readable label for the coalesced snapshot
        """
        cls._atomic_depth += 1
        if cls._atomic_depth == 1:
            cls._atomic_label = label

        try:
            yield
        finally:
            cls._atomic_depth -= 1
            if cls._atomic_depth == 0:
                # Outermost atomic block - record the coalesced snapshot
                final_label = cls._atomic_label or label
                cls._atomic_label = None
                cls.record_snapshot(final_label)

    @classmethod
    def get_branch_history(cls, branch_name: Optional[str] = None) -> List[Snapshot]:
        """Get ordered history for a branch by walking parent_id chain.

        Args:
            branch_name: Branch to get history for. If None, uses current branch.

        Returns:
            List of snapshots from oldest to newest (root first, head last).
            Index 0 = oldest (root), index -1 = newest (head).
            Empty list if branch has no snapshots yet.
        """
        if branch_name is None:
            branch_name = cls._current_timeline

        if branch_name not in cls._timelines:
            return []

        head_id = cls._timelines[branch_name].head_id
        history = []
        current_id: Optional[str] = head_id

        while current_id is not None:
            snapshot = cls._snapshots[current_id]  # KeyError if bug
            history.append(snapshot)
            current_id = snapshot.parent_id

        history.reverse()  # [oldest, ..., newest] - natural timeline order
        return history

    @classmethod
    def get_current_snapshot_index(cls) -> int:
        """Get current position as index into branch history.

        Returns:
            -1 if at head (live), else index into get_branch_history() list.
            Index 0 = oldest, len-1 = head.
        """
        if cls._current_head is None:
            return -1

        history = cls.get_branch_history()
        for i, snapshot in enumerate(history):
            if snapshot.id == cls._current_head:
                return i

        logger.error(f"⏱️ BRANCH: current_head {cls._current_head} not in branch history")
        return -1

    @classmethod
    def record_snapshot(cls, label: str = "", scope_id: Optional[str] = None) -> None:
        """Record current state of ALL ObjectStates to history.

        Called automatically after significant state changes.
        Each snapshot captures the full system state at a point in time.

        On FIRST edit, automatically records a baseline "init" snapshot first,
        so users can always go back to the original state before any edits.

        Args:
            label: Human-readable label (e.g., "edit group_by", "save")
            scope_id: Optional scope that triggered the snapshot (for labeling)
        """
        if not cls._history_enabled:
            return

        # CRITICAL: Don't record snapshots during time-travel
        if cls._in_time_travel:
            return

        # ATOMIC OPERATIONS: Defer snapshot until atomic block exits
        # The atomic() context manager will call record_snapshot() when it completes
        if cls._atomic_depth > 0:
            logger.debug(f"⏱️ ATOMIC: Deferring snapshot '{label}' (depth={cls._atomic_depth})")
            return

        import time

        # FIRST EDIT: Record baseline "init" snapshot before the actual edit snapshot
        is_first_snapshot = len(cls._snapshots) == 0
        if is_first_snapshot and label.startswith("edit"):
            cls._record_snapshot_internal("init", time.time(), None)

        full_label = f"{label} [{scope_id}]" if scope_id else label
        cls._record_snapshot_internal(full_label, time.time(), scope_id)

    @classmethod
    def _record_snapshot_internal(cls, label: str, timestamp: float, triggering_scope: Optional[str]) -> None:
        """Internal method to record a snapshot without baseline logic.

        DAG Model:
        - Snapshots are added to _snapshots dict (never deleted)
        - If _current_head is not None (time-traveling), we're diverging
        - On diverge: create auto-branch for old future, new snapshot parents from _current_head
        - Branch head_id is updated to point to new snapshot
        """
        import uuid

        # Capture ALL registered ObjectStates as StateSnapshot dataclasses
        all_states: Dict[str, StateSnapshot] = {}
        for key, state in cls._states.items():
            all_states[key] = StateSnapshot(
                saved_resolved=copy.deepcopy(state._saved_resolved),
                live_resolved=copy.deepcopy(state._live_resolved) if state._live_resolved else {},
                parameters=copy.deepcopy(state.parameters),
                saved_parameters=copy.deepcopy(state._saved_parameters),
                provenance=copy.deepcopy(state._live_provenance),
            )

        # Determine parent_id for new snapshot
        if cls._current_head is not None:
            # We're in the past - diverging from _current_head
            parent_id = cls._current_head

            # Auto-branch: preserve old future before we diverge
            # The old branch head becomes an auto-saved branch
            if cls._current_timeline in cls._timelines:
                old_head_id = cls._timelines[cls._current_timeline].head_id
                if old_head_id != cls._current_head:
                    # There IS an old future to preserve
                    branch_name = f"auto-{old_head_id[:8]}"
                    if branch_name not in cls._timelines:
                        cls._timelines[branch_name] = Timeline(
                            name=branch_name,
                            head_id=old_head_id,
                            base_id=cls._current_head,
                            description=f"Auto-saved from diverge at {cls._current_head[:8]}",
                        )
                        old_snapshot = cls._snapshots[old_head_id]
                        logger.info(f"⏱️ AUTO-BRANCH: Created '{branch_name}' (was {old_snapshot.label})")

            # Move limbo contents to graveyard before clearing - enables time travel
            # to any snapshot that references these states (even on other branches)
            cls._graveyard.update(cls._time_travel_limbo)
            cls._time_travel_limbo.clear()
        else:
            # At branch head - parent is current branch's head (if exists)
            if cls._current_timeline in cls._timelines:
                parent_id = cls._timelines[cls._current_timeline].head_id
            else:
                parent_id = None

        # Create new snapshot
        snapshot = Snapshot(
            id=str(uuid.uuid4()),
            timestamp=timestamp,
            label=label,
            triggering_scope=triggering_scope,
            parent_id=parent_id,
            all_states=all_states,
        )

        # Add to DAG
        cls._snapshots[snapshot.id] = snapshot

        # Update or create current branch to point to new snapshot
        if cls._current_timeline not in cls._timelines:
            cls._timelines[cls._current_timeline] = Timeline(
                name=cls._current_timeline,
                head_id=snapshot.id,
                base_id=snapshot.id,
                description="Main timeline" if cls._current_timeline == "main" else "",
            )
            logger.info(f"⏱️ BRANCH: Created '{cls._current_timeline}' timeline")
        else:
            cls._timelines[cls._current_timeline].head_id = snapshot.id

        # Return to head (live state) - we're no longer time-traveling
        cls._current_head = None

        # Enforce max DAG size (prune oldest snapshots not referenced by any branch)
        if len(cls._snapshots) > cls._max_history_size:
            cls._prune_unreachable_snapshots()

        logger.debug(f"⏱️ SNAPSHOT: Recorded '{label}' (id={snapshot.id[:8]})")
        cls._fire_history_changed_callbacks()

    @classmethod
    def _prune_unreachable_snapshots(cls) -> None:
        """Remove snapshots not reachable from any branch head.

        Walks from each branch head to find all reachable snapshots,
        then removes any that aren't reachable.
        """
        reachable: Set[str] = set()

        for timeline in cls._timelines.values():
            current_id: Optional[str] = timeline.head_id
            while current_id is not None and current_id not in reachable:
                reachable.add(current_id)
                snapshot = cls._snapshots.get(current_id)
                current_id = snapshot.parent_id if snapshot else None

        # Remove unreachable
        unreachable = set(cls._snapshots.keys()) - reachable
        for snapshot_id in unreachable:
            del cls._snapshots[snapshot_id]

        if unreachable:
            logger.debug(f"⏱️ PRUNE: Removed {len(unreachable)} unreachable snapshots")

    @classmethod
    def time_travel_to_snapshot(cls, snapshot_id: str) -> bool:
        """Travel ALL ObjectStates to a specific snapshot by ID.

        Full time-travel: ObjectStates are registered/unregistered to match the snapshot.
        ObjectStates not in the snapshot are moved to limbo. ObjectStates in snapshot
        but not in registry are restored from limbo.

        Args:
            snapshot_id: UUID of snapshot to travel to

        Returns:
            True if travel succeeded.
        """
        if snapshot_id not in cls._snapshots:
            logger.error(f"⏱️ TIME_TRAVEL: Snapshot {snapshot_id} not found")
            return False

        snapshot = cls._snapshots[snapshot_id]
        cls._current_head = snapshot_id

        # Set flag so PFM knows to refresh widget values
        cls._in_time_travel = True
        try:
            snapshot_scopes = set(snapshot.all_states.keys())
            current_scopes = set(cls._states.keys())

            # PHASE 1: UNREGISTER ObjectStates not in snapshot (move to limbo)
            scopes_to_limbo = current_scopes - snapshot_scopes
            for scope_key in scopes_to_limbo:
                state = cls._states.pop(scope_key)
                cls._time_travel_limbo[scope_key] = state
                cls._fire_unregister_callbacks(scope_key, state)
                logger.debug(f"⏱️ TIME_TRAVEL: Moved to limbo: {scope_key}")

            # PHASE 2: RE-REGISTER ObjectStates from limbo or graveyard
            # Track scopes restored in this phase - they shouldn't trigger window reopening
            scopes_restored_from_limbo: Set[str] = set()
            scopes_to_register = snapshot_scopes - current_scopes
            for scope_key in scopes_to_register:
                # Try limbo first (time-travel within session), then graveyard (deleted objects)
                if scope_key in cls._time_travel_limbo:
                    state = cls._time_travel_limbo.pop(scope_key)
                    logger.debug(f"⏱️ TIME_TRAVEL: Restored from limbo: {scope_key}")
                elif scope_key in cls._graveyard:
                    state = cls._graveyard.pop(scope_key)
                    logger.debug(f"⏱️ TIME_TRAVEL: Resurrected from graveyard: {scope_key}")
                else:
                    # This should not happen - snapshot references a scope we never had
                    logger.error(f"⏱️ TIME_TRAVEL: Cannot restore {scope_key} - not in limbo or graveyard")
                    continue
                cls._states[scope_key] = state
                cls._fire_register_callbacks(scope_key, state)
                scopes_restored_from_limbo.add(scope_key)

            # PHASE 3: RESTORE state for all ObjectStates in snapshot
            # Track which scopes need window reopening (for PHASE 4)
            scopes_needing_window: Set[str] = set()

            for scope_key, state_snap in snapshot.all_states.items():
                state = cls._states.get(scope_key)
                if not state:
                    continue

                # Was this scope just restored from limbo in PHASE 2?
                was_restored_from_limbo = scope_key in scopes_restored_from_limbo

                current_params = state.parameters.copy() if state.parameters else {}
                target_live = state_snap.live_resolved
                current_live = state._live_resolved.copy() if state._live_resolved else {}

                # Find changed resolved values
                changed_paths = set()
                all_keys = set(target_live.keys()) | set(current_live.keys())
                for key in all_keys:
                    if target_live.get(key) != current_live.get(key):
                        changed_paths.add(key)

                # Find changed raw parameters (ONLY leaf fields, skip container dataclasses)
                has_param_change = False
                changed_param_keys = []
                all_param_keys = set(state_snap.parameters.keys()) | set(current_params.keys())
                for param_key in all_param_keys:
                    before = current_params.get(param_key)
                    after = state_snap.parameters.get(param_key)
                    # Skip container dataclasses - they're structural, not editable values
                    if is_dataclass(before) or is_dataclass(after):
                        continue
                    if before != after:
                        changed_paths.add(param_key)
                        changed_param_keys.append((param_key, before, after))
                        has_param_change = True

                # Log param changes for debugging (but don't use to decide window opening)
                # Only scopes with CONCRETE unsaved work should open windows (see below)
                if has_param_change and not was_restored_from_limbo:
                    for pk, pv_before, pv_after in changed_param_keys:
                        logger.debug(f"⏱️ PARAM_CHANGE: {scope_key} param={pk} before={pv_before!r} after={pv_after!r}")

                # RESTORE state (including saved_parameters for concrete dirty detection)
                state._saved_resolved = copy.deepcopy(state_snap.saved_resolved)
                state._live_resolved = copy.deepcopy(state_snap.live_resolved)
                state._live_provenance = copy.deepcopy(state_snap.provenance)
                state.parameters = copy.deepcopy(state_snap.parameters)
                state._saved_parameters = copy.deepcopy(state_snap.saved_parameters)
                state._sync_materialized_state()

                # ALL scopes: include if CONCRETE dirty after restore (unsaved work exists)
                # Concrete dirty = parameters != saved_parameters (raw values, not resolved)
                is_concrete_dirty = state.parameters != state._saved_parameters
                if is_concrete_dirty:
                    # Log which params differ for debugging
                    for k in set(state.parameters.keys()) | set(state._saved_parameters.keys()):
                        p_val = state.parameters.get(k)
                        sp_val = state._saved_parameters.get(k)
                        if p_val != sp_val:
                            logger.debug(f"⏱️ CONCRETE_DIRTY: {scope_key} param={k} params={p_val!r} saved_params={sp_val!r}")
                    scopes_needing_window.add(scope_key)

                # Notify UI
                if changed_paths and state._on_resolved_changed_callbacks:
                    for callback in state._on_resolved_changed_callbacks:
                        callback(changed_paths)

            # PHASE 4: Fire time-travel completion callbacks
            # Reopen windows for states that:
            # - Had param changes during time travel, OR
            # - Have concrete unsaved work (parameters != saved_parameters)
            if cls._on_time_travel_complete_callbacks and scopes_needing_window:
                dirty_states = [
                    (scope_key, cls._states[scope_key])
                    for scope_key in scopes_needing_window
                    if scope_key in cls._states
                ]
                if dirty_states:
                    logger.debug(f"⏱️ TIME_TRAVEL: {len(dirty_states)} states needing window")
                    for callback in cls._on_time_travel_complete_callbacks:
                        callback(dirty_states, snapshot.triggering_scope)
        finally:
            cls._in_time_travel = False

        cls._fire_history_changed_callbacks()
        logger.info(f"⏱️ TIME_TRAVEL: Traveled to {snapshot.label} ({snapshot_id[:8]})")
        return True

    @classmethod
    def time_travel_to(cls, index: int) -> bool:
        """Travel to a snapshot by index in current branch history.

        Convenience method for UI sliders. Uses get_branch_history() to map
        index to snapshot_id.

        Args:
            index: Index into branch history (0 = oldest/root, -1 = newest/head)

        Returns:
            True if travel succeeded.
        """
        history = cls.get_branch_history()
        if not history:
            logger.warning("⏱️ TIME_TRAVEL: No history")
            return False

        # Normalize negative index
        if index < 0:
            index = len(history) + index

        if index < 0 or index >= len(history):
            logger.warning(f"⏱️ TIME_TRAVEL: Index {index} out of range [0, {len(history) - 1}]")
            return False

        # Index len-1 = head (newest), returning to head means exit time-travel
        if index == len(history) - 1:
            return cls.time_travel_to_head()

        snapshot = history[index]
        return cls.time_travel_to_snapshot(snapshot.id)

    @classmethod
    def time_travel_back(cls) -> bool:
        """Travel one step back in history (toward older/lower index)."""
        history = cls.get_branch_history()
        if not history:
            return False

        current_index = cls.get_current_snapshot_index()
        if current_index == -1:
            # At head (len-1) - go one step back
            if len(history) < 2:
                return False
            return cls.time_travel_to_snapshot(history[-2].id)

        # Already time-traveling - go one step older (lower index)
        if current_index <= 0:
            return False  # Already at oldest
        return cls.time_travel_to_snapshot(history[current_index - 1].id)

    @classmethod
    def time_travel_forward(cls) -> bool:
        """Travel one step forward in history (toward newer/higher index)."""
        if cls._current_head is None:
            return False  # Already at head

        history = cls.get_branch_history()
        current_index = cls.get_current_snapshot_index()

        # Go one step toward head (higher index)
        next_index = current_index + 1
        if next_index >= len(history) - 1:
            # At or past head - return to head
            return cls.time_travel_to_head()

        return cls.time_travel_to_snapshot(history[next_index].id)

    @classmethod
    def time_travel_to_head(cls) -> bool:
        """Return to the latest state (exit time-travel mode).

        Restores state from current branch's head snapshot.
        """
        if cls._current_head is None:
            return True  # Already at head

        if cls._current_timeline not in cls._timelines:
            logger.warning("⏱️ TIME_TRAVEL: No current timeline")
            return False

        head_id = cls._timelines[cls._current_timeline].head_id
        result = cls.time_travel_to_snapshot(head_id)
        cls._current_head = None  # Mark as at head (not time-traveling)
        return result

    @classmethod
    def get_history_info(cls) -> List[Dict[str, Any]]:
        """Get human-readable history for UI display.

        Returns history for current branch, oldest first (index 0 = oldest, -1 = head).
        """
        import datetime
        history = cls.get_branch_history()
        current_index = cls.get_current_snapshot_index()
        head_index = len(history) - 1

        result = []
        for i, snapshot in enumerate(history):
            is_head = (i == head_index)
            is_current = (current_index == -1 and is_head) or (i == current_index)
            result.append({
                'index': i,
                'id': snapshot.id,
                'timestamp': datetime.datetime.fromtimestamp(snapshot.timestamp).strftime('%H:%M:%S.%f')[:-3],
                'label': snapshot.label or f"Snapshot #{i}",
                'is_current': is_current,
                'is_head': is_head,
                'num_states': len(snapshot.all_states),
                'parent_id': snapshot.parent_id,
            })
        return result

    @classmethod
    def get_history_length(cls) -> int:
        """Get number of snapshots in current branch history."""
        return len(cls.get_branch_history())

    @classmethod
    def is_time_traveling(cls) -> bool:
        """Check if currently viewing historical state (not at head)."""
        return cls._current_head is not None

    # ========== BRANCH OPERATIONS ==========

    @classmethod
    def create_branch(cls, name: str, description: str = "") -> Timeline:
        """Create a new branch at current position.

        Args:
            name: Branch name (must be unique)
            description: Optional description

        Returns:
            The created Timeline
        """
        # Branch from current position
        if cls._current_head is not None:
            # Time-traveling - branch from current position
            head_id = cls._current_head
        elif cls._current_timeline in cls._timelines:
            # At head of current branch
            head_id = cls._timelines[cls._current_timeline].head_id
        else:
            logger.error("⏱️ BRANCH: No snapshots to branch from")
            raise ValueError("No snapshots to branch from")

        timeline = Timeline(
            name=name,
            head_id=head_id,
            base_id=head_id,
            description=description,
        )
        cls._timelines[name] = timeline
        logger.info(f"⏱️ BRANCH: Created branch '{name}' at {head_id[:8]}")
        return timeline

    @classmethod
    def switch_branch(cls, name: str) -> bool:
        """Switch to a different branch.

        Args:
            name: Branch name

        Returns:
            True if switch succeeded
        """
        timeline = cls._timelines[name]  # KeyError if branch doesn't exist

        # If we're back in time on current branch, preserve the old future as auto-branch
        # before switching (same logic as diverge in record_snapshot)
        if cls._current_head is not None and cls._current_timeline in cls._timelines:
            old_head_id = cls._timelines[cls._current_timeline].head_id
            if old_head_id != cls._current_head:
                # There IS an old future to preserve
                branch_name = f"auto-{old_head_id[:8]}"
                if branch_name not in cls._timelines:
                    cls._timelines[branch_name] = Timeline(
                        name=branch_name,
                        head_id=old_head_id,
                        base_id=cls._current_head,
                        description=f"Auto-saved before switch from {cls._current_timeline} at {cls._current_head[:8]}",
                    )
                    old_snapshot = cls._snapshots[old_head_id]
                    logger.info(f"⏱️ AUTO-BRANCH: Created '{branch_name}' before branch switch (was {old_snapshot.label})")

        # Switch to branch and travel to its head
        cls._current_timeline = name
        result = cls.time_travel_to_snapshot(timeline.head_id)
        cls._current_head = None  # At head of new branch
        cls._fire_history_changed_callbacks()
        logger.info(f"⏱️ BRANCH: Switched to '{name}'")
        return result

    @classmethod
    def delete_branch(cls, name: str) -> None:
        """Delete a branch.

        Args:
            name: Branch name to delete

        Note: Snapshots are not deleted - they may be reachable from other branches.
              Unreachable snapshots are pruned automatically when DAG exceeds max size.
        """
        del cls._timelines[name]  # KeyError if branch doesn't exist
        logger.info(f"⏱️ BRANCH: Deleted branch '{name}'")
        cls._fire_history_changed_callbacks()

    @classmethod
    def list_branches(cls) -> List[Dict[str, Any]]:
        """List all branches.

        Returns:
            List of dicts with branch info
        """
        return [
            {
                'name': tl.name,
                'head_id': tl.head_id,
                'base_id': tl.base_id,
                'description': tl.description,
                'is_current': tl.name == cls._current_timeline,
            }
            for tl in cls._timelines.values()
        ]

    @classmethod
    def get_current_branch(cls) -> str:
        """Get current branch name."""
        return cls._current_timeline

    # ========== PERSISTENCE ==========

    @classmethod
    def export_history_to_dict(cls) -> Dict[str, Any]:
        """Export history to a JSON-serializable dict.

        Returns:
            Dict with 'snapshots', 'timelines', 'current_head', 'current_timeline'.
        """
        return {
            'snapshots': {sid: snap.to_dict() for sid, snap in cls._snapshots.items()},
            'timelines': [tl.to_dict() for tl in cls._timelines.values()],
            'current_head': cls._current_head,
            'current_timeline': cls._current_timeline,
        }

    @classmethod
    def import_history_from_dict(cls, data: Dict[str, Any]) -> None:
        """Import history from a dict (e.g., loaded from JSON).

        Only imports state data for scope_ids that currently exist in the registry.
        Scopes in the snapshot but not in the app are skipped.

        Args:
            data: Dict with 'snapshots', 'timelines', 'current_head', 'current_timeline'.
        """
        cls._snapshots.clear()
        cls._timelines.clear()
        current_scopes = set(cls._states.keys())

        # Handle both old list format and new dict format
        snapshots_data = data['snapshots']
        if isinstance(snapshots_data, list):
            # Old format: list of snapshots
            snapshot_items = [(s['id'], s) for s in snapshots_data]
        else:
            # New format: dict of id -> snapshot
            snapshot_items = snapshots_data.items()

        for _snapshot_id, snapshot_data in snapshot_items:
            # Filter to only scopes that exist in current registry
            filtered_states: Dict[str, StateSnapshot] = {}
            for scope_id, state_data in snapshot_data['states'].items():
                if scope_id in current_scopes:
                    filtered_states[scope_id] = StateSnapshot(
                        saved_resolved=state_data['saved_resolved'],
                        live_resolved=state_data['live_resolved'],
                        parameters=state_data['parameters'],
                        saved_parameters=state_data.get('saved_parameters', state_data['parameters']),  # Fallback for old snapshots
                        provenance=state_data['provenance'],
                    )

            snapshot = Snapshot(
                id=snapshot_data['id'],
                timestamp=snapshot_data['timestamp'],
                label=snapshot_data['label'],
                triggering_scope=snapshot_data.get('triggering_scope'),
                parent_id=snapshot_data.get('parent_id'),
                all_states=filtered_states,
            )
            cls._snapshots[snapshot.id] = snapshot

        # Import timelines
        if 'timelines' in data:
            for tl_data in data['timelines']:
                tl = Timeline.from_dict(tl_data)
                cls._timelines[tl.name] = tl
            cls._current_timeline = data.get('current_timeline', 'main')
        else:
            cls._current_timeline = 'main'

        # Handle both old index format and new head format
        if 'current_head' in data:
            cls._current_head = data['current_head']
        elif 'current_index' in data:
            # Old format - convert index to head
            # Can't reliably convert, just go to head
            cls._current_head = None
        else:
            cls._current_head = None

    @classmethod
    def save_history_to_file(cls, filepath: str) -> None:
        """Save history to a JSON file.

        Args:
            filepath: Path to save the JSON file.
        """
        import json
        data = cls.export_history_to_dict()
        with open(filepath, 'w') as f:
            json.dump(data, f, indent=2)
        logger.info(f"⏱️ Saved {len(cls._snapshots)} snapshots to {filepath}")

    @classmethod
    def load_history_from_file(cls, filepath: str) -> None:
        """Load history from a JSON file.

        Args:
            filepath: Path to the JSON file.
        """
        import json
        with open(filepath, 'r') as f:
            data = json.load(f)
        cls.import_history_from_dict(data)
        logger.info(f"⏱️ Loaded {len(cls._snapshots)} snapshots from {filepath}")


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
        from typing import get_origin, get_args, Union
        origin = get_origin(field_type)
        if origin is Union:
            args = get_args(field_type)
            if len(args) == 2 and type(None) in args:
                inner_type = next(arg for arg in args if arg is not type(None))
                if is_dataclass(inner_type) and isinstance(inner_type, type):
                    return FieldProxy(self._state, new_path, inner_type)

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
    - dirty_fields → _live_resolved != _saved_resolved
    - signature_diff_fields → parameters != signature defaults
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

        # === Cache (3 attributes) ===
        self._live_resolved: Optional[Dict[str, Any]] = None  # None = needs full compute
        self._invalid_fields: Set[str] = set()  # Fields needing partial recompute
        # Maps dotted_path → (source_scope_id, source_type) for inherited fields
        # source_type may differ from local container_type due to MRO inheritance
        self._live_provenance: Dict[str, Tuple[Optional[str], Optional[type]]] = {}

        # === Saved baseline (2 attributes) ===
        self._saved_resolved: Dict[str, Any] = {}
        self._saved_parameters: Dict[str, Any] = {}  # Immutable snapshot for diff on restore

        # === Materialized diffs (2 attributes) ===
        self._dirty_fields: Set[str] = set()
        self._signature_diff_fields: Set[str] = set()

        # === Flags (kept for batch operations) ===
        self._in_reset = False
        self._block_cross_window_updates = False

        # === State Change Callbacks ===
        # Callbacks notified when materialized state changes (dirty/signature diffs)
        self._on_state_changed_callbacks: List[Callable[[], None]] = []

        # === Resolved Change Callbacks ===
        # Callbacks notified when resolved values actually change (for UI flashing)
        self._on_resolved_changed_callbacks: List[Callable[[Set[str]], None]] = []

        # === Time-Travel Callbacks ===
        # Callbacks notified when time-travel restores parameters (for widget refresh)
        self._on_time_travel_callbacks: List[Callable[[], None]] = []

        # === Time-Travel ===
        # Instance-level time-travel removed - use ObjectStateRegistry class-level DAG instead

        # Initialize baselines (suppress flash during init)
        self._ensure_live_resolved(notify_flash=False)
        assert self._live_resolved is not None  # Guaranteed by _ensure_live_resolved

        # CRITICAL: Initialize _saved_parameters BEFORE _compute_resolved_snapshot(use_saved=True)
        # because that method reads from _saved_parameters to get raw values.
        self._saved_parameters = copy.deepcopy(self.parameters)

        # CRITICAL: Compute saved_resolved using SAVED ancestor context, not LIVE.
        # This ensures saved baseline represents "what would this object's values be
        # if all ancestors were at their saved state", NOT "what are values right now
        # with ancestor's unsaved edits baked in".
        #
        # If we used copy.deepcopy(_live_resolved), we'd bake in ancestor's unsaved
        # edits, causing inverted dirty state when ancestor is saved/reset.
        self._saved_resolved = self._compute_resolved_snapshot(use_saved=True)

        # DEBUG: Log live vs saved at registration
        logger.debug(f"🔵 INIT_RESOLVED: scope={self.scope_id!r} obj_type={type(self.object_instance).__name__}")
        for k in sorted(self._live_resolved.keys()):
            live_val = self._live_resolved.get(k)
            saved_val = self._saved_resolved.get(k)
            if live_val != saved_val:
                logger.debug(f"🔵 INIT_DIFF: {k!r} live={live_val!r} saved={saved_val!r}")

        # Materialize initial diff sets (no notification during init)
        # Should be empty for new objects since saved = live
        self._dirty_fields = self._compute_dirty_fields()
        self._signature_diff_fields = self._compute_signature_diff_fields()

        # NOTE: Don't record "init" snapshot here - each ObjectState would create a separate
        # snapshot missing other ObjectStates created later. Instead, the first edit will
        # record the baseline state automatically (see record_snapshot logic).

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

    def on_state_changed(self, callback: Callable[[], None]) -> None:
        """Subscribe to materialized state change notifications (dirty/signature diffs)."""
        if callback not in self._on_state_changed_callbacks:
            self._on_state_changed_callbacks.append(callback)

    def off_state_changed(self, callback: Callable[[], None]) -> None:
        """Unsubscribe from materialized state change notifications."""
        if callback in self._on_state_changed_callbacks:
            self._on_state_changed_callbacks.remove(callback)

    def _notify_state_changed(self) -> None:
        """Fire state change callbacks (best-effort)."""
        for callback in list(self._on_state_changed_callbacks):
            try:
                callback()
            except Exception as e:
                logger.warning(f"Error in state_changed callback: {e}")

    def _ensure_live_resolved(self, notify_flash: bool = True) -> Set[str]:
        """Ensure _live_resolved cache is populated.

        PERFORMANCE: Field-level invalidation only.
        - First access: full compute to populate cache
        - After update_parameter(): only recompute invalid fields
        - Cross-window access: return cached values directly (no work)

        Args:
            notify_flash: If True, fire on_resolved_changed callbacks for flash animations.
                          Set to False during initialization to suppress flash.

        Returns:
            Set of paths that changed (for flash). Empty if no changes.

        NOTE: This method handles CACHE + FLASH only. Caller handles _sync_materialized_state().
        """
        # First access - populate cache
        if self._live_resolved is None:
            self._live_resolved = self._compute_resolved_snapshot()
            self._invalid_fields.clear()
            return set()  # First populate - no "changes" to flash

        # Partial recompute for invalid fields only
        if self._invalid_fields:
            changed_paths = self._recompute_invalid_fields()
            self._invalid_fields.clear()

            # Notify subscribers of which paths actually changed (flash events)
            if notify_flash and changed_paths and self._on_resolved_changed_callbacks:
                logger.debug(f"🔔 CALLBACK_LEAK_DEBUG: Notifying {len(self._on_resolved_changed_callbacks)} callbacks "
                            f"for scope={self.scope_id}, changed_paths={changed_paths}")
                for i, callback in enumerate(self._on_resolved_changed_callbacks):
                    try:
                        callback(changed_paths)
                    except RuntimeError as e:
                        # Qt widget was deleted - this indicates a leaked callback
                        logger.warning(f"🔴 CALLBACK_LEAK_DEBUG: Dead callback #{i} detected! "
                                     f"scope={self.scope_id}, error: {e}")
                    except Exception as e:
                        logger.warning(f"Error in resolved_changed callback #{i}: {e}")

            return changed_paths

        return set()  # No changes - cache was already valid

    # DELETED: _create_nested_states() - No longer needed with flat storage
    # Nested ObjectStates are no longer created - flat storage handles all parameters

    def _analyze_parameters(self, obj: Any, exclude_params: Optional[List[str]] = None) -> Dict[str, Any]:
        """Analyze object parameters using pure stdlib introspection.

        Returns dict mapping param_name -> info object with .param_type and .default_value attributes.

        Handles:
        - Dataclasses: uses dataclasses.fields()
        - Regular classes: walks MRO and analyzes __init__ signatures
        """
        import inspect
        from dataclasses import fields, MISSING
        from types import SimpleNamespace

        exclude_params = exclude_params or []
        result = {}

        obj_type = obj if isinstance(obj, type) else type(obj)

        if is_dataclass(obj_type):
            # Dataclass: use fields()
            for field in fields(obj_type):
                if field.name in exclude_params:
                    continue
                default = field.default if field.default is not MISSING else (
                    field.default_factory() if field.default_factory is not MISSING else None
                )
                result[field.name] = SimpleNamespace(
                    param_type=field.type,
                    default_value=default
                )
        else:
            # Non-dataclass: walk MRO and analyze __init__ signatures
            for cls in obj_type.__mro__:
                if cls is object:
                    continue
                if not hasattr(cls, '__init__') or cls.__init__ is object.__init__:
                    continue

                try:
                    sig = inspect.signature(cls.__init__)
                except (ValueError, TypeError):
                    continue

                for name, param in sig.parameters.items():
                    if name in ('self', 'cls', 'args', 'kwargs'):
                        continue
                    if name in exclude_params:
                        continue
                    if name in result:  # Already found in more specific class
                        continue

                    param_type = param.annotation if param.annotation is not inspect.Parameter.empty else Any
                    default = param.default if param.default is not inspect.Parameter.empty else None

                    result[name] = SimpleNamespace(
                        param_type=param_type,
                        default_value=default
                    )

        return result

    def _get_nested_dataclass_type(self, param_type: Any) -> Optional[type]:
        """Get the nested dataclass type if param_type is a nested dataclass.

        Args:
            param_type: The parameter type to check

        Returns:
            The dataclass type if nested, None otherwise
        """
        from typing import get_origin, get_args, Union

        # Check Optional[dataclass]
        origin = get_origin(param_type)
        if origin is Union:
            args = get_args(param_type)
            if len(args) == 2 and type(None) in args:
                inner_type = next(arg for arg in args if arg is not type(None))
                if is_dataclass(inner_type):
                    return inner_type

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
            logger.warning(
                f"⚠️ update_parameter({param_name!r}) called on ObjectState(scope={self.scope_id!r}) "
                f"but parameter does not exist. Available: {list(self.parameters.keys())[:5]}..."
            )
            return

        # EARLY EXIT: No change, no invalidation, no flash
        current_value = self.parameters[param_name]
        if current_value == value:
            return

        # Update state directly (no type conversion - that's VIEW responsibility)
        self.parameters[param_name] = value

        # SELF-INVALIDATION: Mark this field as needing recompute in our own cache
        self._invalid_fields.add(param_name)
        self._cached_object = None  # Invalidate cached reconstructed object

        # GLOBAL CONFIG EXCEPTION: Update LIVE thread-local FIRST, BEFORE invalidating descendants!
        # This is critical: descendants re-resolve during invalidation, so they need to see
        # the NEW value in the LIVE thread-local, not the old one.
        obj_type = type(self.object_instance)
        if getattr(obj_type, '_is_global_config', False):
            try:
                from openhcs.config_framework.global_config import set_live_global_config, get_live_global_config
                from openhcs.config_framework.context_manager import clear_current_temp_global
                from openhcs.config_framework.lazy_factory import replace_raw

                # Get current LIVE config
                current_live = get_live_global_config(obj_type)
                if current_live is not None:
                    # Do a quick partial update to set the new value in LIVE thread-local
                    if '.' in param_name:
                        # Nested field like 'well_filter_config.well_filter'
                        parts = param_name.split('.')
                        nested_config_name = parts[0]
                        nested_field_name = '.'.join(parts[1:])

                        # Get nested config using object.__getattribute__ to avoid lazy resolution
                        try:
                            nested_config = object.__getattribute__(current_live, nested_config_name)
                        except AttributeError:
                            nested_config = None

                        if nested_config is not None and is_dataclass(nested_config):
                            # Update the nested config with the new value
                            updated_nested = replace_raw(nested_config, **{nested_field_name: value})
                            # Update LIVE thread-local with the updated nested config
                            temp_live = replace_raw(current_live, **{nested_config_name: updated_nested})
                            set_live_global_config(obj_type, temp_live)
                    else:
                        # Top-level field
                        temp_live = replace_raw(current_live, **{param_name: value})
                        set_live_global_config(obj_type, temp_live)

                # Clear cached context so resolution uses updated LIVE thread-local
                clear_current_temp_global()

                # DEBUG: Log well_filter value
                if 'well_filter' in param_name:
                    verify_live = get_live_global_config(obj_type)
                    try:
                        wf_value = object.__getattribute__(verify_live.well_filter_config, 'well_filter')
                        logger.debug(f"🔍 LIVE thread-local updated BEFORE invalidation: {obj_type.__name__}.{param_name} = {value}, well_filter={wf_value}")
                    except:
                        pass
            except Exception as e:
                logger.warning(f"Failed to update LIVE thread-local: {e}")

        # SCOPE + TYPE + FIELD AWARE INVALIDATION:
        # Get the CONTAINER type for this field (e.g., WellFilterConfig for 'well_filter_config.well_filter')
        # This is critical for sibling inheritance: when WellFilterConfig.well_filter changes,
        # we need to invalidate PathPlanningConfig.well_filter (which inherits from WellFilterConfig)
        container_type = self._path_to_type.get(param_name, type(self.object_instance))

        # Extract leaf field name for invalidation matching
        leaf_field_name = param_name.split('.')[-1] if '.' in param_name else param_name

        # DEBUG: Log invalidation for well_filter
        if 'well_filter' in param_name:
            logger.debug(f"🔍 Invalidating descendants: scope={self.scope_id}, type={container_type.__name__}, field={leaf_field_name}")

        ObjectStateRegistry.invalidate_by_type_and_scope(
            scope_id=self.scope_id,
            changed_type=container_type,
            field_name=leaf_field_name
        )

        # Increment global token for LiveContextService.collect() cache invalidation
        ObjectStateRegistry.increment_token(notify=False)

        # Recompute live cache (flash events fire here)
        self._ensure_live_resolved(notify_flash=True)
        # Sync materialized state (single point for dirty/sig_diff update + notification)
        self._sync_materialized_state()

        # Record snapshot for time-travel (registry-level for coherent system history)
        # ONLY for LEAF fields - skip containers (dataclass instances that have nested params)
        # A field is a container if there are other params that start with "param_name."
        is_container = any(
            p.startswith(f"{param_name}.") for p in self.parameters.keys() if p != param_name
        )
        if not is_container:
            ObjectStateRegistry.record_snapshot(f"edit {param_name}", self.scope_id)

    def get_resolved_value(self, param_name: str) -> Any:
        """Get resolved value for a field from the bulk snapshot.

        Args:
            param_name: Field name to resolve (can be dotted path like 'path_planning_config.well_filter')

        Returns:
            Resolved value from _live_resolved snapshot
        """
        self._ensure_live_resolved()
        assert self._live_resolved is not None  # Guaranteed by _ensure_live_resolved
        result = self._live_resolved.get(param_name)

        # DEBUG: Log well_filter resolution
        if 'well_filter' in param_name:
            logger.debug(f"🔍 get_resolved_value: scope={self.scope_id!r}, obj_type={type(self.object_instance).__name__}, param={param_name}, value={result}")

        return result

    def get_provenance(self, param_name: str) -> Optional[Tuple[str, type]]:
        """Get the source scope_id and type for an inherited field value.

        For fields where the local value is None (inherited), returns the scope_id
        of the ancestor that provided the value AND the type that has it.
        Used for click-to-source navigation in the UI.

        The source_type may differ from the local container type due to MRO inheritance.
        For example, WellFilterConfig.well_filter might inherit from PathPlanningConfig.

        NOTE: Returns provenance even when the resolved value is None (signature default).
        A "concrete None" just means the class default is None and nothing overrode it.

        Args:
            param_name: Field name (can be dotted path like 'path_planning_config.well_filter')

        Returns:
            (source_scope_id, source_type): The scope and type that provided the value,
            or None if the value is local (not inherited).
        """
        self._ensure_live_resolved()
        result = self._live_provenance.get(param_name)
        if result is None:
            return None  # Field is local, not inherited
        scope_id, source_type = result
        if scope_id is None or source_type is None:
            return None  # Field not found in hierarchy (shouldn't happen)
        return (scope_id, source_type)

    def find_path_for_type(self, container_type: type) -> Optional[str]:
        """Find the path prefix for a container type in this ObjectState.

        With flat storage, nested configs are identified by their path prefix.
        Given a container type (e.g., PathPlanningConfig), returns the path prefix
        (e.g., 'path_planning_config').

        Handles type normalization: LazyPathPlanningConfig matches PathPlanningConfig.

        Args:
            container_type: The type to find the path for

        Returns:
            Path prefix for the type, or None if not found.
            Returns "" (empty string) if type is the root object type.
        """
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy

        # Normalize the container_type for comparison
        container_base = get_base_type_for_lazy(container_type) or container_type

        # Check if container_type matches the root object type
        root_type = type(self.object_instance)
        root_base = get_base_type_for_lazy(root_type) or root_type
        if container_base == root_base:
            return ""  # Root type has no prefix

        # Look for paths where the TYPE matches (normalized comparison)
        # The path for a nested config is the one WITHOUT a dot suffix that has the type
        for path, typ in self._path_to_type.items():
            typ_base = get_base_type_for_lazy(typ) or typ
            if typ_base == container_base and '.' not in path:
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
        self._live_provenance = {}  # Provenance must be recomputed with resolved values
        self._cached_object = None  # Also invalidate cached object

    def invalidate_self_and_nested(self) -> None:
        """Invalidate this state's cache.

        With flat storage, no nested states to invalidate.
        """
        self._live_resolved = None
        self._live_provenance = {}  # Provenance must be recomputed with resolved values
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
            # Safety check: skip any container entries that might have leaked in
            # (containers should NOT be in parameters — only leaf fields are tracked)
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
                logger.debug(
                    f"RECOMPUTE EXPLICIT CHANGED [{self.scope_id}] {name}: "
                    f"old={old_val!r} -> new={explicit_val!r}"
                )
            self._live_resolved[name] = explicit_val
            # Clear provenance for explicit values - they're no longer inherited
            if name in self._live_provenance:
                del self._live_provenance[name]

        # Inherited values: need context stack for lazy resolution + provenance
        if inherited_fields:
            from openhcs.config_framework.dual_axis_resolver import resolve_with_provenance

            # Use _with_scopes version to enable provenance tracking via context_layer_stack
            ancestor_objects_with_scopes = ObjectStateRegistry.get_ancestor_objects_with_scopes(self.scope_id)

            # CRITICAL: Use to_object() to get CURRENT state with user edits,
            # not object_instance which is the original/saved baseline.
            # This ensures sibling field inheritance sees updated values.
            current_obj = self.to_object()

            stack = build_context_stack(
                object_instance=current_obj,
                ancestor_objects_with_scopes=ancestor_objects_with_scopes,
                current_scope_id=self.scope_id,
            )

            with stack:
                # For each inherited field, resolve using dual-axis resolution with provenance
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

                    # Use resolve_with_provenance for SINGLE walk that gets both value AND source
                    value, source_scope_id, source_type = resolve_with_provenance(container_type, field_name)

                    old_val = self._live_resolved.get(dotted_path)
                    if old_val != value:
                        changed_paths.add(dotted_path)
                        logger.debug(
                            f"RECOMPUTE INHERITED CHANGED [{self.scope_id}] {dotted_path}: "
                            f"old={old_val!r} -> new={value!r}"
                        )
                    self._live_resolved[dotted_path] = value

                    # Update provenance for this field
                    self._live_provenance[dotted_path] = (source_scope_id, source_type)

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

    # ==================== MATERIALIZED DIFFS ====================

    @property
    def dirty_fields(self) -> Set[str]:
        """Fields where resolved_live != resolved_saved."""
        return self._dirty_fields

    @property
    def signature_diff_fields(self) -> Set[str]:
        """Fields where raw != signature_default."""
        return self._signature_diff_fields

    def _compute_dirty_fields(self) -> Set[str]:
        """Compute dirty set from live vs saved caches."""
        if self._live_resolved is None:
            return set()
        dirty = set()
        for k in (self._live_resolved.keys() | self._saved_resolved.keys()):
            live_val = self._live_resolved.get(k)
            saved_val = self._saved_resolved.get(k)
            if live_val != saved_val:
                dirty.add(k)
                logger.debug(f"🔴 DIRTY_FIELD: scope={self.scope_id!r} field={k!r} live={live_val!r} saved={saved_val!r}")
        if dirty:
            logger.debug(f"🔴 DIRTY_SUMMARY: scope={self.scope_id!r} dirty_fields={dirty}")
        return dirty

    def _compute_signature_diff_fields(self) -> Set[str]:
        """Compute signature-diff set from parameters vs defaults.

        Only includes LEAF fields (those with signature defaults).
        Nested dataclass container fields are excluded since they're not
        directly editable values.

        For non-dataclass roots (e.g. AbstractStep): only includes fields INSIDE nested
        dataclass configs (has '.' in path), not top-level attrs which are set explicitly.
        For dataclass roots: all fields are trackable.
        """
        obj = self.object_instance
        obj_type = obj if isinstance(obj, type) else type(obj)
        is_dataclass_root = is_dataclass(obj_type)

        return {
            k for k, v in self.parameters.items()
            if k in self._signature_defaults
            and (is_dataclass_root or '.' in k)  # dataclass: all fields; non-dataclass: only nested
            and v != self._signature_defaults[k]
        }

    def _update_dirty_fields(self) -> Set[str]:
        """Recompute _dirty_fields, return set of fields that changed dirty status.

        Returns fields that either became dirty OR became clean.
        Empty set means no change.
        """
        new_dirty = self._compute_dirty_fields()
        if new_dirty != self._dirty_fields:
            # Symmetric difference: fields that changed dirty status in either direction
            changed_fields = new_dirty ^ self._dirty_fields
            self._dirty_fields = new_dirty
            return changed_fields
        return set()

    def _update_signature_diff_fields(self) -> bool:
        """Recompute _signature_diff_fields, return True if changed."""
        new_sig_diff = self._compute_signature_diff_fields()
        if new_sig_diff != self._signature_diff_fields:
            self._signature_diff_fields = new_sig_diff
            return True
        return False

    def _sync_materialized_state(self) -> None:
        """Single point where materialized diffs are recomputed and notified.

        Call this after ANY mutation that could affect:
        - _live_resolved (affects dirty_fields)
        - _saved_resolved (affects dirty_fields)
        - parameters (affects signature_diff_fields)

        Correctness guarantee: All mutation paths call this ONE method.

        Flash behavior: Fires on_resolved_changed for fields that changed dirty status.
        This ensures flash animation triggers when fields become clean (not just dirty).
        """
        dirty_status_changed_fields = self._update_dirty_fields()
        sig_diff_changed = self._update_signature_diff_fields()

        # Fire flash for fields that changed dirty status (became dirty OR clean)
        if dirty_status_changed_fields and self._on_resolved_changed_callbacks:
            for callback in list(self._on_resolved_changed_callbacks):
                try:
                    callback(dirty_status_changed_fields)
                except Exception as e:
                    logger.warning(f"Error in resolved_changed callback during dirty sync: {e}")

        if dirty_status_changed_fields or sig_diff_changed:
            self._notify_state_changed()

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
        from openhcs.config_framework.dual_axis_resolver import resolve_with_provenance

        # Get ancestor objects WITH scope_ids for provenance tracking
        # use_saved=True returns object_instance (saved), False returns to_object() (live)
        ancestor_objects_with_scopes = ObjectStateRegistry.get_ancestor_objects_with_scopes(
            self.scope_id, use_saved=use_saved
        )

        # Use saved baseline or live state for this object
        if use_saved:
            current_obj = self.object_instance
        else:
            # CRITICAL: Use to_object() to get CURRENT state with user edits,
            # not object_instance which is the original/saved baseline.
            current_obj = self.to_object()

        # Build context stack ONCE with scope_ids for provenance tracking
        # CRITICAL: use_live must match use_saved to ensure global config layer
        # uses SAVED thread-local when computing saved baselines
        stack = build_context_stack(
            object_instance=current_obj,
            ancestor_objects_with_scopes=ancestor_objects_with_scopes,
            current_scope_id=self.scope_id,
            use_live=not use_saved,
        )

        snapshot: Dict[str, Any] = {}
        provenance: Dict[str, Tuple[Optional[str], Optional[type]]] = {}

        # CRITICAL: When computing saved_resolved, use _saved_parameters for raw values.
        # This ensures saved_resolved represents "what was last saved locally" + ancestor saved values,
        # NOT "current live edits resolved with saved ancestor context".
        # This is key for dirty detection: dirty = live_resolved != saved_resolved
        params_source = self._saved_parameters if use_saved else self.parameters

        # UNIFIED: Resolve ALL fields in single context stack
        # For each path, check if it has a lazy dataclass container type
        with stack:
            for dotted_path in self.parameters.keys():
                raw_value = params_source.get(dotted_path)
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
                    # Leaf field inside a lazy dataclass - resolve value AND provenance in ONE walk
                    # This handles both:
                    # - Nested fields (processing_config.group_by) where parts > 1
                    # - Top-level fields on root (num_workers on PipelineConfig) where parts == 1
                    field_name = parts[-1]

                    if raw_value is None:
                        # Field needs resolution - use combined resolve + provenance walk
                        resolved_val, source_scope, source_type = resolve_with_provenance(container_type, field_name)
                        snapshot[dotted_path] = resolved_val

                        # Track provenance for inherited values (live only)
                        # Store (scope_id, source_type) tuple so UI can find the correct path
                        if not use_saved:
                            provenance[dotted_path] = (source_scope, source_type)
                    else:
                        # Field has concrete local value - no resolution needed
                        resolved_val = raw_value
                        snapshot[dotted_path] = resolved_val

                    logger.debug(
                        f"SNAPSHOT [{self.scope_id}] {dotted_path}: "
                        f"raw={raw_value!r} -> resolved={resolved_val!r} (type={type(resolved_val).__name__})"
                    )
                else:
                    # Non-dataclass field - use raw value directly
                    snapshot[dotted_path] = raw_value

        # Store provenance for live resolution (not saved)
        if not use_saved:
            self._live_provenance = provenance

        return snapshot

    def mark_saved(self) -> None:
        """Mark current state as saved baseline.

        UNIFIED: Works for any object_instance type.

        CRITICAL: Invalidates descendant caches for any parameters that changed.
        This ensures that when saving, other windows that inherited from the
        old saved values get their caches invalidated so they pick up new values.
        This mirrors what restore_saved() does but in the opposite direction.

        Invalidation is based on comparing the OLD object_instance (about to be replaced)
        with the NEW self.parameters (live values used for reconstruction).
        """
        # Ensure live cache is populated for accurate dirty computation post-save
        self._ensure_live_resolved(notify_flash=False)

        # CRITICAL: Extract old values from object_instance BEFORE rebuilding it
        # These are the values that descendants might be inheriting from
        old_instance_values = {}
        if not isinstance(self.object_instance, type):
            # Extract raw attribute values from the old object_instance
            for param_name in self.parameters.keys():
                # Skip container entries (nested dataclass instances)
                if param_name in self.parameters:
                    raw_value = self.parameters.get(param_name)
                    is_container = raw_value is not None and is_dataclass(type(raw_value))
                    if is_container:
                        continue

                # Get the old value from object_instance by navigating dotted path
                try:
                    # Navigate through nested attributes for dotted paths
                    obj = self.object_instance
                    parts = param_name.split('.')
                    for part in parts:
                        obj = object.__getattribute__(obj, part)
                    old_instance_values[param_name] = obj
                except AttributeError:
                    # Field doesn't exist on object_instance, skip it
                    pass

        # Find parameters that differ between old object_instance and new live parameters
        # These are the fields that changed and need descendant invalidation
        changed_params = []
        for param_name in self.parameters.keys():
            # Skip container entries
            raw_value = self.parameters.get(param_name)
            is_container = raw_value is not None and is_dataclass(type(raw_value))
            if is_container:
                continue

            old_value = old_instance_values.get(param_name)
            new_value = self.parameters.get(param_name)
            if old_value != new_value:
                changed_params.append(param_name)

        # CRITICAL: Rebuild object_instance BEFORE invalidating descendants
        # Descendants will recompute using parent's object_instance, so it must have new values!
        if not isinstance(self.object_instance, type):
            # Update object_instance with current parameters
            # to_object() already handles all types uniformly
            self.object_instance = self.to_object()

        # Update saved parameters (after object_instance update, before invalidation)
        self._saved_parameters = copy.deepcopy(self.parameters)

        # NOW invalidate descendant caches AFTER object_instance is updated
        # This ensures descendants see the NEW object_instance when they recompute
        # CRITICAL: Also invalidate saved_resolved cache so descendants recompute their saved baseline
        for param_name in changed_params:
            container_type = self._path_to_type.get(param_name, type(self.object_instance))
            leaf_field_name = param_name.split('.')[-1] if '.' in param_name else param_name

            ObjectStateRegistry.invalidate_by_type_and_scope(
                scope_id=self.scope_id,
                changed_type=container_type,
                field_name=leaf_field_name,
                invalidate_saved=True  # Invalidate saved baseline for descendants
            )

        # Compute new saved resolved using SAVED ancestor baselines (use_saved=True)
        # This ensures saved baseline is computed relative to other saved baselines
        new_saved_resolved = self._compute_resolved_snapshot(use_saved=True)

        # Update saved resolved baseline
        self._saved_resolved = new_saved_resolved

        # Invalidate cached object so next to_object() call rebuilds
        self._cached_object = None

        # Sync materialized state (single point for dirty/sig_diff update + notification)
        self._sync_materialized_state()

        # Record snapshot for time-travel (registry-level) - ONLY if there were actual changes
        # This prevents no-op snapshots (e.g., saving a window where only sibling state changed)
        if changed_params:
            ObjectStateRegistry.record_snapshot("save", self.scope_id)

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
            self._sync_materialized_state()
            return

        # Find parameters that differ from saved baseline AND capture their container types
        # BEFORE clearing parameters (we need _path_to_type)
        changed_params_with_types = []
        for param_name, current_value in self.parameters.items():
            saved_value = self._saved_parameters.get(param_name)
            if current_value != saved_value:
                container_type = self._path_to_type.get(param_name, type(self.object_instance))
                leaf_field_name = param_name.split('.')[-1] if '.' in param_name else param_name
                changed_params_with_types.append((param_name, container_type, leaf_field_name))

        # Clear and re-extract from object_instance (the saved version)
        # CRITICAL: Pass exclude_params to ensure excluded fields stay excluded
        # Do this BEFORE invalidating descendants so they see restored values
        self.parameters.clear()
        self._path_to_type.clear()
        self._extract_all_parameters_flat(self.object_instance, prefix='', exclude_params=self._exclude_param_names)

        # CRITICAL: Also restore _saved_parameters to match current parameters
        # After restore, parameters == saved (both extracted from object_instance)
        self._saved_parameters = copy.deepcopy(self.parameters)

        self.invalidate_cache()

        # CRITICAL: Recompute _saved_resolved to match the restored state
        # Time travel may have overwritten _saved_resolved with snapshot values,
        # but after restore_saved(), _saved_resolved should reflect object_instance
        self._saved_resolved = self._compute_resolved_snapshot(use_saved=True)

        # NOW invalidate descendant caches for each changed parameter
        # This must happen AFTER restoring parameters so descendants see restored values
        for param_name, container_type, leaf_field_name in changed_params_with_types:
            ObjectStateRegistry.invalidate_by_type_and_scope(
                scope_id=self.scope_id,
                changed_type=container_type,
                field_name=leaf_field_name
            )

        # Emit on_resolved_changed for changed params so SAME-LEVEL observers flash
        # (e.g., list item subscribed to this ObjectState sees the revert as a change)
        if changed_params_with_types and self._on_resolved_changed_callbacks:
            changed_paths = {param_name for param_name, _, _ in changed_params_with_types}
            logger.debug(f"🔔 CALLBACK_LEAK_DEBUG: restore_saved notifying {len(self._on_resolved_changed_callbacks)} callbacks "
                        f"for scope={self.scope_id}, changed_paths={changed_paths}")
            for i, callback in enumerate(self._on_resolved_changed_callbacks):
                try:
                    callback(changed_paths)
                except RuntimeError as e:
                    # Qt widget was deleted - this indicates a leaked callback
                    logger.warning(f"🔴 CALLBACK_LEAK_DEBUG: Dead callback #{i} in restore_saved! "
                                 f"scope={self.scope_id}, error: {e}")
                except Exception as e:
                    logger.warning(f"Error in resolved_changed callback #{i} during restore: {e}")

        # Sync materialized state (single point for dirty/sig_diff update + notification)
        self._sync_materialized_state()

        # Record snapshot for time-travel (registry-level) - ONLY if there were changes
        if changed_params_with_types:
            ObjectStateRegistry.record_snapshot("restore", self.scope_id)

    def should_skip_updates(self) -> bool:
        """Check if updates should be skipped due to batch operations."""
        return self._in_reset or self._block_cross_window_updates

    # ==================== FLAT STORAGE METHODS (NEW) ====================

    def _extract_all_parameters_flat(self, obj: Any, prefix: str = '', exclude_params: Optional[List[str]] = None) -> None:
        """Recursively extract parameters into flat dict with dotted paths.

        Populates self.parameters and self._path_to_type with dotted path keys.

        Uses pluggable parameter analyzer if available, falls back to stdlib dataclass introspection.

        Args:
            obj: Object to extract from (dataclass instance OR regular object like FunctionStep)
            prefix: Current path prefix (e.g., 'well_filter_config')
            exclude_params: List of top-level parameter names to exclude
        """
        exclude_params = exclude_params or []
        obj_type = type(obj)
        is_function = obj_type.__name__ == 'function'

        # Try to use UnifiedParameterAnalyzer if available (OpenHCS), else fall back to stdlib
        param_info = self._analyze_parameters(obj, exclude_params if not prefix else [])

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
                # info.default_value is now guaranteed to be the CLASS signature default
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
        root_type = type(self.object_instance)
        for field_name in self._path_to_type:
            if '.' not in field_name:
                # Check if this field's TYPE is a dataclass (not the instance value)
                # We need to check the TYPE because the instance value might be stale
                # (e.g., self.parameters['well_filter_config'] might have well_filter=2
                # even though self.parameters['well_filter_config.well_filter'] = None)
                field_type = self._path_to_type.get(field_name)
                # CRITICAL FIX: _path_to_type stores CONTAINER type for leaf fields,
                # but FIELD type for nested dataclass fields. We must distinguish:
                # - If field_type == root_type, it's a leaf field (container type stored)
                # - If field_type != root_type AND is_dataclass, it's a nested dataclass
                is_nested_dataclass = (
                    field_type is not None and
                    is_dataclass(field_type) and
                    field_type != root_type  # Not the container type
                )
                if is_nested_dataclass:
                    # Nested dataclass: ALWAYS recursively reconstruct from flat storage
                    # This ensures we pick up changes to nested fields like 'well_filter_config.well_filter'
                    field_updates[field_name] = self._reconstruct_from_prefix(field_name)
                else:
                    # Primitive field: use value directly from parameters
                    value = self.parameters.get(field_name)
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
            obj_type = type(self.object_instance)
            for field_name, field_value in field_updates.items():
                # Skip read-only properties (those without setters)
                prop = getattr(obj_type, field_name, None)
                if isinstance(prop, property) and prop.fset is None:
                    continue
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
                # DEBUG
                if prefix == 'well_filter_config' and remainder == 'well_filter':
                    logger.debug(f"🔍 _reconstruct: Found direct field {prefix}.{remainder} = {value}")

        # Reconstruct nested dataclasses first
        for nested_name in nested_prefixes:
            nested_path = f'{prefix_dot}{nested_name}'
            nested_obj = self._reconstruct_from_prefix(nested_path)
            direct_fields[nested_name] = nested_obj

        # CRITICAL: Do NOT filter out None values!
        # In OpenHCS, None has semantic meaning: "inherit from parent context"
        # When a user explicitly resets a field to None, we MUST pass that None
        # to the dataclass constructor so lazy resolution can walk up the MRO.
        # Filtering None would cause the dataclass to use its class-level default
        # instead of the user's explicit None, breaking inheritance.

        # At root level, include excluded params (e.g., 'func' for FunctionStep)
        # These are required for construction but excluded from editing
        if not prefix:
            direct_fields.update(self._excluded_params)

        # DEBUG: Log what we're reconstructing
        if prefix == 'well_filter_config':
            logger.debug(f"🔍 _reconstruct_from_prefix: prefix={prefix}, direct_fields={direct_fields}")

        # Instantiate the dataclass with ALL fields including None values
        result = obj_type(**direct_fields)

        # DEBUG: Log the result
        if prefix == 'well_filter_config':
            raw_well_filter = object.__getattribute__(result, 'well_filter')
            logger.debug(f"🔍 _reconstruct_from_prefix: Reconstructed {prefix} with well_filter={raw_well_filter}")

        return result
