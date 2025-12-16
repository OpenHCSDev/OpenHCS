"""
ObjectStateRegistry: Singleton registry of all ObjectState instances.

Replaces LiveContextService._active_form_managers as the single source of truth
for all configuration state. Keyed by scope_id for efficient lookup.

Lifecycle ownership:
- PipelineEditor: registers when step added, unregisters when step removed
- ImageBrowser: registers when opened, unregisters when closed
- Config window: registers PipelineConfig/GlobalPipelineConfig

Thread safety: Not thread-safe (all operations expected on main thread).
"""
from dataclasses import is_dataclass, fields as dataclass_fields
import logging
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, TYPE_CHECKING
import copy

from openhcs.config_framework.snapshot_model import Snapshot, StateSnapshot, Timeline

if TYPE_CHECKING:
    from openhcs.config_framework.object_state import ObjectState

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
            del cls._states[key]
            logger.debug(f"Unregistered ObjectState: scope={key}")

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

    # Limbo: ObjectStates temporarily removed during time-travel
    # When traveling to a snapshot, ObjectStates not in that snapshot are moved here.
    # When traveling forward or to head, they're restored from here.
    _time_travel_limbo: Dict[str, 'ObjectState'] = {}

    # Timelines (branches): Named branches that point to a head snapshot
    # "main" is always created automatically on first snapshot
    # head_id always points to a valid key in _snapshots (guaranteed by construction)
    _timelines: Dict[str, Timeline] = {}
    _current_timeline: str = "main"

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

            # Clear limbo when diverging
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

            # PHASE 2: RE-REGISTER ObjectStates from limbo
            scopes_to_register = snapshot_scopes - current_scopes
            for scope_key in scopes_to_register:
                state = cls._time_travel_limbo.pop(scope_key)  # KeyError if bug
                cls._states[scope_key] = state
                cls._fire_register_callbacks(scope_key, state)
                logger.debug(f"⏱️ TIME_TRAVEL: Restored from limbo: {scope_key}")

            # PHASE 3: RESTORE state for all ObjectStates in snapshot
            for scope_key, state_snap in snapshot.all_states.items():
                state = cls._states.get(scope_key)
                if not state:
                    continue

                current_params = state.parameters.copy() if state.parameters else {}
                target_live = state_snap.live_resolved
                current_live = state._live_resolved.copy() if state._live_resolved else {}

                # Find changed resolved values
                changed_paths = set()
                all_keys = set(target_live.keys()) | set(current_live.keys())
                for key in all_keys:
                    if target_live.get(key) != current_live.get(key):
                        changed_paths.add(key)

                # Find changed raw parameters
                all_param_keys = set(state_snap.parameters.keys()) | set(current_params.keys())
                for param_key in all_param_keys:
                    before = current_params.get(param_key)
                    after = state_snap.parameters.get(param_key)
                    if before != after and not (is_dataclass(before) or is_dataclass(after)):
                        changed_paths.add(param_key)

                # RESTORE state
                state._saved_resolved = copy.deepcopy(state_snap.saved_resolved)
                state._live_resolved = copy.deepcopy(state_snap.live_resolved)
                state._live_provenance = copy.deepcopy(state_snap.provenance)
                state.parameters = copy.deepcopy(state_snap.parameters)
                state._sync_materialized_state()

                # Notify UI
                if changed_paths and state._on_resolved_changed_callbacks:
                    for callback in state._on_resolved_changed_callbacks:
                        callback(changed_paths)

            # PHASE 4: Fire time-travel completion callbacks
            if cls._on_time_travel_complete_callbacks:
                dirty_states = [
                    (scope_key, state)
                    for scope_key, state in cls._states.items()
                    if state.dirty_fields
                ]
                if dirty_states:
                    logger.debug(f"⏱️ TIME_TRAVEL: {len(dirty_states)} dirty states")
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


