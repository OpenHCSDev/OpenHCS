"""
Live context collection and registry service.

SIMPLIFIED ARCHITECTURE:
- Maintains registry of active form managers
- Token-based cache invalidation (increment on any change)
- External listeners just poll collect() on debounced timer
- NO complex signal wiring between managers
- NO field path matching - just "something changed, refresh"

This separation allows ParameterFormManager to focus solely on instance-level
form management while this service handles the cross-cutting coordination.
"""

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Type, TYPE_CHECKING
from weakref import WeakSet
import logging

if TYPE_CHECKING:
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
    from openhcs.config_framework import TokenCache

logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class LiveContextSnapshot:
    """Snapshot of live context values from all active form managers."""
    token: int
    values: Dict[type, Dict[str, Any]]
    scoped_values: Dict[str, Dict[type, Dict[str, Any]]] = field(default_factory=dict)


class LiveContextService:
    """
    Centralized service for live context collection and cross-window coordination.

    SIMPLIFIED: External listeners just need to:
    1. Call connect_listener(callback) once
    2. callback is called on any change (debounce in callback)
    3. callback calls collect() to get fresh values

    No N×N signal wiring. No field path matching. Just "something changed".
    """

    # Registry of all active form managers (WeakSet for automatic cleanup)
    _active_form_managers: WeakSet['ParameterFormManager'] = WeakSet()

    # Simple list of change callbacks - called on any change
    _change_callbacks: List[Callable[[], None]] = []

    # Live context token and cache for cross-window placeholder resolution
    _live_context_token_counter: int = 0
    _live_context_cache: Optional['TokenCache'] = None  # Initialized on first use

    # ========== TOKEN MANAGEMENT ==========

    @classmethod
    def get_token(cls) -> int:
        """Get current live context token."""
        return cls._live_context_token_counter

    @classmethod
    def increment_token(cls) -> None:
        """Increment token to invalidate all caches and notify listeners."""
        cls._live_context_token_counter += 1
        cls._notify_change()

    @classmethod
    def _notify_change(cls) -> None:
        """Notify all listeners that something changed."""
        for callback in cls._change_callbacks:
            try:
                callback()
            except Exception as e:
                logger.warning(f"Change callback failed: {e}")

    # ========== MANAGER REGISTRY ==========

    @classmethod
    def register(cls, manager: 'ParameterFormManager') -> None:
        """Register a form manager for cross-window updates."""
        cls._active_form_managers.add(manager)
        logger.debug(f"Registered manager: {manager.field_id} (total: {len(cls._active_form_managers)})")

    @classmethod
    def unregister(cls, manager: 'ParameterFormManager') -> None:
        """Unregister a form manager from cross-window updates."""
        cls._active_form_managers.discard(manager)
        cls.increment_token()  # Invalidate cache + notify listeners
        logger.debug(f"Unregistered manager: {manager.field_id} (total: {len(cls._active_form_managers)})")

    @classmethod
    def get_active_managers(cls) -> WeakSet['ParameterFormManager']:
        """Get all active form managers (read-only access)."""
        return cls._active_form_managers

    # ========== SIMPLE CHANGE LISTENER API ==========

    @classmethod
    def connect_listener(cls, callback: Callable[[], None]) -> None:
        """Connect a listener callback that's called on any change.

        The callback should debounce and call collect() to get fresh values.
        This replaces the complex external_listener/signal wiring.
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

    # ========== LIVE CONTEXT COLLECTION ==========

    @classmethod
    def collect(cls, scope_filter=None, for_type: Optional[Type] = None) -> LiveContextSnapshot:
        """
        Collect live context from all active form managers INCLUDING nested managers.

        Includes nested manager values to enable sibling inheritance via
        _find_live_values_for_type()'s issubclass matching.

        Args:
            scope_filter: Optional scope filter (e.g., 'plate_path' or 'x::y::z')
                         If None, collects from all scopes
            for_type: Optional type for hierarchy filtering. Only collects from
                      managers whose type is an ANCESTOR of for_type.

        Returns:
            LiveContextSnapshot with token and values dict
        """
        # Initialize cache on first use
        if cls._live_context_cache is None:
            from openhcs.config_framework import TokenCache, CacheKey
            cls._live_context_cache = TokenCache(lambda: cls._live_context_token_counter)

        from openhcs.config_framework import CacheKey
        from openhcs.config_framework.context_manager import is_ancestor_in_context, is_same_type_in_context

        for_type_name = for_type.__name__ if for_type else None
        cache_key = CacheKey.from_args(scope_filter, for_type_name)

        def compute_live_context() -> LiveContextSnapshot:
            """Recursively collect values from all managers and nested managers."""
            logger.info(f"📦 collect_live_context: COMPUTING (token={cls._live_context_token_counter}, scope={scope_filter}, for_type={for_type_name})")

            live_context = {}
            scoped_live_context = {}

            for manager in cls._active_form_managers:
                manager_type = type(manager.object_instance)
                manager_type_name = manager_type.__name__

                # HIERARCHY FILTER: Only collect from ancestors of for_type
                if for_type is not None:
                    if not (is_ancestor_in_context(manager_type, for_type) or is_same_type_in_context(manager_type, for_type)):
                        logger.info(f"  📋 SKIP {manager.field_id}: {manager_type_name} not ancestor/same-type of {for_type_name}")
                        continue

                # Apply scope filter if provided
                if scope_filter is not None and manager.scope_id is not None:
                    is_visible = cls._is_scope_visible(manager.scope_id, scope_filter)
                    logger.info(f"  📋 MANAGER {manager.field_id}: type={manager_type_name}, scope={manager.scope_id}, visible={is_visible}")
                    if not is_visible:
                        continue
                else:
                    logger.info(f"  📋 MANAGER {manager.field_id}: type={manager_type_name}, scope={manager.scope_id}, no_filter_or_no_scope")

                # Collect from this manager AND all its nested managers
                cls._collect_from_manager_tree(manager, live_context, scoped_live_context)

            collected_types = list(live_context.keys())
            logger.info(f"  📦 COLLECTED {len(collected_types)} types: {[t.__name__ for t in collected_types]}")
            token = cls._live_context_token_counter
            return LiveContextSnapshot(token=token, values=live_context, scoped_values=scoped_live_context)

        # Use token cache to get or compute
        snapshot = cls._live_context_cache.get_or_compute(cache_key, compute_live_context)

        if snapshot.token == cls._live_context_token_counter:
            logger.debug(f"✅ collect_live_context: CACHE HIT (token={cls._live_context_token_counter}, scope={scope_filter})")

        return snapshot

    @classmethod
    def _collect_from_manager_tree(cls, manager, result: dict, scoped_result: Optional[dict] = None) -> None:
        """Recursively collect values from manager and all nested managers."""
        if manager.dataclass_type:
            # Start with the manager's own user-modified values
            values = manager.get_user_modified_values()

            # CRITICAL: Merge nested manager values into parent's entry
            for field_name, nested in manager.nested_managers.items():
                if nested.dataclass_type:
                    nested_values = nested.get_user_modified_values()
                    if nested_values:
                        try:
                            values[field_name] = nested.dataclass_type(**nested_values)
                        except Exception:
                            pass  # Skip if reconstruction fails

            result[manager.dataclass_type] = values
            if scoped_result is not None and manager.scope_id:
                scoped_result.setdefault(manager.scope_id, {})[manager.dataclass_type] = result[manager.dataclass_type]

        # Recurse into nested managers
        for nested in manager.nested_managers.values():
            cls._collect_from_manager_tree(nested, result, scoped_result)

    @staticmethod
    def _is_scope_visible(manager_scope: str, filter_scope) -> bool:
        """Check if manager's scope is visible to the filter scope using root-based matching."""
        from openhcs.config_framework.context_manager import get_root_from_scope_key

        filter_scope_str = str(filter_scope) if not isinstance(filter_scope, str) else filter_scope
        manager_root = get_root_from_scope_key(manager_scope)
        filter_root = get_root_from_scope_key(filter_scope_str)

        # Empty root (global) is visible to all
        if not manager_root:
            return True

        return manager_root == filter_root

    # ========== GLOBAL REFRESH ==========

    @classmethod
    def trigger_global_refresh(cls) -> None:
        """Trigger cross-window refresh for all active form managers.

        Called when:
        - Config window saves/cancels (restore to saved state)
        - Code editor modifies config (apply code changes to UI)
        - Any bulk operation that affects multiple windows
        """
        from openhcs.pyqt_gui.widgets.shared.services.parameter_ops_service import ParameterOpsService

        logger.debug(f"🔄 GLOBAL_REFRESH: Triggering for {len(cls._active_form_managers)} managers")

        refresh_service = ParameterOpsService()
        for manager in cls._active_form_managers:
            try:
                refresh_service.refresh_with_live_context(manager, use_user_modified_only=False)
            except Exception as e:
                logger.warning(f"Failed to refresh manager {manager.field_id}: {e}")

        # Notify listeners via token increment
        cls.increment_token()

