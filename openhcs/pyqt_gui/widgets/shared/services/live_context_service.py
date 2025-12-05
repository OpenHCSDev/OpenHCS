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
from typing import Any, Callable, Dict, List, Optional, TYPE_CHECKING
from weakref import WeakSet
import logging

if TYPE_CHECKING:
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
    from openhcs.config_framework import TokenCache

logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class LiveContextSnapshot:
    """Snapshot of live context values from all active form managers.

    Contains a single `scopes` dict organized by scope_id → type → values.
    Consumers apply their own filtering at consumption time:
    - Exact lookup: scopes.get(my_scope_id)
    - Ancestor merge: merge_ancestor_values(scopes, my_scope_id)
    """
    token: int
    scopes: Dict[str, Dict[type, Dict[str, Any]]] = field(default_factory=dict)


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
    def increment_token(cls, notify: bool = True) -> None:
        """Increment token to invalidate all caches.

        Args:
            notify: If True (default), notify all listeners of the change.
                   Set to False when you need to invalidate caches but will
                   notify listeners later (e.g., after sibling refresh completes).
        """
        cls._live_context_token_counter += 1
        if notify:
            cls._notify_change()

    @classmethod
    def _notify_change(cls) -> None:
        """Notify all listeners that something changed."""
        logger.info(f"🔔 _notify_change: notifying {len(cls._change_callbacks)} listeners")
        dead_callbacks = []
        for callback in cls._change_callbacks:
            try:
                callback_name = getattr(callback, '__name__', str(callback))
                callback_self = getattr(callback, '__self__', None)
                owner = type(callback_self).__name__ if callback_self else 'unknown'

                # Check if bound method's object has been deleted (PyQt C++ side)
                if callback_self is not None:
                    try:
                        from PyQt6 import sip
                        if sip.isdeleted(callback_self):
                            logger.debug(f"  ⚠️  Skipping deleted object: {owner}.{callback_name}")
                            dead_callbacks.append(callback)
                            continue
                    except (ImportError, TypeError):
                        pass  # sip not available or object not a Qt object

                logger.info(f"  📣 Calling listener: {owner}.{callback_name}")
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

    # ========== MANAGER REGISTRY ==========

    @classmethod
    def register(cls, manager: 'ParameterFormManager') -> None:
        """Register a form manager for cross-window updates."""
        cls._active_form_managers.add(manager)
        # Invalidate live context cache so newly opened windows build fresh snapshots
        cls.increment_token(notify=False)
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
    def collect(cls) -> LiveContextSnapshot:
        """
        Collect live context from ALL active form managers.

        No filtering at collection time - consumers apply their own filtering:
        - Exact lookup: snapshot.scopes.get(my_scope_id)
        - Ancestor merge: merge_ancestor_values(snapshot.scopes, my_scope_id)

        Returns:
            LiveContextSnapshot with token and scopes dict
        """
        from openhcs.config_framework.context_manager import get_dispatch_cache

        # PERFORMANCE OPTIMIZATION: Check dispatch cycle cache first
        dispatch_cache = get_dispatch_cache()
        if dispatch_cache is not None:
            dispatch_cache_key = ('live_context',)
            if dispatch_cache_key in dispatch_cache:
                logger.info("📦 collect_live_context: DISPATCH CACHE HIT")
                return dispatch_cache[dispatch_cache_key]

        # Initialize token cache on first use
        if cls._live_context_cache is None:
            from openhcs.config_framework import TokenCache, CacheKey
            cls._live_context_cache = TokenCache(lambda: cls._live_context_token_counter)

        from openhcs.config_framework import CacheKey
        cache_key = CacheKey.from_args()  # No params = single cache entry

        def compute_live_context() -> LiveContextSnapshot:
            """Collect values from all managers and nested managers."""
            logger.info(f"📦 collect_live_context: COMPUTING (token={cls._live_context_token_counter})")

            scopes: Dict[str, Dict[type, Dict[str, Any]]] = {}

            for manager in cls._active_form_managers:
                logger.debug(f"  📋 MANAGER {manager.field_id}: scope={manager.scope_id}")
                cls._collect_from_manager_tree(manager, scopes)

            scope_count = len(scopes)
            logger.info(f"  📦 COLLECTED {scope_count} scopes: {list(scopes.keys())}")
            return LiveContextSnapshot(token=cls._live_context_token_counter, scopes=scopes)

        # Use token cache to get or compute
        snapshot = cls._live_context_cache.get_or_compute(cache_key, compute_live_context)

        # Store in dispatch cache if available
        if dispatch_cache is not None:
            dispatch_cache[('live_context',)] = snapshot
            logger.debug("📦 collect_live_context: cached in dispatch cycle")

        if snapshot.token == cls._live_context_token_counter:
            logger.debug(f"✅ collect_live_context: CACHE HIT (token={cls._live_context_token_counter})")

        return snapshot

    @classmethod
    def _collect_from_manager_tree(cls, manager, scopes: Dict[str, Dict[type, Dict[str, Any]]]) -> None:
        """Recursively collect values from manager and all nested managers.

        Populates scopes dict: scope_id → type → values
        """
        if manager.object_instance:
            values = manager.get_user_modified_values()
            scope_id = manager.scope_id or ""
            scopes.setdefault(scope_id, {})[type(manager.object_instance)] = values

        # Recurse into nested managers
        for nested in manager.nested_managers.values():
            cls._collect_from_manager_tree(nested, scopes)

    # ========== CONSUMPTION-TIME HELPERS ==========

    @staticmethod
    def merge_ancestor_values(
        scopes: Dict[str, Dict[type, Dict[str, Any]]],
        my_scope: str,
    ) -> Dict[type, Dict[str, Any]]:
        """Merge values from ancestor scopes for placeholder resolution.

        Walks scopes from least-specific to most-specific, merging values.
        More-specific values overwrite less-specific ones (proper precedence).

        Args:
            scopes: The scopes dict from LiveContextSnapshot
            my_scope: The consumer's scope_id (e.g., "/path/to/plate::step_0")

        Returns:
            Dict[type, Dict[str, Any]] merged values for context stack building
        """
        result: Dict[type, Dict[str, Any]] = {}

        # Build list of ancestor scopes (least-specific to most-specific)
        # e.g., "/path/to/plate::step_0" -> ["", "/path/to/plate", "/path/to/plate::step_0"]
        ancestors = [""]  # Global scope always included
        if my_scope:
            parts = my_scope.split("::")
            for i in range(len(parts)):
                ancestors.append("::".join(parts[:i+1]))

        # Merge in order (less-specific first, more-specific overwrites)
        for ancestor_scope in ancestors:
            scope_data = scopes.get(ancestor_scope, {})
            for config_type, values in scope_data.items():
                if config_type not in result:
                    result[config_type] = {}
                result[config_type].update(values)

        return result

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
                refresh_service.refresh_with_live_context(manager)
            except Exception as e:
                logger.warning(f"Failed to refresh manager {manager.field_id}: {e}")

        # Notify listeners via token increment
        cls.increment_token()
