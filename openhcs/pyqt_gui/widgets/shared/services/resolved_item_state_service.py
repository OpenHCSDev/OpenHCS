"""
Reactive flash/dirty service for list items.

REGISTRY REFACTOR: Listens to ContextStackRegistry.value_changed instead of
ParameterFormManager.context_value_changed.

Architecture:
- Listens to registry.value_changed (scope_id, field_path, old_value, new_value)
- Uses scope visibility rules to filter which items are affected
- ANY change in visible scope triggers flash - no field tracking needed
- Lazydataclass inheritance handles field propagation automatically
- Dirty tracking via registry.get_resolved_state() comparison to baseline

Usage:
    service = ResolvedItemStateService.instance()

    # Register item scope (no field list - automatic via lazydataclass)
    service.register_item(scope_id)

    # Set baseline for dirty tracking
    service.set_baseline(scope_id)

    # Values come in via registry.value_changed - flash if scope visible
"""

from typing import Any, Optional, Set, Dict
import logging

from PyQt6.QtCore import QObject, pyqtSignal

logger = logging.getLogger(__name__)


class ResolvedItemStateService(QObject):
    """Reactive service that flashes items when visible scope changes.

    REGISTRY REFACTOR: Uses ContextStackRegistry as single source of truth.
    NO field tracking - lazydataclass inheritance handles propagation.
    """

    _instance: Optional['ResolvedItemStateService'] = None

    # Signals
    item_resolved_changed = pyqtSignal(str, str, object)  # scope_id, field_name, new_value
    item_dirty_changed = pyqtSignal(str, bool)  # scope_id, is_dirty

    def __init__(self):
        super().__init__()
        # Registered scope_ids
        self._registrations: Set[str] = set()

        # Baselines for dirty tracking (scope_id -> resolved state dict)
        self._baselines: Dict[str, Dict[str, Any]] = {}

        # REGISTRY REFACTOR: Connect to registry.value_changed
        from openhcs.config_framework import ContextStackRegistry
        registry = ContextStackRegistry.instance()
        registry.value_changed.connect(self._on_registry_value_changed)
        logger.info("🔗 Connected to ContextStackRegistry.value_changed")

    @classmethod
    def instance(cls) -> 'ResolvedItemStateService':
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance

    @classmethod
    def reset_instance(cls) -> None:
        """Reset singleton for testing."""
        cls._instance = None

    # --- Registration ---

    def register_item(self, scope_id: str) -> None:
        """Register a list item scope for flash tracking."""
        self._registrations.add(scope_id)
        logger.debug(f"📦 Registered scope: {scope_id}")

    def unregister_item(self, scope_id: str) -> None:
        """Unregister item when removed from list."""
        self._registrations.discard(scope_id)
        self._baselines.pop(scope_id, None)

    def set_baseline(self, scope_id: str) -> None:
        """Set baseline for dirty tracking.

        REGISTRY REFACTOR: Captures current resolved state from registry.
        Call this after save, load, or when item is first registered.
        """
        from openhcs.config_framework import ContextStackRegistry

        registry = ContextStackRegistry.instance()
        baseline = registry.get_resolved_state(scope_id)
        if baseline is not None:
            self._baselines[scope_id] = baseline
            logger.debug(f"� Set baseline for {scope_id}: {len(baseline)} fields")
            # Check if dirty status changed
            self._check_dirty_status(scope_id)

    def _on_registry_value_changed(self, scope_id: str, field_path: str,
                                    old_value: Any, new_value: Any) -> None:
        """Handle registry value change - flash and check dirty status.

        REGISTRY REFACTOR: Listens to ContextStackRegistry.value_changed.
        """
        # Extract leaf field name
        field_name = field_path.split('.')[-1]

        # Flash all registered items where scope is visible
        for registered_scope_id in self._registrations:
            if self._is_scope_visible(scope_id, registered_scope_id):
                logger.info(f"⚡ Flash {registered_scope_id} (field={field_name})")
                self.item_resolved_changed.emit(registered_scope_id, field_name, new_value)

                # Check dirty status for this item
                self._check_dirty_status(registered_scope_id)

    def _check_dirty_status(self, scope_id: str) -> None:
        """Check if scope is dirty compared to baseline and emit signal if changed."""
        from openhcs.config_framework import ContextStackRegistry

        if scope_id not in self._baselines:
            return  # No baseline set yet

        registry = ContextStackRegistry.instance()
        current_state = registry.get_resolved_state(scope_id)
        if current_state is None:
            return

        baseline = self._baselines[scope_id]
        is_dirty = current_state != baseline

        # Emit signal (AbstractManagerWidget will update display)
        self.item_dirty_changed.emit(scope_id, is_dirty)
        logger.debug(f"Dirty check {scope_id}: {is_dirty}")

    def _is_scope_visible(self, editing_scope_id: str, target_scope_id: str) -> bool:
        """Check if edits from editing_scope_id should affect target_scope_id.

        Uses the same visibility rules as ParameterFormManager.
        """
        from openhcs.config_framework.context_manager import get_root_from_scope_key

        # Global config edits affect everything
        if 'Global' in editing_scope_id:
            return True

        # Same scope
        if editing_scope_id == target_scope_id:
            return True

        # Same root (same plate)
        editing_root = get_root_from_scope_key(editing_scope_id)
        target_root = get_root_from_scope_key(target_scope_id)

        if editing_root and target_root:
            return editing_root == target_root

        return False

    def clear_all(self) -> None:
        """Clear all state. Called on pipeline close/reset."""
        self._registrations.clear()
        logger.debug("Cleared all registrations")

