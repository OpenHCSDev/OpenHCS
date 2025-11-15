"""Mixin for widgets that consume cross-window ParameterFormManager updates."""

from __future__ import annotations

from typing import Any, Dict, Hashable, Optional, Set


class CrossWindowPreviewMixin:
    """Shared helpers for windows that respond to cross-window preview updates."""

    # Debounce delay for preview updates (ms)
    # Trailing debounce: timer restarts on each change, only executes after typing stops
    PREVIEW_UPDATE_DEBOUNCE_MS = 100

    def _init_cross_window_preview_mixin(self) -> None:
        self._preview_scope_map: Dict[str, Hashable] = {}
        self._pending_preview_keys: Set[Hashable] = set()
        self._preview_update_timer = None  # QTimer for debouncing preview updates

    # --- Scope mapping helpers -------------------------------------------------
    def set_preview_scope_mapping(self, scope_map: Dict[str, Hashable]) -> None:
        """Replace the scope->item mapping used for incremental updates."""
        self._preview_scope_map = dict(scope_map)

    def register_preview_scope(self, scope_id: Optional[str], item_key: Hashable) -> None:
        if scope_id:
            self._preview_scope_map[scope_id] = item_key

    def unregister_preview_scope(self, scope_id: Optional[str]) -> None:
        if scope_id and scope_id in self._preview_scope_map:
            del self._preview_scope_map[scope_id]

    # --- Event routing ---------------------------------------------------------
    def handle_cross_window_preview_change(
        self,
        field_path: Optional[str],
        new_value: Any,
        editing_object: Any,
        context_object: Any,
    ) -> None:
        """Shared handler to route cross-window updates to incremental refreshes.

        Uses trailing debounce: timer restarts on each change, only executes after
        changes stop for PREVIEW_UPDATE_DEBOUNCE_MS milliseconds.
        """
        import logging
        logger = logging.getLogger(__name__)

        if not self._should_process_preview_field(
            field_path, new_value, editing_object, context_object
        ):
            return

        scope_id = self._extract_scope_id_for_preview(editing_object, context_object)

        # Add affected items to pending set
        if scope_id in ("PIPELINE_CONFIG_CHANGE", "GLOBAL_CONFIG_CHANGE"):
            # Refresh ALL steps (add all indices to pending updates)
            all_indices = [idx for idx in self._preview_scope_map.values() if isinstance(idx, int)]
            for idx in all_indices:
                self._pending_preview_keys.add(idx)
        elif scope_id and scope_id in self._preview_scope_map:
            item_key = self._preview_scope_map[scope_id]
            self._pending_preview_keys.add(item_key)
        elif scope_id is None:
            # Unknown scope - trigger full refresh
            self._schedule_preview_update(full_refresh=True)
            return
        else:
            # Scope not in map - might be a new item or unrelated change
            return

        # Schedule debounced update (trailing debounce - restarts timer on each change)
        self._schedule_preview_update(full_refresh=False)

    def _schedule_preview_update(self, full_refresh: bool = False) -> None:
        """Schedule a debounced preview update.

        Trailing debounce: timer restarts on each call, only executes after
        calls stop for PREVIEW_UPDATE_DEBOUNCE_MS milliseconds.

        Args:
            full_refresh: If True, trigger full refresh instead of incremental
        """
        from PyQt6.QtCore import QTimer

        # Cancel existing timer if any (trailing debounce - restart on each change)
        if self._preview_update_timer is not None:
            self._preview_update_timer.stop()

        # Schedule new update after configured delay
        self._preview_update_timer = QTimer()
        self._preview_update_timer.setSingleShot(True)

        if full_refresh:
            self._preview_update_timer.timeout.connect(self._handle_full_preview_refresh)
        else:
            self._preview_update_timer.timeout.connect(self._process_pending_preview_updates)

        delay = max(0, self.PREVIEW_UPDATE_DEBOUNCE_MS)
        self._preview_update_timer.start(delay)

    # --- Hooks for subclasses --------------------------------------------------
    def _should_process_preview_field(
        self,
        field_path: Optional[str],
        new_value: Any,
        editing_object: Any,
        context_object: Any,
    ) -> bool:
        """Return True if a cross-window change should trigger a preview update."""
        raise NotImplementedError

    def _extract_scope_id_for_preview(
        self, editing_object: Any, context_object: Any
    ) -> Optional[str]:
        """Extract the relevant scope identifier from the editing/context objects."""
        raise NotImplementedError

    def _process_pending_preview_updates(self) -> None:
        """Apply incremental updates for all pending preview keys."""
        raise NotImplementedError

    def _handle_full_preview_refresh(self) -> None:
        """Fallback handler when incremental updates are not possible."""
        raise NotImplementedError
