"""Mixin for widgets that consume cross-window ParameterFormManager updates.

SIMPLIFIED ARCHITECTURE:
- Listen for any change via LiveContextService.connect_listener()
- Debounce + full refresh (no complex field path matching)
- Use LiveContextService.collect() to get fresh values
"""

from __future__ import annotations

from abc import abstractmethod
from typing import Any, Callable, Dict, Optional, Set
import logging

logger = logging.getLogger(__name__)


class CrossWindowPreviewMixin:
    """Helpers for widgets that respond to cross-window preview updates.

    SIMPLIFIED: Any change triggers a debounced full refresh.
    No complex field path matching - just refresh everything.

    Usage:
        class MyWidget(QWidget, CrossWindowPreviewMixin):
            def __init__(self):
                super().__init__()
                self._init_cross_window_preview_mixin()

                # Configure which fields to show in previews
                self.enable_preview_for_field('napari_streaming_config',
                                             format_streaming_indicator)

                # Implement _handle_full_preview_refresh()...
    """

    # Debounce delay for preview updates (ms)
    PREVIEW_UPDATE_DEBOUNCE_MS = 100

    def _init_cross_window_preview_mixin(self) -> None:
        self._preview_update_timer = None  # QTimer for debouncing

        # Per-widget preview field configuration: field_path -> formatter function
        self._preview_fields: Dict[str, Callable] = {}
        self._preview_field_fallbacks: Dict[str, Callable] = {}

        # Connect to LiveContextService for change notifications
        from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
        LiveContextService.connect_listener(self._on_live_context_changed)

    def _on_live_context_changed(self) -> None:
        """Called when any live context value changes. Schedules debounced refresh."""
        self._schedule_preview_update()

    # --- Preview field configuration -------------------------------------------
    def enable_preview_for_field(
        self,
        field_path: str,
        formatter: Optional[Callable[[Any], str]] = None,
        *,
        scope_root: Optional[str] = None,  # kept for API compat, ignored
        fallback_resolver: Optional[Callable[[Any, Dict[str, Any]], Any]] = None,
    ) -> None:
        """Enable preview label for a specific field.

        Args:
            field_path: Dot-separated field path (e.g., 'napari_streaming_config')
            formatter: Optional formatter function. If None, uses str().
            scope_root: IGNORED (kept for backward compatibility)
            fallback_resolver: Optional resolver for computing value from context
        """
        self._preview_fields[field_path] = formatter or str
        if fallback_resolver:
            self._preview_field_fallbacks[field_path] = fallback_resolver

    def disable_preview_for_field(self, field_path: str) -> None:
        """Disable preview label for a specific field."""
        self._preview_fields.pop(field_path, None)
        self._preview_field_fallbacks.pop(field_path, None)

    def is_preview_enabled(self, field_path: str) -> bool:
        """Check if preview is enabled for a specific field."""
        return field_path in self._preview_fields

    def format_preview_value(self, field_path: str, value: Any) -> str:
        """Format a value for preview display using the registered formatter."""
        formatter = self._preview_fields.get(field_path, str)
        try:
            return formatter(value)
        except Exception:
            return str(value)

    def get_enabled_preview_fields(self) -> Set[str]:
        """Get the set of all enabled preview field paths."""
        return set(self._preview_fields.keys())

    def _apply_preview_field_fallback(
        self, field_path: str, context: Optional[Dict[str, Any]] = None
    ) -> Any:
        """Apply fallback resolver for a preview field if registered."""
        fallback = self._preview_field_fallbacks.get(field_path)
        if fallback and context:
            return fallback(self, context)
        return None

    # --- Debounced refresh ---
    def _schedule_preview_update(self) -> None:
        """Schedule a debounced full preview refresh."""
        from PyQt6.QtCore import QTimer

        # Cancel existing timer (trailing debounce - restart on each change)
        if self._preview_update_timer is not None:
            self._preview_update_timer.stop()

        # Schedule new update after configured delay
        self._preview_update_timer = QTimer()
        self._preview_update_timer.setSingleShot(True)
        self._preview_update_timer.timeout.connect(self._handle_full_preview_refresh)
        self._preview_update_timer.start(max(0, self.PREVIEW_UPDATE_DEBOUNCE_MS))


    @abstractmethod
    def _handle_full_preview_refresh(self) -> None:
        """Subclasses must implement this to refresh all previews."""
        raise NotImplementedError
