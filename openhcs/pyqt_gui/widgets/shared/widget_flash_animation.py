"""Flash animation for form widgets (QLineEdit, QComboBox, etc.)."""

import logging
from typing import Optional
from PyQt6.QtCore import QTimer, QPropertyAnimation, QEasingCurve, pyqtProperty
from PyQt6.QtWidgets import QWidget
from PyQt6.QtGui import QColor, QPalette

from .scope_visual_config import ScopeVisualConfig

logger = logging.getLogger(__name__)


class WidgetFlashAnimator:
    """Manages flash animation for form widget background color changes.
    
    Uses QPropertyAnimation for smooth color transitions.
    """

    def __init__(self, widget: QWidget):
        """Initialize animator.

        Args:
            widget: Widget to animate
        """
        self.widget = widget
        self.config = ScopeVisualConfig()
        self._original_palette: Optional[QPalette] = None
        self._flash_timer: Optional[QTimer] = None
        self._is_flashing: bool = False

    def flash_update(self) -> None:
        """Trigger flash animation on widget background."""
        if not self.widget or not self.widget.isVisible():
            return
            
        if self._is_flashing:
            # Already flashing - restart timer
            if self._flash_timer:
                self._flash_timer.stop()
                self._flash_timer.start(self.config.FLASH_DURATION_MS)
            return

        self._is_flashing = True

        # Store original palette
        self._original_palette = self.widget.palette()

        # Apply flash color
        flash_palette = self.widget.palette()
        flash_color = QColor(*self.config.FLASH_COLOR_RGB, 100)
        flash_palette.setColor(QPalette.ColorRole.Base, flash_color)
        self.widget.setPalette(flash_palette)

        # Setup timer to restore original palette
        self._flash_timer = QTimer(self.widget)
        self._flash_timer.setSingleShot(True)
        self._flash_timer.timeout.connect(self._restore_palette)
        self._flash_timer.start(self.config.FLASH_DURATION_MS)

    def _restore_palette(self) -> None:
        """Restore original palette."""
        if self.widget and self._original_palette:
            self.widget.setPalette(self._original_palette)
        self._is_flashing = False


# Global registry of animators (keyed by widget id)
_widget_animators: dict[int, WidgetFlashAnimator] = {}


def flash_widget(widget: QWidget) -> None:
    """Flash a widget to indicate update.

    Args:
        widget: Widget to flash
    """
    config = ScopeVisualConfig()
    if not config.WIDGET_FLASH_ENABLED:
        return

    if not widget or not widget.isVisible():
        return

    widget_id = id(widget)

    # Get or create animator
    if widget_id not in _widget_animators:
        _widget_animators[widget_id] = WidgetFlashAnimator(widget)

    animator = _widget_animators[widget_id]
    animator.flash_update()


def cleanup_widget_animator(widget: QWidget) -> None:
    """Cleanup animator when widget is destroyed.

    Args:
        widget: Widget being destroyed
    """
    widget_id = id(widget)
    if widget_id in _widget_animators:
        animator = _widget_animators[widget_id]
        if animator._flash_timer and animator._flash_timer.isActive():
            animator._flash_timer.stop()
        del _widget_animators[widget_id]

