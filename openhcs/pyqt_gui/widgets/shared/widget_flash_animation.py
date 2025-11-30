"""Flash animation for form widgets (QLineEdit, QComboBox, etc.)."""

import logging
from typing import Optional
from PyQt6.QtWidgets import QWidget, QGroupBox
from PyQt6.QtGui import QColor, QPalette

from .smooth_flash_base import SmoothFlashAnimatorBase
from .scope_visual_config import ScopeVisualConfig

logger = logging.getLogger(__name__)


class WidgetFlashAnimator(SmoothFlashAnimatorBase):
    """Smooth flash animation for form widget background color changes.

    Uses stylesheet manipulation for GroupBox (since stylesheets override palettes),
    and palette manipulation for input widgets.
    """

    def __init__(self, widget: QWidget, flash_color: Optional[QColor] = None):
        """Initialize animator.

        Args:
            widget: Widget to animate
            flash_color: Optional custom flash color (defaults to config FLASH_COLOR_RGB)
        """
        self.widget = widget
        self.config = ScopeVisualConfig()
        resolved_flash_color = flash_color or QColor(*self.config.FLASH_COLOR_RGB, 180)
        self._original_stylesheet: Optional[str] = None
        self._use_stylesheet: bool = False

        # Get initial original color (will be re-captured on first flash)
        palette = widget.palette()
        original_color = palette.color(QPalette.ColorRole.Base)

        super().__init__(resolved_flash_color, original_color)

    def _can_flash(self) -> bool:
        """Check if widget is visible."""
        return self.widget is not None and self.widget.isVisible()

    def _prepare_flash(self) -> None:
        """Capture original state before flash starts."""
        self._use_stylesheet = isinstance(self.widget, QGroupBox)
        if self._use_stylesheet:
            self._original_stylesheet = self.widget.styleSheet()
            palette = self.widget.palette()
            self._original_color = palette.color(QPalette.ColorRole.Window)
        else:
            palette = self.widget.palette()
            self._original_color = palette.color(QPalette.ColorRole.Base)

    def _apply_color(self, color: QColor) -> None:
        """Apply interpolated color to widget."""
        if not self.widget:
            return

        if self._use_stylesheet:
            # GroupBox: Apply via stylesheet
            r, g, b, a = color.red(), color.green(), color.blue(), color.alpha()
            style = f"QGroupBox {{ background-color: rgba({r}, {g}, {b}, {a}); }}"
            self.widget.setStyleSheet(style)
        else:
            # Other widgets: Apply via palette
            palette = self.widget.palette()
            palette.setColor(QPalette.ColorRole.Base, color)
            self.widget.setPalette(palette)

    def _on_animation_complete(self) -> None:
        """Restore original stylesheet for GroupBox."""
        if self._use_stylesheet and self._original_stylesheet is not None:
            self.widget.setStyleSheet(self._original_stylesheet)
        logger.debug(f"✅ Smooth flash complete for {type(self.widget).__name__}")


# Global registry of animators (keyed by widget id)
_widget_animators: dict[int, WidgetFlashAnimator] = {}


def flash_widget(widget: QWidget, flash_color: Optional[QColor] = None) -> None:
    """Flash a widget to indicate update.

    Args:
        widget: Widget to flash
        flash_color: Optional custom flash color (defaults to config FLASH_COLOR_RGB)
    """
    config = ScopeVisualConfig()
    if not config.WIDGET_FLASH_ENABLED:
        return

    if not widget or not widget.isVisible():
        return

    widget_id = id(widget)

    # Get or create animator
    if widget_id not in _widget_animators:
        _widget_animators[widget_id] = WidgetFlashAnimator(widget, flash_color=flash_color)
    else:
        # Update flash color if provided
        if flash_color is not None:
            _widget_animators[widget_id].flash_color = flash_color

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
        animator.stop()  # Stop all animations
        del _widget_animators[widget_id]

