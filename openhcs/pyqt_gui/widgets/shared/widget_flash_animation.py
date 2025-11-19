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
        self.flash_color = flash_color or QColor(*self.config.FLASH_COLOR_RGB, 180)
        self._original_palette: Optional[QPalette] = None
        self._original_stylesheet: Optional[str] = None
        self._flash_timer: Optional[QTimer] = None
        self._is_flashing: bool = False
        self._use_stylesheet: bool = False  # Track which method we used

    def flash_update(self) -> None:
        """Trigger flash animation on widget background."""
        if not self.widget or not self.widget.isVisible():
            logger.info(f"⚠️ Widget not visible or None")
            return

        if self._is_flashing:
            # Already flashing - restart timer
            logger.info(f"⚠️ Already flashing, restarting timer")
            if self._flash_timer:
                self._flash_timer.stop()
                self._flash_timer.start(self.config.FLASH_DURATION_MS)
            return

        self._is_flashing = True
        logger.debug(f"🎨 Starting flash animation for {type(self.widget).__name__}")

        # Use different approaches depending on widget type
        # GroupBox: Use stylesheet (stylesheets override palettes)
        # Input widgets: Use palette (works fine for QLineEdit, QComboBox, etc.)
        from PyQt6.QtWidgets import QGroupBox
        if isinstance(self.widget, QGroupBox):
            self._use_stylesheet = True
            # Store original stylesheet
            self._original_stylesheet = self.widget.styleSheet()
            logger.debug(f"   Is GroupBox, using stylesheet approach")
            logger.debug(f"   Original stylesheet: '{self._original_stylesheet}'")

            # Apply flash color via stylesheet (overrides parent stylesheet)
            r, g, b, a = self.flash_color.red(), self.flash_color.green(), self.flash_color.blue(), self.flash_color.alpha()
            flash_style = f"QGroupBox {{ background-color: rgba({r}, {g}, {b}, {a}); }}"
            logger.debug(f"   Applying flash style: '{flash_style}'")
            self.widget.setStyleSheet(flash_style)
        else:
            self._use_stylesheet = False
            # Store original palette
            self._original_palette = self.widget.palette()
            logger.debug(f"   Not GroupBox, using palette approach")

            # Apply flash color via palette
            flash_palette = self.widget.palette()
            flash_palette.setColor(QPalette.ColorRole.Base, self.flash_color)
            self.widget.setPalette(flash_palette)

        # Setup timer to restore original state
        # CRITICAL: Use widget as parent to prevent garbage collection
        if self._flash_timer is None:
            logger.debug(f"   Creating new timer")
            self._flash_timer = QTimer(self.widget)
            self._flash_timer.setSingleShot(True)
            self._flash_timer.timeout.connect(self._restore_original)

        logger.debug(f"   Starting timer for {self.config.FLASH_DURATION_MS}ms")
        self._flash_timer.start(self.config.FLASH_DURATION_MS)

    def _restore_original(self) -> None:
        """Restore original stylesheet or palette."""
        logger.debug(f"🔄 _restore_original called for {type(self.widget).__name__}")
        if not self.widget:
            logger.debug(f"   Widget is None, aborting")
            self._is_flashing = False
            return

        # Use the flag to determine which method to restore
        if self._use_stylesheet:
            # Restore original stylesheet
            logger.debug(f"   Restoring stylesheet: '{self._original_stylesheet}'")
            self.widget.setStyleSheet(self._original_stylesheet)
        else:
            # Restore original palette
            logger.debug(f"   Restoring palette")
            if self._original_palette:
                self.widget.setPalette(self._original_palette)

        logger.debug(f"✅ Restored original state")
        self._is_flashing = False


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
        if animator._flash_timer and animator._flash_timer.isActive():
            animator._flash_timer.stop()
        del _widget_animators[widget_id]

