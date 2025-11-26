"""Flash animation for form widgets (QLineEdit, QComboBox, etc.).

Uses QVariantAnimation for smooth 60fps color transitions:
- Rapid fade-in (~100ms) with OutQuad easing
- Hold at max flash while rapid updates continue
- Smooth fade-out (~350ms) with InOutCubic easing when updates stop
"""

import logging
from typing import Optional
from PyQt6.QtCore import QVariantAnimation, QEasingCurve, QTimer
from PyQt6.QtWidgets import QWidget, QGroupBox
from PyQt6.QtGui import QColor, QPalette

from .scope_visual_config import ScopeVisualConfig

logger = logging.getLogger(__name__)


class WidgetFlashAnimator:
    """Manages smooth flash animation for form widget background color changes.

    Uses QVariantAnimation for 60fps color interpolation with:
    - Rapid fade-in: 100ms with OutQuad easing (quick snap to flash color)
    - Hold at max: stays at flash color while rapid updates continue
    - Smooth fade-out: 350ms with InOutCubic easing (when updates stop)

    Uses stylesheet manipulation for GroupBox (since stylesheets override palettes),
    and palette manipulation for input widgets.
    """

    # Animation timing constants
    FADE_IN_DURATION_MS: int = 100   # Rapid fade-in
    FADE_OUT_DURATION_MS: int = 350  # Smooth fade-out
    HOLD_DURATION_MS: int = 150      # Hold at max flash before fade-out

    def __init__(self, widget: QWidget, flash_color: Optional[QColor] = None):
        """Initialize animator.

        Args:
            widget: Widget to animate
            flash_color: Optional custom flash color (defaults to config FLASH_COLOR_RGB)
        """
        self.widget = widget
        self.config = ScopeVisualConfig()
        self.flash_color = flash_color or QColor(*self.config.FLASH_COLOR_RGB, 180)
        self._original_color: Optional[QColor] = None
        self._original_stylesheet: Optional[str] = None
        self._is_flashing: bool = False
        self._use_stylesheet: bool = False

        # Create fade-in animation
        self._fade_in_anim = QVariantAnimation()
        self._fade_in_anim.setDuration(self.FADE_IN_DURATION_MS)
        self._fade_in_anim.setEasingCurve(QEasingCurve.Type.OutQuad)
        self._fade_in_anim.valueChanged.connect(self._apply_color)
        self._fade_in_anim.finished.connect(self._on_fade_in_complete)

        # Create fade-out animation
        self._fade_out_anim = QVariantAnimation()
        self._fade_out_anim.setDuration(self.FADE_OUT_DURATION_MS)
        self._fade_out_anim.setEasingCurve(QEasingCurve.Type.InOutCubic)
        self._fade_out_anim.valueChanged.connect(self._apply_color)
        self._fade_out_anim.finished.connect(self._on_animation_complete)

        # Hold timer - resets on each flash, starts fade-out when expires
        self._hold_timer = QTimer()
        self._hold_timer.setSingleShot(True)
        self._hold_timer.timeout.connect(self._start_fade_out)

    def flash_update(self, use_coordinator: bool = False) -> None:  # noqa: ARG002
        """Trigger smooth flash animation on widget background.

        Args:
            use_coordinator: Ignored (kept for API compatibility). Animations are self-contained.
        """
        del use_coordinator  # Unused, kept for API compatibility
        if not self.widget or not self.widget.isVisible():
            return

        # If already flashing, just reset the hold timer (stay at max flash)
        if self._is_flashing:
            self._hold_timer.stop()
            self._fade_out_anim.stop()  # Cancel fade-out if it started
            # Ensure we're at max flash color
            self._apply_color(self.flash_color)
            self._hold_timer.start(self.HOLD_DURATION_MS)
            return

        # First flash - capture original and start fade-in
        self._use_stylesheet = isinstance(self.widget, QGroupBox)
        if self._use_stylesheet:
            self._original_stylesheet = self.widget.styleSheet()
            palette = self.widget.palette()
            self._original_color = palette.color(QPalette.ColorRole.Window)
        else:
            palette = self.widget.palette()
            self._original_color = palette.color(QPalette.ColorRole.Base)

        self._is_flashing = True

        # Start fade-in: original -> flash color
        self._fade_in_anim.setStartValue(self._original_color)
        self._fade_in_anim.setEndValue(self.flash_color)
        self._fade_in_anim.start()

    def _on_fade_in_complete(self) -> None:
        """Called when fade-in completes. Start hold timer."""
        self._hold_timer.start(self.HOLD_DURATION_MS)

    def _start_fade_out(self) -> None:
        """Called when hold timer expires. Start fade-out animation."""
        self._fade_out_anim.setStartValue(self.flash_color)
        self._fade_out_anim.setEndValue(self._original_color)
        self._fade_out_anim.start()

    def _apply_color(self, color: QColor) -> None:
        """Apply interpolated color to widget. Called ~60 times/sec during animation."""
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
        """Called when fade-out completes. Restore original state."""
        if self._use_stylesheet and self._original_stylesheet is not None:
            self.widget.setStyleSheet(self._original_stylesheet)
        self._is_flashing = False
        logger.debug(f"✅ Smooth flash complete for {type(self.widget).__name__}")

    def _restore_original(self) -> None:
        """Immediate restoration (for cleanup/cancellation)."""
        self._fade_in_anim.stop()
        self._fade_out_anim.stop()
        self._on_animation_complete()

    def stop(self) -> None:
        """Stop all animations immediately."""
        self._fade_in_anim.stop()
        self._fade_out_anim.stop()
        self._is_flashing = False


# Global registry of animators (keyed by widget id)
_widget_animators: dict[int, WidgetFlashAnimator] = {}


def flash_widget(widget: QWidget, flash_color: Optional[QColor] = None) -> None:
    """Flash a widget with smooth fade-in/fade-out animation.

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
        animator.stop()
        del _widget_animators[widget_id]

