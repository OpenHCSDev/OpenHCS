"""Base class for smooth flash animations using QVariantAnimation.

Uses QVariantAnimation for smooth 60fps color transitions:
- Rapid fade-in (~100ms) with OutQuad easing
- Hold at max flash while rapid updates continue
- Smooth fade-out (~350ms) with InOutCubic easing when updates stop
"""

import logging
from abc import abstractmethod
from typing import Optional
from PyQt6.QtCore import QVariantAnimation, QEasingCurve, QTimer
from PyQt6.QtGui import QColor

logger = logging.getLogger(__name__)


class SmoothFlashAnimatorBase:
    """Base class for smooth flash animation with hold-at-max behavior.

    Uses QVariantAnimation for 60fps color interpolation with:
    - Rapid fade-in: 100ms with OutQuad easing (quick snap to flash color)
    - Hold at max: stays at flash color while rapid updates continue
    - Smooth fade-out: 350ms with InOutCubic easing (when updates stop)

    Subclasses must implement:
    - _apply_color(color: QColor) -> None: Apply interpolated color to target
    - _on_animation_complete() -> None: Cleanup when animation finishes
    """

    # Animation timing constants (configurable per-class)
    FADE_IN_DURATION_MS: int = 100   # Rapid fade-in
    FADE_OUT_DURATION_MS: int = 350  # Smooth fade-out
    HOLD_DURATION_MS: int = 150      # Hold at max flash before fade-out

    def __init__(self, flash_color: QColor, original_color: QColor):
        """Initialize animator.

        Args:
            flash_color: Target color at max flash intensity
            original_color: Color to return to after flash
        """
        self.flash_color = flash_color
        self._original_color = original_color
        self._is_flashing: bool = False

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
        self._fade_out_anim.finished.connect(self._on_fade_out_complete)

        # Hold timer - resets on each flash, starts fade-out when expires
        self._hold_timer = QTimer()
        self._hold_timer.setSingleShot(True)
        self._hold_timer.timeout.connect(self._start_fade_out)

    def flash_update(self) -> None:
        """Trigger smooth flash animation. Call this on each update."""
        if not self._can_flash():
            return

        # If already flashing, just reset the hold timer (stay at max flash)
        if self._is_flashing:
            self._hold_timer.stop()
            self._fade_out_anim.stop()  # Cancel fade-out if it started
            self._apply_color(self.flash_color)  # Ensure at max
            self._hold_timer.start(self.HOLD_DURATION_MS)
            return

        # First flash - prepare and start fade-in
        self._prepare_flash()
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

    def _on_fade_out_complete(self) -> None:
        """Called when fade-out completes."""
        self._is_flashing = False
        self._on_animation_complete()

    def stop(self) -> None:
        """Stop all animations immediately."""
        self._fade_in_anim.stop()
        self._fade_out_anim.stop()
        self._hold_timer.stop()
        self._is_flashing = False

    # --- Abstract methods for subclasses ---

    def _can_flash(self) -> bool:
        """Return True if flash should proceed. Override to add visibility checks."""
        return True

    def _prepare_flash(self) -> None:
        """Called before first flash starts. Override to capture original state."""
        pass

    @abstractmethod
    def _apply_color(self, color: QColor) -> None:
        """Apply interpolated color to target. Called ~60 times/sec during animation."""
        raise NotImplementedError

    def _on_animation_complete(self) -> None:
        """Called when animation finishes. Override to restore original state."""
        pass

