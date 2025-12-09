"""Unified visual update mixin for PyQt widgets.

Uses a SINGLE 60fps timer for ALL flash animations (batched updates).
Text updates batched on a separate debounce timer.
"""

import logging
from typing import Dict, Optional
from PyQt6.QtCore import QTimer
from PyQt6.QtGui import QColor

logger = logging.getLogger(__name__)


# Shared flash color (light blue)
FLASH_BASE_COLOR = QColor(77, 166, 255)  # #4da6ff

# Animation timing (ms)
FADE_IN_MS = 100    # Rapid fade-in
HOLD_MS = 150       # Hold at max flash
FADE_OUT_MS = 350   # Smooth fade-out
FLASH_ALPHA = 180   # Flash color alpha
FRAME_MS = 16       # ~60fps


def get_flash_color(opacity: float = 1.0) -> QColor:
    """Get the shared flash QColor with optional opacity (0.0-1.0)."""
    color = QColor(FLASH_BASE_COLOR)
    color.setAlpha(int(FLASH_ALPHA * opacity))
    return color


def _lerp_color(c1: QColor, c2: QColor, t: float) -> QColor:
    """Linear interpolation between two colors."""
    return QColor(
        int(c1.red() + (c2.red() - c1.red()) * t),
        int(c1.green() + (c2.green() - c1.green()) * t),
        int(c1.blue() + (c2.blue() - c1.blue()) * t),
        int(c1.alpha() + (c2.alpha() - c1.alpha()) * t),
    )


class VisualUpdateMixin:
    """Mixin providing batched visual updates at 60fps.

    SINGLE timer handles ALL flash animations - one update() call per frame.

    Subclasses must implement:
    - _execute_text_update() -> None: Update all text/labels
    - _set_item_background(key: str, color: QColor) -> None: Set item bg (no update)
    - _get_original_color(key: str) -> Optional[QColor]: Get original bg color
    - _visual_repaint() -> None: Trigger single widget repaint
    """

    # Flash state per key: (phase, elapsed_ms, original_color, current_color)
    # phase: 'in' | 'hold' | 'out'
    _flash_states: Dict[str, tuple]
    _frame_timer: QTimer
    _text_timer: QTimer
    _text_update_pending: bool

    def _init_visual_update_mixin(self) -> None:
        """Initialize visual update state. Call in __init__."""
        self._flash_states = {}
        self._text_update_pending = False

        # SINGLE timer for ALL flash animations (batched)
        self._frame_timer = QTimer(self)
        self._frame_timer.timeout.connect(self._on_frame_tick)

        # Debounce timer for text updates
        self._text_timer = QTimer(self)
        self._text_timer.setSingleShot(True)
        self._text_timer.timeout.connect(self._execute_text_update_batch)

    def queue_visual_update(self) -> None:
        """Queue text/placeholder update (debounced)."""
        self._text_update_pending = True
        if not self._text_timer.isActive():
            self._text_timer.start(16)

    def queue_flash(self, key: str) -> None:
        """Start or retrigger flash for key."""
        logger.info(f"⚡ FLASH_DEBUG queue_flash: key={key}, self={type(self).__name__}")
        original = self._get_original_color(key) or QColor(0, 0, 0, 0)
        flash_color = get_flash_color(1.0)

        if key in self._flash_states:
            # Retrigger - jump to hold phase at flash color
            logger.info(f"⚡ FLASH_DEBUG queue_flash: RETRIGGER existing flash for {key}")
            self._flash_states[key] = ('hold', 0, original, flash_color)
            self._set_item_background(key, flash_color)
        else:
            # New flash - start fade-in
            logger.info(f"⚡ FLASH_DEBUG queue_flash: NEW flash for {key}")
            self._flash_states[key] = ('in', 0, original, original)

        logger.info(f"⚡ FLASH_DEBUG queue_flash: _flash_states now has {len(self._flash_states)} entries")
        # Ensure timer is running
        if not self._frame_timer.isActive():
            logger.info(f"⚡ FLASH_DEBUG queue_flash: Starting frame timer")
            self._frame_timer.start(FRAME_MS)

    def _on_frame_tick(self) -> None:
        """Single frame tick - update ALL flashes, then ONE repaint."""
        to_remove = []

        for key, (phase, elapsed, original, current) in list(self._flash_states.items()):
            elapsed += FRAME_MS
            flash_color = get_flash_color(1.0)

            if phase == 'in':
                t = min(1.0, elapsed / FADE_IN_MS)
                # OutQuad easing: t * (2 - t)
                t = t * (2 - t)
                new_color = _lerp_color(original, flash_color, t)
                self._set_item_background(key, new_color)
                if elapsed >= FADE_IN_MS:
                    self._flash_states[key] = ('hold', 0, original, flash_color)
                else:
                    self._flash_states[key] = ('in', elapsed, original, new_color)

            elif phase == 'hold':
                if elapsed >= HOLD_MS:
                    self._flash_states[key] = ('out', 0, original, flash_color)
                else:
                    self._flash_states[key] = ('hold', elapsed, original, flash_color)

            elif phase == 'out':
                t = min(1.0, elapsed / FADE_OUT_MS)
                # InOutCubic easing
                if t < 0.5:
                    t = 4 * t * t * t
                else:
                    t = 1 - pow(-2 * t + 2, 3) / 2
                new_color = _lerp_color(flash_color, original, t)
                self._set_item_background(key, new_color)
                if elapsed >= FADE_OUT_MS:
                    self._set_item_background(key, original)
                    to_remove.append(key)
                else:
                    self._flash_states[key] = ('out', elapsed, original, new_color)

        for key in to_remove:
            del self._flash_states[key]

        # ONE repaint for all items
        self._visual_repaint()

        # Stop timer when nothing is animating
        if not self._flash_states:
            self._frame_timer.stop()

    def _execute_text_update_batch(self) -> None:
        """Execute pending text update."""
        if self._text_update_pending:
            self._text_update_pending = False
            self._execute_text_update()
            self._visual_repaint()

    def _execute_text_update(self) -> None:
        """Execute text/placeholder update. Override in subclass."""
        pass

    def _set_item_background(self, key: str, color: QColor) -> None:
        """Set item background without triggering repaint. Override in subclass."""
        raise NotImplementedError("Subclass must implement _set_item_background")

    def _get_original_color(self, key: str) -> Optional[QColor]:
        """Get original background color for key. Override in subclass."""
        return None  # Default: transparent

    def _visual_repaint(self) -> None:
        """Trigger single widget repaint. Override in subclass."""
        pass


# Backwards compatibility
FlashMixin = VisualUpdateMixin

