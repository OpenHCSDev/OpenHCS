"""Unified visual update mixin for PyQt widgets.

GAME ENGINE ARCHITECTURE:
- Single FlashOverlayWidget per form renders ALL flash effects in ONE paintEvent
- Global 60fps timer triggers overlay.update() only (not individual groupboxes)
- Overlay gets geometry from groupbox registry, draws all rectangles in one pass
- Scales O(1) per window regardless of number of animated items

PAINT-TIME color computation: store start_time, compute color during paint.
Text updates batched on a separate debounce timer per widget.
"""

import logging
import time
from typing import Dict, Optional, Set, Tuple, List, TYPE_CHECKING
from PyQt6.QtCore import QTimer, Qt, QRect
from PyQt6.QtWidgets import QWidget
from PyQt6.QtGui import QColor, QPainter

if TYPE_CHECKING:
    from PyQt6.QtWidgets import QGroupBox

logger = logging.getLogger(__name__)


# Shared flash color (light blue)
FLASH_BASE_COLOR = QColor(77, 166, 255)  # #4da6ff

# Animation timing (seconds for perf_counter)
FADE_IN_S = 0.100    # Rapid fade-in
HOLD_S = 0.150       # Hold at max flash
FADE_OUT_S = 0.350   # Smooth fade-out
TOTAL_DURATION_S = FADE_IN_S + HOLD_S + FADE_OUT_S
FLASH_ALPHA = 180    # Flash color alpha
FRAME_MS = 16        # ~60fps timer interval

# PERFORMANCE: Pre-computed colors to avoid allocation
_FLASH_COLOR_FULL = QColor(77, 166, 255, FLASH_ALPHA)
_TRANSPARENT = QColor(0, 0, 0, 0)


def get_flash_color(opacity: float = 1.0) -> QColor:
    """Get the shared flash QColor with optional opacity (0.0-1.0)."""
    if opacity >= 1.0:
        return _FLASH_COLOR_FULL
    color = QColor(FLASH_BASE_COLOR)
    color.setAlpha(int(FLASH_ALPHA * opacity))
    return color


def compute_flash_color_at_time(start_time: float, now: float) -> Optional[QColor]:
    """Compute flash color based on elapsed time. Returns None if animation complete.

    PAINT-TIME COMPUTATION: Called during paint, not during timer tick.
    This moves O(n) color computation from timer to paint (which Qt batches).
    """
    elapsed = now - start_time

    if elapsed < 0:
        return None  # Not started yet
    elif elapsed >= TOTAL_DURATION_S:
        return None  # Animation complete
    elif elapsed < FADE_IN_S:
        # Fade in: 0 → full alpha
        t = elapsed / FADE_IN_S
        t = t * (2 - t)  # OutQuad easing
        alpha = int(FLASH_ALPHA * t)
        return QColor(77, 166, 255, alpha)
    elif elapsed < FADE_IN_S + HOLD_S:
        # Hold at full
        return _FLASH_COLOR_FULL
    else:
        # Fade out: full → 0
        fade_elapsed = elapsed - FADE_IN_S - HOLD_S
        t = fade_elapsed / FADE_OUT_S
        # InOutCubic easing
        if t < 0.5:
            t = 4 * t * t * t
        else:
            t = 1 - pow(-2 * t + 2, 3) / 2
        alpha = int(FLASH_ALPHA * (1 - t))
        return QColor(77, 166, 255, alpha)


# ==================== GLOBAL ANIMATION COORDINATOR ====================
# Single timer shared across ALL FlashMixin instances - triggers repaints only

class _GlobalFlashCoordinator:
    """Singleton coordinator for all flash animations across all windows.

    BATCH ARCHITECTURE (O(1) per window):
    - Timer tick pre-computes ALL colors across ALL windows in ONE pass
    - Store computed colors in shared dict: key -> QColor
    - Overlays just do dict lookups during paintEvent (no computation)
    - Total work: O(n) once per tick, then O(k) lookups per window
    """
    _instance: Optional['_GlobalFlashCoordinator'] = None

    @classmethod
    def get(cls) -> '_GlobalFlashCoordinator':
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance

    def __init__(self):
        self._timer: Optional[QTimer] = None
        self._active_mixins: Set['VisualUpdateMixin'] = set()
        # BATCH: Pre-computed colors for ALL keys across ALL windows
        self._computed_colors: Dict[str, QColor] = {}

    def _ensure_timer(self) -> QTimer:
        """Lazy-create timer on first use (after QApplication exists)."""
        if self._timer is None:
            self._timer = QTimer()
            self._timer.timeout.connect(self._on_global_tick)
        return self._timer

    def register(self, mixin: 'VisualUpdateMixin') -> None:
        """Register a mixin as needing animation updates."""
        self._active_mixins.add(mixin)
        timer = self._ensure_timer()
        was_active = timer.isActive()
        if not was_active:
            timer.start(FRAME_MS)
        logger.debug(f"[FLASH] register: mixin={type(mixin).__name__}, mixins={len(self._active_mixins)}, timer_was_active={was_active}, timer_now_active={timer.isActive()}")

    def unregister(self, mixin: 'VisualUpdateMixin') -> None:
        """Unregister a mixin (no more active flashes)."""
        self._active_mixins.discard(mixin)
        if not self._active_mixins and self._timer and self._timer.isActive():
            self._timer.stop()

    def get_computed_color(self, key: str) -> Optional[QColor]:
        """Get pre-computed color for key. O(1) dict lookup."""
        return self._computed_colors.get(key)

    def _on_global_tick(self) -> None:
        """Global tick - BATCH compute ALL colors, then trigger repaints."""
        logger.debug(f"[FLASH] _on_global_tick ENTER, mixins={len(self._active_mixins)}")
        now = time.perf_counter()

        # ==================== BATCH COLOR COMPUTATION ====================
        # Compute ALL colors for ALL windows in ONE pass (O(n) total)
        self._computed_colors.clear()
        total_keys = 0
        for mixin in self._active_mixins:
            for key, start_time in mixin._flash_start_times.items():
                color = compute_flash_color_at_time(start_time, now)
                if color and color.alpha() > 0:
                    self._computed_colors[key] = color
                    total_keys += 1

        # DIAGNOSTIC: Log mixin count and key count every 60 frames (~1s)
        if not hasattr(self, '_tick_count'):
            self._tick_count = 0
        self._tick_count += 1
        if self._tick_count % 60 == 0:
            logger.debug(f"[FLASH TICK] mixins={len(self._active_mixins)}, keys={total_keys}, computed_colors={len(self._computed_colors)}")

        # ==================== TRIGGER REPAINTS ====================
        # Now each overlay just reads from _computed_colors (O(1) lookups)
        dead_mixins = []
        for mixin in list(self._active_mixins):
            try:
                # Prune expired animations (always, even if invisible)
                still_active = mixin._prune_and_repaint(now, trigger_repaint=mixin._is_flash_visible())
                if not still_active:
                    dead_mixins.append(mixin)
            except RuntimeError:
                dead_mixins.append(mixin)

        for mixin in dead_mixins:
            self._active_mixins.discard(mixin)

        if not self._active_mixins and self._timer:
            self._timer.stop()


class VisualUpdateMixin:
    """Mixin providing batched visual updates at 60fps.

    PAINT-TIME ARCHITECTURE:
    - _flash_start_times: Dict[key, start_time] - when each flash started
    - Timer tick: prune expired, trigger repaint (O(n) dict iteration only)
    - Paint callback: compute_flash_color_at_time(start_time, now) per visible item

    Subclasses must implement:
    - _visual_repaint() -> None: Trigger single widget repaint
    - get_flash_color_for_key(key) -> Optional[QColor]: Called during paint
    """

    # PAINT-TIME: Only store start times, not colors
    _flash_start_times: Dict[str, float]
    _text_timer: QTimer
    _text_update_pending: bool
    _flash_overlay: Optional['FlashOverlayWidget']

    def _init_visual_update_mixin(self) -> None:
        """Initialize visual update state. Call in __init__."""
        self._flash_start_times = {}
        self._text_update_pending = False
        self._flash_overlay = None  # Created lazily when first groupbox registered

        # Text update timer (per-widget, debounced)
        self._text_timer = QTimer()
        self._text_timer.setSingleShot(True)
        self._text_timer.timeout.connect(self._execute_text_update_batch)

    def register_flash_groupbox(self, key: str, groupbox: 'QWidget') -> None:
        """Register a groupbox for overlay-based flash rendering.

        GAME ENGINE: All flash effects are rendered by a single overlay widget
        instead of each groupbox having its own paintEvent.
        """
        # Lazy-create overlay on first registration
        if self._flash_overlay is None:
            self._flash_overlay = FlashOverlayWidget(self, self)
        self._flash_overlay.register_groupbox(key, groupbox)

    def queue_visual_update(self) -> None:
        """Queue text/placeholder update (debounced)."""
        self._text_update_pending = True
        if not self._text_timer.isActive():
            self._text_timer.start(16)

    def queue_flash(self, key: str) -> None:
        """Start or retrigger flash for key."""
        self._flash_start_times[key] = time.perf_counter()
        logger.debug(f"[FLASH] queue_flash: key={key}, total_keys={len(self._flash_start_times)}")
        # Register with global coordinator (starts timer if needed)
        _GlobalFlashCoordinator.get().register(self)

    def get_flash_color_for_key(self, key: str) -> Optional[QColor]:
        """Get current flash color for key. Called during paint.

        PAINT-TIME: Computes color from start_time, no per-frame storage.
        """
        start_time = self._flash_start_times.get(key)
        if start_time is None:
            return None
        return compute_flash_color_at_time(start_time, time.perf_counter())

    def _prune_and_repaint(self, now: float, trigger_repaint: bool = True) -> bool:
        """Prune expired animations and optionally trigger repaint. Called by coordinator."""
        # Remove expired (animation complete)
        expired = [k for k, st in self._flash_start_times.items()
                   if now - st >= TOTAL_DURATION_S]
        for key in expired:
            del self._flash_start_times[key]

        # Trigger repaint if still animating AND visible
        if self._flash_start_times:
            if trigger_repaint:
                self._visual_repaint()
            return True
        return False

    def _execute_text_update_batch(self) -> None:
        """Execute pending text update."""
        if self._text_update_pending:
            self._text_update_pending = False
            self._execute_text_update()
            self._visual_repaint()

    def _execute_text_update(self) -> None:
        """Execute text/placeholder update. Override in subclass."""
        pass

    def _visual_repaint(self) -> None:
        """GAME ENGINE: Repaint only the overlay, not individual groupboxes.

        This is O(1) per window regardless of how many items are animating,
        because the overlay's single paintEvent draws all rectangles.
        """
        if self._flash_overlay is not None:
            # Resize overlay to match parent and repaint
            self._flash_overlay.setGeometry(self.rect())
            self._flash_overlay.raise_()
            self._flash_overlay.update()

    def _is_flash_visible(self) -> bool:
        """Check if this widget's flash animations are visible on screen."""
        return True

    # BACKWARDS COMPAT: Keep old interface working during transition
    @property
    def _flash_states(self) -> Dict[str, float]:
        """Backwards compat: return start_times as flash_states."""
        return self._flash_start_times


# Backwards compatibility
FlashMixin = VisualUpdateMixin


# ==================== GAME ENGINE OVERLAY ====================

class FlashOverlayWidget(QWidget):
    """Transparent overlay that renders ALL flash effects in ONE paintEvent.

    GAME ENGINE ARCHITECTURE:
    - Sits on top of form content (transparent, passes mouse events through)
    - Gets geometry of ALL flashing groupboxes from manager
    - Draws ALL flash rectangles in a SINGLE paintEvent call
    - Only this widget gets update() called - not individual groupboxes

    This scales O(1) per window regardless of how many items are animating,
    because Qt only processes ONE paintEvent per overlay per frame.
    """

    def __init__(self, manager: 'VisualUpdateMixin', parent: QWidget = None):
        super().__init__(parent)
        self._manager = manager
        self._groupbox_registry: Dict[str, 'QGroupBox'] = {}  # key -> groupbox

        # Make overlay transparent and pass mouse events through
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setStyleSheet("background: transparent;")

        # Raise to top of stacking order
        self.raise_()

    def register_groupbox(self, key: str, groupbox: 'QGroupBox') -> None:
        """Register a groupbox for flash overlay rendering."""
        self._groupbox_registry[key] = groupbox

    def unregister_groupbox(self, key: str) -> None:
        """Unregister a groupbox."""
        self._groupbox_registry.pop(key, None)

    def paintEvent(self, a0) -> None:
        """GAME ENGINE: Render ALL flash effects in ONE paint call.

        BATCH ARCHITECTURE: Colors are pre-computed by the global coordinator.
        This paintEvent just does O(k) dict lookups + fillRect calls.
        """
        if not self._manager._flash_start_times:
            return  # Nothing animating

        coordinator = _GlobalFlashCoordinator.get()
        painter = QPainter(self)
        painter.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)

        # Draw ALL flash rectangles in one pass (O(k) lookups, no computation)
        for key in self._manager._flash_start_times:
            # O(1) lookup - color was pre-computed in global tick
            color = coordinator.get_computed_color(key)
            if not color:
                continue

            # Get groupbox geometry
            groupbox = self._groupbox_registry.get(key)
            if groupbox is None:
                continue

            # Map groupbox rect to overlay coordinates
            try:
                # Get groupbox content rect in global coords, then map to overlay
                global_pos = groupbox.mapToGlobal(groupbox.contentsRect().topLeft())
                local_pos = self.mapFromGlobal(global_pos)
                rect = QRect(local_pos, groupbox.contentsRect().size())

                # Only draw if visible
                if rect.intersects(self.rect()):
                    painter.fillRect(rect, color)
            except RuntimeError:
                continue  # Widget deleted

        painter.end()

