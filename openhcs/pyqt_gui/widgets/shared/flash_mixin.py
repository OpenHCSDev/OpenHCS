"""Unified visual update mixin for PyQt widgets.

GAME ENGINE ARCHITECTURE (TRUE O(1) PER WINDOW):
- ONE WindowFlashOverlay per top-level window renders ALL flash effects
- ALL element types (groupboxes, tree items, list items) register with it
- Single paintEvent draws ALL flash rectangles regardless of element count/type
- Scales O(1) per window, O(k) per flashing element, regardless of total elements

BATCH COLOR COMPUTATION:
- Global 60fps coordinator pre-computes ALL colors in ONE pass
- Overlays just do O(1) dict lookups during paintEvent
- Total work: O(k) per tick where k = number of flashing elements
"""

import logging
import time
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Callable, Any, Tuple, TYPE_CHECKING
from weakref import WeakValueDictionary
from PyQt6.QtCore import QTimer, Qt, QRect
from PyQt6.QtWidgets import QWidget, QMainWindow, QDialog, QScrollArea
from PyQt6.QtGui import QColor, QPainter

if TYPE_CHECKING:
    from PyQt6.QtWidgets import QGroupBox, QTreeWidget, QListWidget

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


# ==================== FLASH ELEMENT REGISTRATION ====================
# Unified element representation for groupboxes, tree items, list items

@dataclass
class FlashElement:
    """Abstract representation of a flashable UI element.

    Provides a geometry callback that returns the element's rect in window coords.
    Works for ANY element type: groupboxes, tree items, list items, etc.
    """
    key: str
    get_rect_in_window: Callable[[QWidget], Optional[QRect]]
    get_child_rects: Optional[Callable[[QWidget], List[QRect]]] = None  # For masking child widgets
    needs_scroll_clipping: bool = True  # Groupboxes need clipping, list/tree items don't (they handle it themselves)
    source_id: Optional[str] = None  # Unique identifier for deduplication (e.g., "groupbox:123", "list_item:scope_id")


def create_groupbox_element(key: str, groupbox: 'QGroupBox') -> FlashElement:
    """Create a FlashElement for a QGroupBox.

    Maps groupbox position to WINDOW coordinates (not scroll content coordinates).
    This accounts for scroll position so rects are in visible window space.
    Flashes the groupbox background (same area as stylesheet background-color) by
    subtracting the layout's content area.
    """
    def get_rect(window: QWidget) -> Optional[QRect]:
        try:
            # Use full rect (includes frame/title)
            global_pos = groupbox.mapToGlobal(groupbox.rect().topLeft())
            window_pos = window.mapFromGlobal(global_pos)
            return QRect(window_pos, groupbox.rect().size())
        except RuntimeError:
            return None

    def get_child_rects(window: QWidget) -> List[QRect]:
        """Get content widgets to exclude from flash.

        Flashes the groupbox background (frame, title area, margins) while keeping
        form content visible. For GroupBoxWithHelp, excludes widgets in content_layout
        but flashes over the title area background.
        """
        import logging
        logger = logging.getLogger(__name__)

        child_rects = []
        try:
            # Debug: inspect groupbox structure
            logger.info(f"⚡ GROUPBOX_FLASH: === Inspecting groupbox ===")
            logger.info(f"⚡ GROUPBOX_FLASH: groupbox type: {type(groupbox).__name__}")
            logger.info(f"⚡ GROUPBOX_FLASH: groupbox.rect(): {groupbox.rect().x()},{groupbox.rect().y()} {groupbox.rect().width()}x{groupbox.rect().height()}")
            logger.info(f"⚡ GROUPBOX_FLASH: has content_layout: {hasattr(groupbox, 'content_layout')}")

            # Inspect main layout
            main_layout = groupbox.layout()
            if main_layout:
                logger.info(f"⚡ GROUPBOX_FLASH: main_layout type: {type(main_layout).__name__}")
                logger.info(f"⚡ GROUPBOX_FLASH: main_layout.count(): {main_layout.count()}")
                logger.info(f"⚡ GROUPBOX_FLASH: main_layout.geometry(): {main_layout.geometry().x()},{main_layout.geometry().y()} {main_layout.geometry().width()}x{main_layout.geometry().height()}")

                # Inspect each item in main layout
                for i in range(main_layout.count()):
                    item = main_layout.itemAt(i)
                    if item:
                        if item.widget():
                            w = item.widget()
                            logger.info(f"⚡ GROUPBOX_FLASH: main_layout[{i}] = widget {type(w).__name__}, geom={w.geometry().x()},{w.geometry().y()} {w.geometry().width()}x{w.geometry().height()}")
                        elif item.layout():
                            l = item.layout()
                            logger.info(f"⚡ GROUPBOX_FLASH: main_layout[{i}] = layout {type(l).__name__}, count={l.count()}, geom={l.geometry().x()},{l.geometry().y()} {l.geometry().width()}x{l.geometry().height()}")

            # Check if this is a GroupBoxWithHelp with content_layout
            if hasattr(groupbox, 'content_layout'):
                from PyQt6.QtWidgets import (QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox,
                                              QCheckBox, QPushButton, QToolButton, QTextEdit,
                                              QPlainTextEdit, QTreeWidget, QListWidget, QTableWidget,
                                              QLabel)

                # Recursively find all leaf widgets (buttons, labels, inputs) to exclude
                # This flashes container backgrounds but not the actual content
                LEAF_WIDGET_TYPES = (QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QCheckBox,
                                     QPushButton, QToolButton, QTextEdit, QPlainTextEdit,
                                     QTreeWidget, QListWidget, QTableWidget, QLabel)

                for child in groupbox.findChildren(QWidget):
                    if child.isVisible() and isinstance(child, LEAF_WIDGET_TYPES):
                        # Map child geometry to window coordinates
                        child_geom = child.geometry()
                        global_pos = child.mapToGlobal(child.rect().topLeft())
                        window_pos = window.mapFromGlobal(global_pos)
                        child_rects.append(QRect(window_pos, child.rect().size()))
                        logger.info(f"⚡ GROUPBOX_FLASH: Excluding leaf widget {type(child).__name__}: {window_pos.x()},{window_pos.y()} {child.rect().width()}x{child.rect().height()}")

                logger.info(f"⚡ GROUPBOX_FLASH: Total child_rects to exclude: {len(child_rects)}")
            else:
                # Regular QGroupBox - exclude all direct child widgets
                for child in groupbox.children():
                    if isinstance(child, QWidget) and child.isVisible():
                        child_geom = child.geometry()
                        global_pos = groupbox.mapToGlobal(child_geom.topLeft())
                        window_pos = window.mapFromGlobal(global_pos)
                        child_rects.append(QRect(window_pos, child_geom.size()))
        except RuntimeError:
            pass
        return child_rects

    return FlashElement(
        key=key,
        get_rect_in_window=get_rect,
        get_child_rects=get_child_rects,
        source_id=f"groupbox:{id(groupbox)}"
    )


def create_tree_item_element(key: str, tree: 'QTreeWidget', get_index: Callable[[], Any]) -> FlashElement:
    """Create a FlashElement for a tree item.

    Args:
        key: Flash key
        tree: The QTreeWidget
        get_index: Callback that returns the current QModelIndex (handles item recreation)
    """
    def get_rect(window: QWidget) -> Optional[QRect]:
        try:
            index = get_index()
            if index is None or not index.isValid():
                return None
            visual_rect = tree.visualRect(index)
            if not visual_rect.isValid():
                return None
            viewport = tree.viewport()
            if viewport is None:
                return None
            global_pos = viewport.mapToGlobal(visual_rect.topLeft())
            window_pos = window.mapFromGlobal(global_pos)
            return QRect(window_pos, visual_rect.size())
        except RuntimeError:
            return None
    return FlashElement(
        key=key,
        get_rect_in_window=get_rect,
        needs_scroll_clipping=False,
        source_id=f"tree:{id(tree)}:{key}"  # Include key to distinguish different items in same tree
    )


def create_list_item_element(key: str, list_widget: 'QListWidget', get_row: Callable[[], int]) -> FlashElement:
    """Create a FlashElement for a list item.

    Args:
        key: Flash key
        list_widget: The QListWidget
        get_row: Callback that returns the current row index (handles item recreation)
    """
    def get_rect(window: QWidget) -> Optional[QRect]:
        try:
            row = get_row()
            item = list_widget.item(row)
            if item is None:
                return None
            visual_rect = list_widget.visualItemRect(item)
            if not visual_rect.isValid():
                return None
            viewport = list_widget.viewport()
            if viewport is None:
                return None
            global_pos = viewport.mapToGlobal(visual_rect.topLeft())
            window_pos = window.mapFromGlobal(global_pos)
            return QRect(window_pos, visual_rect.size())
        except RuntimeError:
            return None
    return FlashElement(
        key=key,
        get_rect_in_window=get_rect,
        needs_scroll_clipping=False,
        source_id=f"list:{id(list_widget)}:{key}"  # Include key to distinguish different items in same list
    )


# ==================== WINDOW-LEVEL FLASH OVERLAY ====================
# ONE overlay per top-level window - renders ALL flash effects in ONE paintEvent

class WindowFlashOverlay(QWidget):
    """Transparent overlay that renders ALL flash effects for an entire window.

    TRUE GAME ENGINE ARCHITECTURE:
    - ONE instance per top-level window (QMainWindow/QDialog)
    - Renders ALL element types (groupboxes, tree items, list items) in ONE paintEvent
    - Elements register via FlashElement with geometry callbacks
    - Scales O(1) per window regardless of element count or type

    VIEWPORT CULLING: Elements outside visible scroll areas return None from
    their geometry callback and are skipped.
    """
    # Class-level registry: window_id -> overlay (weak refs for cleanup)
    _overlays: Dict[int, 'WindowFlashOverlay'] = {}

    @classmethod
    def get_for_window(cls, widget: QWidget) -> Optional['WindowFlashOverlay']:
        """Get or create the overlay for a top-level window.

        Returns None if widget is not yet in a proper window hierarchy
        (i.e., widget.window() returns itself rather than a QMainWindow/QDialog).
        """
        # Find the actual top-level window
        top_window = widget.window()

        # Only create overlays for REAL top-level windows, not widgets that
        # return themselves because they haven't been parented yet
        if not isinstance(top_window, (QMainWindow, QDialog)):
            return None

        window_id = id(top_window)

        if window_id not in cls._overlays:
            overlay = cls(top_window)
            cls._overlays[window_id] = overlay
            logger.info(f"🧹 FLASH_LEAK_DEBUG: Created WindowFlashOverlay for window {window_id}, "
                       f"total overlays: {len(cls._overlays)}")

        return cls._overlays[window_id]

    @classmethod
    def cleanup_window(cls, window: QWidget) -> None:
        """Remove overlay for a window (call when window closes)."""
        window_id = id(window.window())
        overlays_before = len(cls._overlays)
        overlay = cls._overlays.pop(window_id, None)
        overlays_after = len(cls._overlays)
        if overlay:
            # CRITICAL: Clear all registered elements BEFORE deleteLater()
            # Otherwise overlay might paint dead elements during async deletion
            elements_count = sum(len(v) for v in overlay._elements.values())
            overlay._elements.clear()
            overlay.deleteLater()
            logger.info(f"🧹 FLASH_LEAK_DEBUG: Cleaned up WindowFlashOverlay for window {window_id}, "
                       f"cleared {elements_count} elements, total overlays: {overlays_before} -> {overlays_after}")
        else:
            logger.warning(f"🧹 FLASH_LEAK_DEBUG: No overlay found for window {window_id}, "
                          f"total overlays: {overlays_before}")

    def __init__(self, window: QWidget):
        super().__init__(window)
        self._window = window
        self._elements: Dict[str, List[FlashElement]] = {}  # key -> list of elements

        # Make overlay transparent and pass mouse events through
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setStyleSheet("background: transparent;")

        # CRITICAL: Disable Qt's paint optimizations that clip to dirty regions
        # When another window occludes this window and then moves away, Qt only
        # sends paintEvents for the newly exposed "dirty" region. This causes
        # flashes to only appear in the occluded area. By setting WA_OpaquePaintEvent
        # to False, we tell Qt to always repaint the entire widget.
        self.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent, False)

        # Cover entire window
        self.setGeometry(window.rect())
        self.raise_()
        self.show()

    def register_element(self, element: FlashElement) -> None:
        """Register a flashable element. Multiple elements can share the same key.

        CRITICAL: Deduplicate based on (key, source_id) to prevent duplicate registrations
        while allowing multiple element types (tree item + groupbox) for the same key.
        """
        if element.key not in self._elements:
            self._elements[element.key] = []

        # Check if element with same source_id already exists
        if element.source_id is not None:
            for i, existing in enumerate(self._elements[element.key]):
                if existing.source_id == element.source_id:
                    # Replace existing element with same source
                    self._elements[element.key][i] = element
                    logger.debug(f"[FLASH] Replaced element: {element.key}, source_id={element.source_id}")
                    return

        # New element - append
        self._elements[element.key].append(element)
        total = sum(len(v) for v in self._elements.values())
        logger.debug(f"[FLASH] Registered element: {element.key}, source_id={element.source_id}, total={total}")

    def unregister_element(self, key: str) -> None:
        """Unregister all elements for a key."""
        self._elements.pop(key, None)

    def resizeEvent(self, event) -> None:
        """Resize to cover entire window."""
        super().resizeEvent(event)
        if self._window:
            self.setGeometry(self._window.rect())

    def is_element_in_viewport(self, key: str) -> bool:
        """Check if any element for this key is visible (for viewport culling)."""
        elements = self._elements.get(key)
        if not elements:
            return False
        # Return True if ANY element for this key is visible
        for element in elements:
            rect = element.get_rect_in_window(self._window)
            if rect and rect.isValid() and rect.intersects(self.rect()):
                return True
        return False

    def get_visible_keys(self) -> Set[str]:
        """Get set of keys for elements currently visible in viewport."""
        return {key for key in self._elements if self.is_element_in_viewport(key)}

    def _get_scroll_area_clip_rects(self) -> List[QRect]:
        """Find all QScrollArea viewports in the window and return their rects in window coords.

        Flash rectangles will be clipped to these areas to avoid bleeding over headers/buttons.
        """
        from PyQt6.QtWidgets import QScrollArea

        clip_rects = []
        # Find all QScrollArea widgets in the window
        scroll_areas = self._window.findChildren(QScrollArea)
        for scroll_area in scroll_areas:
            viewport = scroll_area.viewport()
            if viewport and viewport.isVisible():
                # Get viewport rect in window coordinates
                viewport_rect = viewport.rect()
                global_pos = viewport.mapToGlobal(viewport_rect.topLeft())
                window_pos = self._window.mapFromGlobal(global_pos)
                clip_rects.append(QRect(window_pos, viewport_rect.size()))

        return clip_rects

    def _clip_to_scroll_areas(self, rect: QRect, clip_rects: List[QRect]) -> Optional[QRect]:
        """Clip a flash rect to only the parts that intersect with scroll area viewports.

        Returns the clipped rect, or None if the rect doesn't intersect any scroll areas.
        """
        for clip_rect in clip_rects:
            intersection = rect.intersected(clip_rect)
            if intersection.isValid():
                return intersection
        return None

    def paintEvent(self, event) -> None:
        """GAME ENGINE: Render ALL flash effects in ONE paint call.

        O(k) where k = number of flashing elements with active animations.
        Multiple elements can share the same key (e.g., tree item + groupbox).
        """
        coordinator = _GlobalFlashCoordinator.get()
        if not coordinator._computed_colors:
            return  # Nothing animating

        painter = QPainter(self)
        painter.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)

        # Find scroll areas to clip flash rectangles (don't flash over headers/buttons)
        clip_rects = self._get_scroll_area_clip_rects()

        drawn_count = 0
        # Draw ALL flash rectangles in one pass
        for key, elements in self._elements.items():
            color = coordinator.get_computed_color(key)
            if not color:
                continue

            # Draw all elements for this key (tree item + groupbox share same key)
            for element in elements:
                rect = element.get_rect_in_window(self._window)
                if rect and rect.isValid() and rect.intersects(self.rect()):
                    # Try clipping to scroll areas ONLY if element needs it
                    # List/tree items handle their own viewport clipping, groupboxes need it
                    rect_to_draw = rect
                    if element.needs_scroll_clipping and clip_rects:
                        clipped_rect = self._clip_to_scroll_areas(rect, clip_rects)
                        if clipped_rect and clipped_rect.isValid():
                            # Element is inside a scroll area - use clipped rect
                            rect_to_draw = clipped_rect
                        # else: Element is NOT inside any scroll area - use full rect

                    # Check if element has child widgets to mask (e.g., groupbox)
                    if element.get_child_rects:
                        from PyQt6.QtGui import QPainterPath
                        # Create path for groupbox background (excluding child widgets)
                        path = QPainterPath()
                        path.addRect(rect_to_draw.x(), rect_to_draw.y(), rect_to_draw.width(), rect_to_draw.height())

                        # Subtract child widget rects
                        child_rects = element.get_child_rects(self._window)
                        for child_rect in child_rects:
                            if child_rect.intersects(rect_to_draw):
                                child_path = QPainterPath()
                                child_path.addRect(child_rect.x(), child_rect.y(), child_rect.width(), child_rect.height())
                                path = path.subtracted(child_path)

                        painter.fillPath(path, color)
                    else:
                        # No child masking - fill entire rect
                        painter.fillRect(rect_to_draw, color)

                    drawn_count += 1
                    # Debug: log first few rects
                    if drawn_count <= 2:
                        logger.debug(f"[FLASH] Drew rect for {key}: {rect.x()},{rect.y()} {rect.width()}x{rect.height()}")

        if drawn_count > 0:
            logger.debug(f"[FLASH] WindowFlashOverlay.paintEvent drew {drawn_count} rectangles, overlay={self.rect().width()}x{self.rect().height()}")

        painter.end()


# ==================== GLOBAL ANIMATION COORDINATOR ====================
# Single timer shared across ALL windows - batch computes colors, triggers repaints

class _GlobalFlashCoordinator:
    """Singleton coordinator for all flash animations across all windows.

    TRUE O(1) ARCHITECTURE:
    - Global flash timing dict: key -> start_time (owned by coordinator)
    - Timer tick pre-computes ALL colors in ONE pass
    - Triggers ONE repaint per window (WindowFlashOverlay)
    - Total: O(k) per tick where k = flashing elements, O(1) per window for repaint
    """
    _instance: Optional['_GlobalFlashCoordinator'] = None

    @classmethod
    def get(cls) -> '_GlobalFlashCoordinator':
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance

    def __init__(self):
        self._timer: Optional[QTimer] = None
        # GLOBAL flash timing - coordinator owns the start times
        self._flash_start_times: Dict[str, float] = {}
        # Pre-computed colors for ALL keys
        self._computed_colors: Dict[str, QColor] = {}
        # Window overlays that need repaint
        self._active_windows: Set[int] = set()  # window_id
        # Legacy: active mixins (for backwards compat during migration)
        self._active_mixins: Set['VisualUpdateMixin'] = set()
        self._tick_count = 0
        # GLOBAL pending registrations (widgets not in window hierarchy at registration time)
        self._pending_registrations: List[Tuple[str, Callable[[], Optional['FlashElement']], QWidget]] = []

    def _ensure_timer(self) -> QTimer:
        """Lazy-create timer on first use (after QApplication exists)."""
        if self._timer is None:
            self._timer = QTimer()
            self._timer.timeout.connect(self._on_global_tick)
        return self._timer

    def _start_timer(self) -> None:
        """Start the timer if not running."""
        timer = self._ensure_timer()
        if not timer.isActive():
            timer.start(FRAME_MS)

    def add_pending_registration(self, key: str, element_factory: Callable[[], Optional['FlashElement']], widget: QWidget) -> None:
        """Add a pending registration (widget not in window hierarchy yet)."""
        self._pending_registrations.append((key, element_factory, widget))

    def _process_pending_registrations(self) -> None:
        """Process all deferred element registrations (widgets now in window hierarchy)."""
        if not self._pending_registrations:
            return

        still_pending = []
        for key, element_factory, widget in self._pending_registrations:
            overlay = WindowFlashOverlay.get_for_window(widget)
            if overlay is not None:
                element = element_factory()
                if element is not None:
                    overlay.register_element(element)
                    logger.debug(f"[FLASH] Completed deferred registration: key={key}")
            else:
                still_pending.append((key, element_factory, widget))

        self._pending_registrations = still_pending

    def queue_flash_batch(self, keys: List[str]) -> None:
        """Queue multiple flashes with shared timestamp - perfect sync.

        BATCH OPTIMIZED: O(1) pending registration processing, O(overlays) once.
        """
        if not keys:
            return

        # Process pending registrations ONCE for the batch
        self._process_pending_registrations()

        # Capture ONE timestamp for ALL keys
        now = time.perf_counter()
        for key in keys:
            self._flash_start_times[key] = now

        # Find active windows ONCE - check all keys at once
        keys_set = set(keys)
        for window_id, overlay in WindowFlashOverlay._overlays.items():
            if keys_set & overlay._elements.keys():  # Set intersection
                self._active_windows.add(window_id)

        self._start_timer()
        logger.debug(f"[FLASH] queue_flash_batch: {len(keys)} keys, active_windows={len(self._active_windows)}")

    def queue_flash(self, key: str, window: Optional[QWidget] = None, timestamp: Optional[float] = None) -> None:
        """Start or retrigger flash for key (global API).

        Args:
            key: The flash key
            window: Optional window widget (for window-level overlay registration)
            timestamp: Optional shared timestamp for batch sync (all keys in batch use same time)
        """
        # Use provided timestamp or capture now - enables batch sync
        now = timestamp if timestamp is not None else time.perf_counter()
        self._flash_start_times[key] = now

        # Only process pending registrations if no timestamp (not part of a batch)
        if timestamp is None:
            self._process_pending_registrations()

        # Add ALL overlays that have this key registered
        for window_id, overlay in WindowFlashOverlay._overlays.items():
            if key in overlay._elements:
                self._active_windows.add(window_id)
        self._start_timer()
        logger.debug(f"[FLASH] queue_flash: key={key}, active_windows={len(self._active_windows)}")

    def register(self, mixin: 'VisualUpdateMixin') -> None:
        """Register a mixin as needing animation updates (legacy API)."""
        self._active_mixins.add(mixin)
        self._start_timer()
        logger.debug(f"[FLASH] register: mixin={type(mixin).__name__}, mixins={len(self._active_mixins)}")

    def unregister(self, mixin: 'VisualUpdateMixin') -> None:
        """Unregister a mixin (legacy API)."""
        self._active_mixins.discard(mixin)
        self._maybe_stop_timer()

    def _maybe_stop_timer(self) -> None:
        """Stop timer if no active animations."""
        if (not self._active_mixins and
            not self._active_windows and
            not self._flash_start_times and
            self._timer and self._timer.isActive()):
            self._timer.stop()

    def get_computed_color(self, key: str) -> Optional[QColor]:
        """Get pre-computed color for key. O(1) dict lookup."""
        return self._computed_colors.get(key)

    def _on_global_tick(self) -> None:
        """Global tick - BATCH compute ALL colors, then trigger ONE repaint per window.

        TRUE O(1) PER WINDOW:
        - Compute colors for all active keys: O(k)
        - Trigger window overlay repaints: O(w) where w = number of windows
        - Each overlay paintEvent: O(k_window) elements
        """
        now = time.perf_counter()
        self._tick_count += 1

        # ==================== BATCH COLOR COMPUTATION ====================
        self._computed_colors.clear()
        expired_keys = []

        # First: compute colors for global flash_start_times (new API)
        for key, start_time in self._flash_start_times.items():
            if now - start_time >= TOTAL_DURATION_S:
                expired_keys.append(key)
                continue
            color = compute_flash_color_at_time(start_time, now)
            if color and color.alpha() > 0:
                self._computed_colors[key] = color

        # Prune expired from global dict
        for key in expired_keys:
            del self._flash_start_times[key]

        # ==================== TRIGGER WINDOW OVERLAY REPAINTS ====================
        # O(w) where w = number of active windows with flashes
        for window_id in list(self._active_windows):
            overlay = WindowFlashOverlay._overlays.get(window_id)
            if overlay is not None:
                try:
                    overlay.setGeometry(overlay._window.rect())
                    overlay.raise_()
                    overlay.update()
                except RuntimeError:
                    self._active_windows.discard(window_id)

        # Clear active windows when no colors remain (animations complete)
        if not self._computed_colors:
            self._active_windows.clear()

        # ==================== PRUNE DEAD MIXINS (legacy API) ====================
        dead_mixins = []
        for mixin in list(self._active_mixins):
            try:
                # Prune expired animations from mixin's local dict
                still_active = mixin._prune_and_repaint(now)
                if not still_active:
                    dead_mixins.append(mixin)
            except RuntimeError:
                # Widget was deleted
                dead_mixins.append(mixin)

        for mixin in dead_mixins:
            self._active_mixins.discard(mixin)

        # Diagnostic logging
        if self._tick_count % 60 == 0:
            logger.debug(f"[FLASH TICK] windows={len(self._active_windows)}, colors={len(self._computed_colors)}, mixins={len(self._active_mixins)}")

        # Stop timer if nothing active
        self._maybe_stop_timer()


class VisualUpdateMixin:
    """Mixin providing batched visual updates at 60fps.

    TRUE O(1) ARCHITECTURE:
    - Flash timing owned by global coordinator
    - get_flash_color_for_key() returns pre-computed colors (O(1) lookup)
    - Window-level overlay renders ALL elements in ONE paintEvent

    Backwards compat: Still supports per-mixin _flash_start_times during migration.
    """

    # Legacy: per-mixin flash times (for backwards compat)
    _flash_start_times: Dict[str, float]
    _text_timer: QTimer
    _text_update_pending: bool
    _flash_overlay: Optional['FlashOverlayWidget']
    _window_overlay: Optional['WindowFlashOverlay']

    # Optional scope_id from implementing classes (e.g., ParameterFormManager)
    scope_id: Optional[str]

    def _init_visual_update_mixin(self) -> None:
        """Initialize visual update state. Call in __init__."""
        self._flash_start_times = {}
        self._text_update_pending = False
        self._flash_overlay = None  # Legacy per-form overlay
        self._window_overlay = None  # New window-level overlay

        # Text update timer (per-widget, debounced)
        self._text_timer = QTimer()
        self._text_timer.setSingleShot(True)
        self._text_timer.timeout.connect(self._execute_text_update_batch)

    def _get_scoped_flash_key(self, key: str) -> str:
        """Get flash key with scope prefix to prevent cross-window contamination.

        Automatically prepends scope_id if available (ParameterFormManager pattern).
        Prevents flashes from leaking between windows editing different scopes.

        Example:
            plate1 window: "step_0" → "plate1::step_0"
            plate2 window: "step_0" → "plate2::step_0"
        """
        if hasattr(self, 'scope_id') and self.scope_id:
            return f"{self.scope_id}::{key}"
        return key

    def register_flash_groupbox(self, key: str, groupbox: 'QWidget') -> None:
        """Register a groupbox for flash rendering.

        GAME ENGINE: Uses window-level overlay for O(1) per-window rendering.
        Defers registration if widget not yet in window hierarchy.

        Key is automatically scoped to prevent cross-window contamination.
        """
        scoped_key = self._get_scoped_flash_key(key)
        try:
            if groupbox is not None:
                overlay = WindowFlashOverlay.get_for_window(groupbox)
                if overlay is not None:
                    element = create_groupbox_element(scoped_key, groupbox)  # type: ignore
                    overlay.register_element(element)
                else:
                    # Widget not in window hierarchy yet - defer to GLOBAL coordinator
                    coordinator = _GlobalFlashCoordinator.get()
                    coordinator.add_pending_registration(
                        scoped_key, lambda k=scoped_key, g=groupbox: create_groupbox_element(k, g), groupbox
                    )
        except Exception as e:
            logger.warning(f"[FLASH] Failed to register groupbox: {e}")

    def register_flash_tree_item(self, key: str, tree: 'QTreeWidget', get_index: Callable[[], Any]) -> None:
        """Register a tree item for flash rendering (new API).

        Key is automatically scoped to prevent cross-window contamination.
        """
        scoped_key = self._get_scoped_flash_key(key)
        try:
            if tree is not None:
                overlay = WindowFlashOverlay.get_for_window(tree)
                if overlay is not None:
                    element = create_tree_item_element(scoped_key, tree, get_index)
                    overlay.register_element(element)
                    logger.debug(f"[FLASH] register_flash_tree_item: key={key} → scoped={scoped_key}, overlay={id(overlay)}")
                else:
                    # Widget not in window hierarchy yet - defer to GLOBAL coordinator
                    coordinator = _GlobalFlashCoordinator.get()
                    coordinator.add_pending_registration(
                        scoped_key, lambda k=scoped_key, t=tree, g=get_index: create_tree_item_element(k, t, g), tree
                    )
        except Exception as e:
            logger.warning(f"[FLASH] Failed to register tree item: {e}")

    def register_flash_list_item(self, key: str, list_widget: 'QListWidget', get_row: Callable[[], int]) -> None:
        """Register a list item for flash rendering (new API).

        Key is automatically scoped to prevent cross-window contamination.
        """
        scoped_key = self._get_scoped_flash_key(key)
        try:
            if list_widget is not None:
                overlay = WindowFlashOverlay.get_for_window(list_widget)
                if overlay is not None:
                    element = create_list_item_element(scoped_key, list_widget, get_row)
                    overlay.register_element(element)
                else:
                    # Widget not in window hierarchy yet - defer to GLOBAL coordinator
                    coordinator = _GlobalFlashCoordinator.get()
                    coordinator.add_pending_registration(
                        scoped_key, lambda k=scoped_key, lw=list_widget, gr=get_row: create_list_item_element(k, lw, gr), list_widget
                    )
        except Exception as e:
            logger.warning(f"[FLASH] Failed to register list item: {e}")

    def queue_visual_update(self) -> None:
        """Queue text/placeholder update (debounced)."""
        self._text_update_pending = True
        if not self._text_timer.isActive():
            self._text_timer.start(16)

    def queue_flash(self, key: str, timestamp: Optional[float] = None) -> None:
        """Start or retrigger flash for key (GLOBAL - all windows with this key flash).

        Args:
            key: The flash key
            timestamp: Optional shared timestamp for batch sync (all keys in batch use same time)
        """
        now = timestamp if timestamp is not None else time.perf_counter()
        self._flash_start_times[key] = now
        logger.info(f"⚡ FLASH_DEBUG VisualUpdateMixin.queue_flash: key={key}, total_keys={len(self._flash_start_times)}")

        # Queue in global coordinator (processes pending registrations + triggers overlay)
        coordinator = _GlobalFlashCoordinator.get()
        window = self.window() if hasattr(self, 'window') else None  # type: ignore
        coordinator.queue_flash(key, window, timestamp=now)

        # Legacy: register mixin with coordinator
        coordinator.register(self)

    def queue_flash_local(self, key: str) -> None:
        """Start flash for key in THIS WINDOW ONLY.

        Unlike queue_flash(), this only flashes the element in the current window's overlay.
        Used for:
        - Scroll-to-section navigation (local feedback)
        - ParameterFormManager resolved value changes (scope-aware, window-local)

        Key is automatically scoped to prevent cross-window contamination.
        """
        scoped_key = self._get_scoped_flash_key(key)

        window = self.window() if hasattr(self, 'window') else None  # type: ignore
        if window is None:
            logger.debug(f"[FLASH] queue_flash_local: key={key} → scoped={scoped_key}, no window")
            return

        window_id = id(window)
        coordinator = _GlobalFlashCoordinator.get()

        # Process pending registrations FIRST (elements may not be registered yet)
        coordinator._process_pending_registrations()

        overlay = WindowFlashOverlay._overlays.get(window_id)
        if overlay is None:
            logger.debug(f"[FLASH] queue_flash_local: key={key} → scoped={scoped_key}, no overlay for window {window_id}")
            return

        # Check if scoped key exists in this window's overlay
        if scoped_key not in overlay._elements:
            logger.debug(f"[FLASH] queue_flash_local: key={key} → scoped={scoped_key} not in overlay._elements")
            return

        now = time.perf_counter()
        # Store in local mixin dict (use scoped key)
        self._flash_start_times[scoped_key] = now

        # Store in coordinator for color computation (use scoped key)
        coordinator._flash_start_times[scoped_key] = now
        coordinator._active_windows.add(window_id)
        coordinator._start_timer()
        coordinator.register(self)

        logger.debug(f"[FLASH] queue_flash_local: key={key} → scoped={scoped_key}, window={window_id}, SUCCESS")

    def get_flash_color_for_key(self, key: str) -> Optional[QColor]:
        """Get pre-computed flash color for key. O(1) dict lookup.

        Used by delegates during paint - returns color from global coordinator.
        """
        return _GlobalFlashCoordinator.get().get_computed_color(key)

    def _prune_and_repaint(self, now: float, trigger_repaint: bool = True) -> bool:
        """Prune expired animations and optionally trigger repaint. Called by coordinator."""
        # Remove expired (animation complete)
        expired = [k for k, st in self._flash_start_times.items()
                   if now - st >= TOTAL_DURATION_S]
        for key in expired:
            del self._flash_start_times[key]

        # ALWAYS repaint if:
        # 1. Still animating (update colors), OR
        # 2. Just expired (clear residual pixels from overlay)
        if self._flash_start_times or expired:
            self._visual_repaint()

        # Return True if still animating (keeps mixin registered with coordinator)
        return bool(self._flash_start_times)

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

    VIEWPORT CULLING: Groupboxes outside the visible scroll area viewport
    are skipped entirely - no color computation, no paint calls.
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

    def is_groupbox_in_viewport(self, key: str) -> bool:
        """Check if a groupbox is visible in the scroll area viewport.

        VIEWPORT CULLING: Returns False for groupboxes that are scrolled
        out of view, allowing the coordinator to skip color computation.
        """
        groupbox = self._groupbox_registry.get(key)
        if groupbox is None:
            return False

        try:
            # Find the scroll area ancestor (if any)
            from PyQt6.QtWidgets import QScrollArea
            scroll_area = None
            parent = groupbox.parent()
            while parent is not None:
                if isinstance(parent, QScrollArea):
                    scroll_area = parent
                    break
                parent = parent.parent()

            if scroll_area is None:
                # No scroll area - groupbox is always "in viewport"
                return True

            # Get viewport rect in global coordinates
            viewport = scroll_area.viewport()
            if viewport is None:
                return True  # No viewport - treat as visible

            viewport_global_rect = QRect(
                viewport.mapToGlobal(viewport.rect().topLeft()),
                viewport.rect().size()
            )

            # Get groupbox rect in global coordinates
            groupbox_global_rect = QRect(
                groupbox.mapToGlobal(groupbox.rect().topLeft()),
                groupbox.rect().size()
            )

            # Check intersection
            return viewport_global_rect.intersects(groupbox_global_rect)

        except RuntimeError:
            return False  # Widget deleted

    def get_visible_keys(self) -> Set[str]:
        """Get set of keys for groupboxes currently visible in viewport.

        PERFORMANCE: Called once per tick by coordinator to determine
        which groupboxes need color computation.
        """
        return {key for key in self._groupbox_registry if self.is_groupbox_in_viewport(key)}

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

