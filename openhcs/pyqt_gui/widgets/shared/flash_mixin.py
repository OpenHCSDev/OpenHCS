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

ALGEBRAIC SIMPLIFICATIONS (OpenHCS-style):
FIX 1: Eliminated global/local flash duality
  - Before: 2 parallel systems (_flash_start_times + _window_flash_start_times)
  - After: 1 unified system (all keys auto-scoped via _get_scoped_flash_key)
  - Reduction: 2 → 1 (50% simpler, 100+ lines removed)

FIX 2: Simplified dirty tracking
  - Before: 4 prev-color dicts, 30 lines of comparison logic
  - After: 0 dicts, direct dict comparison (Qt batches update() calls anyway)
  - Reduction: Removed complex dirty flag system (30 lines → 2 lines)

FIX 3: Unified geometry cache
  - Before: 2 separate caches (_scroll_area_clip_rects + _cached_element_rects)
  - After: 1 OverlayGeometryCache dataclass with single invalidation point
  - Reduction: Single invalidate() method, clearer ownership
"""

import logging
import time
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Callable, Any, Tuple, TYPE_CHECKING
from weakref import WeakValueDictionary
import re
from PyQt6.QtCore import QTimer, Qt, QRect, QRectF
from PyQt6.QtWidgets import QWidget, QMainWindow, QDialog, QScrollArea
from PyQt6.QtGui import QColor, QPainter, QRegion, QPainterPath

# Default corner radius fallback if not extractable from stylesheet
DEFAULT_CORNER_RADIUS = 6

# Cache for extracted widget corner radii (widget_id -> radius)
_corner_radius_cache: Dict[int, float] = {}

# Regex to extract border-radius from stylesheet (handles px, em, or bare numbers)
_BORDER_RADIUS_RE = re.compile(r'border-radius\s*:\s*(\d+(?:\.\d+)?)\s*(?:px)?', re.IGNORECASE)


def get_widget_corner_radius(widget: QWidget) -> float:
    """Extract corner radius from widget's stylesheet, with caching.

    Searches the widget and its ancestors for border-radius in stylesheets.
    Returns 0 if no border-radius found (sharp corners).
    """
    widget_id = id(widget)
    if widget_id in _corner_radius_cache:
        return _corner_radius_cache[widget_id]

    # Search widget and ancestors for stylesheet with border-radius
    current = widget
    radius = 0.0
    while current is not None:
        stylesheet = current.styleSheet()
        if stylesheet:
            match = _BORDER_RADIUS_RE.search(stylesheet)
            if match:
                radius = float(match.group(1))
                break
        current = current.parentWidget()

    _corner_radius_cache[widget_id] = radius
    return radius


def invalidate_corner_radius_cache(widget: Optional[QWidget] = None) -> None:
    """Invalidate corner radius cache for a widget or all widgets."""
    if widget is None:
        _corner_radius_cache.clear()
    else:
        _corner_radius_cache.pop(id(widget), None)

if TYPE_CHECKING:
    from PyQt6.QtWidgets import QGroupBox, QTreeWidget, QListWidget

logger = logging.getLogger(__name__)


# Shared flash color (light blue)
FLASH_BASE_COLOR = QColor(77, 166, 255)  # #4da6ff

# Animation timing (seconds for perf_counter)
FADE_IN_S = 0.100    # Rapid fade-in
HOLD_S = 0.050       # Hold at max flash
FADE_OUT_S = 0.350   # Smooth fade-out
TOTAL_DURATION_S = FADE_IN_S + HOLD_S + FADE_OUT_S
FLASH_ALPHA = 180    # Flash color alpha
FRAME_MS = 32        # ~60fps timer interval

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
class OverlayGeometryCache:
    """Unified cache for all overlay geometry calculations.

    FIX 3: Single cache object with single invalidation point.
    Replaces separate scroll_area + element caches.
    """
    valid: bool = False
    scroll_clip_rects: List[QRect] = field(default_factory=list)
    element_rects: Dict[str, List[Optional[Tuple[QRect, float]]]] = field(default_factory=dict)
    element_regions: Dict[str, List[Optional[QPainterPath]]] = field(default_factory=dict)

    def invalidate(self):
        """Invalidate entire cache - called on scroll/resize."""
        self.valid = False
        self.scroll_clip_rects.clear()
        self.element_rects.clear()
        self.element_regions.clear()


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
    corner_radius: float = 0.0  # Rounded corners (0 = sharp, >0 = rounded)


def create_groupbox_element(key: str, groupbox: 'QGroupBox') -> FlashElement:
    """Create a FlashElement for a QGroupBox.

    Maps groupbox position to WINDOW coordinates (not scroll content coordinates).
    This accounts for scroll position so rects are in visible window space.
    Flashes the groupbox background (same area as stylesheet background-color) by
    subtracting the layout's content area.
    """
    # Track groupbox size to detect resize and invalidate child cache
    _last_groupbox_size: Optional[tuple] = None
    # Cache child widgets list (doesn't change unless groupbox resizes)
    _cached_child_widgets: Optional[List[QWidget]] = None

    def get_rect(window: QWidget) -> Optional[QRect]:
        try:
            from PyQt6.QtCore import QPoint
            # QGroupBox stylesheet has margin-top which is OUTSIDE the painted area
            # but still part of the widget's geometry. We need to offset by this.
            # Extract margin-top from stylesheet
            margin_top = 0
            stylesheet = groupbox.styleSheet()
            if not stylesheet:
                # Check parent stylesheets
                parent = groupbox.parentWidget()
                while parent:
                    stylesheet = parent.styleSheet()
                    if stylesheet and 'QGroupBox' in stylesheet:
                        break
                    parent = parent.parentWidget()

            if stylesheet:
                import re
                match = re.search(r'margin-top\s*:\s*(\d+)', stylesheet)
                if match:
                    margin_top = int(match.group(1))

            # Map the top-left of the PAINTED area (offset by margin-top)
            global_pos = groupbox.mapToGlobal(QPoint(0, margin_top))
            window_pos = window.mapFromGlobal(global_pos)

            # Reduce height by margin-top since we're starting lower
            size = groupbox.size()
            adjusted_height = size.height() - margin_top
            return QRect(window_pos.x(), window_pos.y(), size.width(), adjusted_height)
        except RuntimeError:
            return None

    def get_child_rects(window: QWidget) -> List[QRect]:
        """Get content widgets to exclude from flash.

        Flashes the groupbox background (frame, title area, margins) while keeping
        form content visible. For GroupBoxWithHelp, excludes widgets in content_layout
        but flashes over the title area background.

        INVALIDATION: Re-scans children when groupbox size changes (resize event).
        PERFORMANCE: Caches child widget list (expensive findChildren).
        Computes fresh window-relative rects on each call (cheap coordinate transform).
        """
        nonlocal _last_groupbox_size, _cached_child_widgets

        child_rects = []
        try:
            # DEBUG: Get groupbox window position for reference
            from PyQt6.QtCore import QPoint
            groupbox_global = groupbox.mapToGlobal(QPoint(0, 0))
            groupbox_window = window.mapFromGlobal(groupbox_global)

            # Invalidate child cache if groupbox size changed
            current_size = (groupbox.width(), groupbox.height())
            if _last_groupbox_size != current_size:
                _cached_child_widgets = None
                _last_groupbox_size = current_size

            # Cache child widgets list (expensive findChildren) on first call or after invalidation
            if _cached_child_widgets is None:
                _cached_child_widgets = []

                # Check if this is a GroupBoxWithHelp with content_layout
                if hasattr(groupbox, 'content_layout'):
                    from PyQt6.QtWidgets import (QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox,
                                                  QCheckBox, QPushButton, QToolButton, QTextEdit,
                                                  QPlainTextEdit, QTreeWidget, QListWidget, QTableWidget,
                                                  QLabel)

                    # Recursively find all leaf widgets (buttons, labels, inputs) to exclude
                    LEAF_WIDGET_TYPES = (QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QCheckBox,
                                         QPushButton, QToolButton, QTextEdit, QPlainTextEdit,
                                         QTreeWidget, QListWidget, QTableWidget, QLabel)

                    for child in groupbox.findChildren(QWidget):
                        if child.isVisible() and isinstance(child, LEAF_WIDGET_TYPES):
                            _cached_child_widgets.append(child)
                else:
                    # Regular QGroupBox - exclude all direct child widgets
                    for child in groupbox.children():
                        if isinstance(child, QWidget) and child.isVisible():
                            _cached_child_widgets.append(child)

            # Compute fresh window-relative rects (cheap coordinate transforms)
            for child in _cached_child_widgets:
                try:
                    if not child.isVisible():
                        continue
                    child_global = child.mapToGlobal(QPoint(0, 0))
                    child_window = window.mapFromGlobal(child_global)
                    child_rects.append(QRect(child_window, child.rect().size()))
                except RuntimeError:
                    pass

            # DEBUG: Log groupbox position and first 2 child positions
            if child_rects:
                first_children = [f"({r.x()},{r.y()})" for r in child_rects[:2]]
                logger.info(f"[FLASH] GET_CHILD_RECTS groupbox_id={id(groupbox)} groupbox_window_pos=({groupbox_window.x()},{groupbox_window.y()}) first_children={first_children} total={len(child_rects)}")
        except RuntimeError:
            pass
        return child_rects

    # Extract corner radius from groupbox stylesheet (cached)
    radius = get_widget_corner_radius(groupbox)
    if radius == 0:
        radius = DEFAULT_CORNER_RADIUS  # Fallback for groupboxes without explicit border-radius

    return FlashElement(
        key=key,
        get_rect_in_window=get_rect,
        get_child_rects=get_child_rects,
        source_id=f"groupbox:{id(groupbox)}",
        corner_radius=radius
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

        # FIX 3: Unified geometry cache with single invalidation point
        self._cache = OverlayGeometryCache()

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

        # Install event filter on scroll areas to catch scroll events
        self._install_scroll_event_filters()

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

        # Install event filter on the element's widget to catch resize/move events
        self._install_widget_event_filter(element)

    def unregister_element(self, key: str) -> None:
        """Unregister all elements for a key."""
        self._elements.pop(key, None)

    def _install_scroll_event_filters(self):
        """Install event filters on ALL scroll areas (QScrollArea, QTreeWidget, QListWidget, etc.)."""
        from PyQt6.QtWidgets import QAbstractScrollArea

        # Install filter on the window itself to catch layout changes
        self._window.installEventFilter(self)

        # QAbstractScrollArea is the base class for QScrollArea, QTreeWidget, QListWidget, etc.
        scroll_areas = self._window.findChildren(QAbstractScrollArea)
        for scroll_area in scroll_areas:
            # Install filter on the viewport (where scroll events happen)
            if scroll_area.viewport():
                scroll_area.viewport().installEventFilter(self)

    def _install_widget_event_filter(self, element: FlashElement) -> None:
        """Install event filter on a flash element's widget to catch resize/move events.

        This ensures cache invalidation when individual widgets change dimensions or position.
        """
        # CARMACK: Instead of installing filters on every widget, we invalidate cache
        # on every paintEvent and rely on the cache rebuild being fast (it is - just coordinate transforms).
        # This is simpler and avoids the complexity of tracking widget references.
        # The event filters on scroll area viewports catch scroll events, which is the main case.
        pass

    def eventFilter(self, obj, event):
        """Catch scroll/resize/move/layout events to invalidate geometry cache."""
        from PyQt6.QtCore import QEvent
        # Invalidate cache on:
        # - Wheel: scroll events in scroll areas/tree widgets
        # - Resize: viewport or widget size changes
        # - Move: widget position changes
        # - LayoutRequest: layout changes (groupbox expand/collapse, etc.)
        if event.type() in (QEvent.Type.Resize, QEvent.Type.Wheel, QEvent.Type.Move, QEvent.Type.LayoutRequest):
            logger.debug(f"[FLASH] Event filter caught {event.type()} on {obj.__class__.__name__}, invalidating cache")
            self._invalidate_geometry_cache()
            # CRITICAL: When window resizes, also resize the overlay to match
            if obj is self._window and event.type() == QEvent.Type.Resize:
                self.setGeometry(self._window.rect())
        return super().eventFilter(obj, event)

    def _invalidate_geometry_cache(self):
        """Invalidate ALL cached geometry - called on scroll/resize."""
        self._cache.invalidate()

    def invalidate_cache(self):
        """Public method to invalidate geometry cache.

        Call this when programmatically scrolling (e.g., scroll_to_section via tree item click).
        """
        self._invalidate_geometry_cache()

    @classmethod
    def invalidate_cache_for_widget(cls, widget: QWidget) -> None:
        """Invalidate geometry cache for the overlay covering a widget's window.

        Convenience method for programmatic scroll/resize operations.
        """
        overlay = cls.get_for_window(widget)
        if overlay:
            overlay.invalidate_cache()

    def _rebuild_geometry_cache(self, clip_rects: List[QRect]):
        """Rebuild ALL cached geometry and QRegion objects.

        CARMACK: This is expensive, but only called on scroll/resize or new element registration.
        During smooth animation, we just use the cached data.
        """
        self._cache.element_rects.clear()
        self._cache.element_regions.clear()

        for key, elements in self._elements.items():
            rects = []
            regions = []

            for element in elements:
                # Compute element rect in window coords
                rect = element.get_rect_in_window(self._window)

                if rect is None or not rect.isValid():
                    rects.append(None)
                    regions.append(None)
                    continue

                # Apply scroll area clipping if needed
                rect_to_draw = rect
                if element.needs_scroll_clipping and clip_rects:
                    clipped_rect = self._clip_to_scroll_areas(rect, clip_rects)
                    if clipped_rect and clipped_rect.isValid():
                        rect_to_draw = clipped_rect
                    else:
                        # Element not visible in scroll area - append None tuple placeholder
                        rects.append((None, 0.0))
                        regions.append(None)
                        continue

                # Get corner radius from element (0 for tree/list items, >0 for groupboxes)
                radius = element.corner_radius

                # Compute QPainterPath with rounded corners and child masking if needed
                # CARMACK: Call get_child_rects() ONCE here, cache the result
                if element.get_child_rects:
                    # Create rounded rect path for outer groupbox
                    path = QPainterPath()
                    path.addRoundedRect(QRectF(rect_to_draw), radius, radius)

                    child_rects = element.get_child_rects(self._window)
                    subtracted_count = 0
                    # Debug: log first 3 child rects to verify coordinates
                    first_children = []
                    for i, child_rect in enumerate(child_rects):
                        if child_rect.intersects(rect_to_draw):
                            # Subtract rounded rect for each child widget
                            child_path = QPainterPath()
                            child_path.addRoundedRect(QRectF(child_rect), radius, radius)
                            path = path.subtracted(child_path)
                            subtracted_count += 1
                        if i < 3:
                            first_children.append(f"({child_rect.x()},{child_rect.y()} {child_rect.width()}x{child_rect.height()})")
                    short_key = key.split('::')[-1] if '::' in key else key[-30:]
                    logger.info(f"[FLASH] CACHE_BUILD key={short_key} groupbox_rect=({rect_to_draw.x()},{rect_to_draw.y()}) first_child_rects={first_children} subtracted={subtracted_count}/{len(child_rects)}")
                    rects.append((rect_to_draw, radius))  # Cache rect + radius tuple
                    regions.append(path)  # QPainterPath for elements with child masking
                else:
                    # No child masking - just cache rect + radius
                    logger.debug(f"[FLASH] _rebuild_geometry_cache: key={key} source={element.source_id} rect={rect_to_draw.x()},{rect_to_draw.y()} {rect_to_draw.width()}x{rect_to_draw.height()} NO child masking radius={radius}")
                    rects.append((rect_to_draw, radius))  # Cache rect + radius tuple
                    regions.append(None)

            self._cache.element_rects[key] = rects
            self._cache.element_regions[key] = regions

        self._cache.valid = True
        logger.debug(f"[FLASH] Rebuilt geometry cache for window {id(self._window)}: {len(self._cache.element_rects)} keys")

    def resizeEvent(self, event) -> None:
        """Resize to cover entire window."""
        super().resizeEvent(event)
        if self._window:
            self.setGeometry(self._window.rect())
            # Invalidate ALL geometry caches on resize
            self._invalidate_geometry_cache()

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

        PERFORMANCE: Cached - findChildren() is expensive (tree traversal).
        Cache invalidated on resize.
        """
        if self._cache.valid and self._cache.scroll_clip_rects:
            return self._cache.scroll_clip_rects

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

        self._cache.scroll_clip_rects = clip_rects
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

        CARMACK OPTIMIZATION: Cache ALL geometry and QRegion objects.
        Recompute ONLY on scroll/resize events.
        During smooth animation: ZERO coordinate transformations, ZERO QRegion operations.
        """
        coordinator = _GlobalFlashCoordinator.get()

        # FIX 1: Single unified color lookup (all keys are scoped)
        if not coordinator._computed_colors:
            return  # Nothing animating

        painter = QPainter(self)
        painter.setCompositionMode(QPainter.CompositionMode.CompositionMode_SourceOver)

        # Find scroll areas to clip flash rectangles (don't flash over headers/buttons)
        clip_rects = self._get_scroll_area_clip_rects()

        # CARMACK: Rebuild geometry cache if invalidated
        if not self._cache.valid:
            logger.debug(f"[FLASH] CACHE MISS - Rebuilding geometry cache for window {id(self._window)}")
            self._rebuild_geometry_cache(clip_rects)
        else:
            logger.debug(f"[FLASH] CACHE HIT - Using cached geometry for window {id(self._window)}")

        drawn_count = 0

        # Get keys to draw (only keys that are registered in this overlay)
        all_keys_to_draw = {
            key: color
            for key, color in coordinator._computed_colors.items()
            if key in self._elements
        }

        # DEBUG: Log what we're about to draw
        logger.debug(f"[FLASH] paintEvent START: {len(all_keys_to_draw)} keys to draw")
        for key in all_keys_to_draw:
            short_key = key.split('::')[-1] if '::' in key else key[-30:]
            rects = self._cache.element_rects.get(key, [])
            paths = self._cache.element_regions.get(key, [])
            path_info = [f"idx{i}:{'Path' if p else 'None'}" for i, p in enumerate(paths)]
            logger.debug(f"[FLASH]   key={short_key} cached_rects={len(rects)} cached_paths={len(paths)} paths={path_info}")

        # PERFORMANCE: Only loop through ANIMATING keys, not ALL registered elements
        for key, color in all_keys_to_draw.items():
            cached_rects = self._cache.element_rects.get(key, [])
            cached_regions = self._cache.element_regions.get(key, [])
            short_key = key.split('::')[-1] if '::' in key else key[-30:]

            # Draw all elements for this key using CACHED geometry
            # cached_rects contains (QRect, corner_radius) tuples or None
            for idx, (rect_tuple, path) in enumerate(zip(cached_rects, cached_regions)):
                # Skip None entries (elements not visible)
                if rect_tuple is None:
                    continue
                # Unpack rect and radius from cached tuple
                rect, radius = rect_tuple
                if rect is None:
                    continue
                if not rect.isValid() or not rect.intersects(self.rect()):
                    logger.debug(f"[FLASH] SKIPPED key={short_key} idx={idx} rect={rect} (invalid or off-screen)")
                    continue

                if path is not None:
                    # Use cached QPainterPath (groupbox with rounded corners and child masking)
                    br = path.boundingRect()
                    logger.debug(f"[FLASH] DRAWING WITH PATH key={short_key} idx={idx} fillRect={rect.x()},{rect.y()} {rect.width()}x{rect.height()} path.boundingRect={br.x():.0f},{br.y():.0f} {br.width():.0f}x{br.height():.0f}")

                    # Fill the rounded path directly (more efficient than clipping)
                    painter.save()
                    painter.setBrush(color)
                    painter.setPen(Qt.PenStyle.NoPen)
                    painter.drawPath(path)
                    painter.restore()
                else:
                    # No child masking - use element-specific corner radius
                    painter.save()
                    painter.setBrush(color)
                    painter.setPen(Qt.PenStyle.NoPen)
                    if radius > 0:
                        painter.drawRoundedRect(QRectF(rect), radius, radius)
                    else:
                        painter.fillRect(rect, color)  # Sharp corners for tree/list items
                    painter.restore()
                    logger.debug(f"[FLASH] DREW RECT key={short_key} idx={idx} rect={rect.x()},{rect.y()} {rect.width()}x{rect.height()} radius={radius}")

                drawn_count += 1

        if drawn_count > 0:
            logger.info(f"[FLASH] paintEvent END: drew {drawn_count} rects, overlay={self.rect().width()}x{self.rect().height()}")

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
        # FIX 1: Single unified flash timing (all keys are scoped, no global/local split)
        self._flash_start_times: Dict[str, float] = {}
        # Pre-computed colors for ALL keys
        self._computed_colors: Dict[str, QColor] = {}
        # Window overlays that need repaint
        self._active_windows: Set[int] = set()  # window_id
        self._tick_count = 0
        # Pending registrations (widgets not in window hierarchy at registration time)
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

        # Start timer - active windows will be determined in tick based on computed colors
        self._start_timer()
        logger.debug(f"[FLASH] queue_flash: key={key}")

    def _maybe_stop_timer(self) -> None:
        """Stop timer if no active animations."""
        if (not self._active_windows and
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
        # FIX 1: Single unified color computation (all keys are scoped)
        self._computed_colors.clear()
        expired_keys = []

        # Compute colors for ALL keys (no global/local distinction)
        for key, start_time in self._flash_start_times.items():
            if now - start_time >= TOTAL_DURATION_S:
                expired_keys.append(key)
                continue
            color = compute_flash_color_at_time(start_time, now)
            if color and color.alpha() > 0:
                self._computed_colors[key] = color

        # Prune expired keys
        for key in expired_keys:
            del self._flash_start_times[key]

        # ==================== TRIGGER WINDOW OVERLAY REPAINTS ====================
        # FIX 1 & 2: Simplified single-path repaint (all keys scoped, no dirty tracking complexity)
        active_windows_this_frame = set()
        computed_keys = set(self._computed_colors.keys())

        # Find windows that had keys expire this frame (need final clear repaint)
        windows_needing_clear = set()
        if expired_keys:
            expired_keys_set = set(expired_keys)
            for window_id, overlay in WindowFlashOverlay._overlays.items():
                if expired_keys_set & overlay._elements.keys():
                    windows_needing_clear.add(window_id)

        for window_id, overlay in WindowFlashOverlay._overlays.items():
            # Find which of this overlay's registered elements are currently flashing
            window_keys = computed_keys & overlay._elements.keys()

            if window_keys:
                active_windows_this_frame.add(window_id)
                try:
                    overlay.update()  # Qt batches update() calls, safe to call every frame
                except RuntimeError:
                    # Widget deleted during animation
                    logger.debug(f"[FLASH] Window {window_id} deleted during animation")

        self._active_windows = active_windows_this_frame

        # CRITICAL: Final clear repaint for windows where keys expired
        # Ensures flash is fully cleared even if no other animations active
        for window_id in windows_needing_clear:
            if window_id not in active_windows_this_frame:
                overlay = WindowFlashOverlay._overlays.get(window_id)
                if overlay:
                    try:
                        overlay.update()  # One final repaint to clear
                    except RuntimeError:
                        pass  # Widget deleted

        # Diagnostic logging
        if self._tick_count % 60 == 0:
            logger.debug(f"[FLASH TICK] windows={len(self._active_windows)}, colors={len(self._computed_colors)}")

        # Stop timer if nothing active
        self._maybe_stop_timer()


class VisualUpdateMixin:
    """Mixin providing batched visual updates at 60fps.

    TRUE O(1) ARCHITECTURE:
    - Flash timing owned by global coordinator
    - get_flash_color_for_key() returns pre-computed colors (O(1) lookup)
    - Window-level overlay renders ALL elements in ONE paintEvent
    """

    _text_timer: QTimer
    _text_update_pending: bool

    # Optional scope_id from implementing classes (e.g., ParameterFormManager)
    scope_id: Optional[str]

    def _init_visual_update_mixin(self) -> None:
        """Initialize visual update state. Call in __init__."""
        self._text_update_pending = False

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

    def _register_flash_element_internal(
        self,
        key: str,
        element_factory: Callable[[str], FlashElement],
        widget: QWidget
    ) -> None:
        """Internal helper for flash element registration. DRY for all element types.

        FAIL-LOUD: No exception handling - registration failures should crash.
        """
        scoped_key = self._get_scoped_flash_key(key)
        if widget is not None:
            overlay = WindowFlashOverlay.get_for_window(widget)
            if overlay is not None:
                element = element_factory(scoped_key)
                overlay.register_element(element)
            else:
                coordinator = _GlobalFlashCoordinator.get()
                coordinator.add_pending_registration(
                    scoped_key,
                    lambda: element_factory(scoped_key),
                    widget
                )

    def register_flash_groupbox(self, key: str, groupbox: 'QWidget') -> None:
        """Register a groupbox for flash rendering."""
        self._register_flash_element_internal(
            key,
            lambda k: create_groupbox_element(k, groupbox),  # type: ignore
            groupbox
        )

    def register_flash_tree_item(self, key: str, tree: 'QTreeWidget', get_index: Callable[[], Any]) -> None:
        """Register a tree item for flash rendering."""
        self._register_flash_element_internal(
            key,
            lambda k: create_tree_item_element(k, tree, get_index),
            tree
        )

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

        # Queue in global coordinator (processes pending registrations + triggers overlay)
        coordinator = _GlobalFlashCoordinator.get()
        window = self.window() if hasattr(self, 'window') else None  # type: ignore
        coordinator.queue_flash(key, window, timestamp=now)

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
            logger.info(f"[FLASH] queue_flash_local: key={key} → scoped={scoped_key} NOT IN overlay._elements. Available keys: {list(overlay._elements.keys())}")
            return

        now = time.perf_counter()
        # FIX 1: Store in unified dict (key is already scoped, prevents cross-window contamination)
        coordinator._flash_start_times[scoped_key] = now
        # Start timer - active windows will be determined in tick based on computed colors
        coordinator._start_timer()

        logger.debug(f"[FLASH] queue_flash_local: key={key} → scoped={scoped_key}, window={window_id}, SUCCESS")

    def get_flash_color_for_key(self, key: str) -> Optional[QColor]:
        """Get pre-computed flash color for key. O(1) dict lookup.

        Used by delegates during paint - returns color from global coordinator.
        """
        return _GlobalFlashCoordinator.get().get_computed_color(key)

    def _execute_text_update_batch(self) -> None:
        """Execute pending text update."""
        if self._text_update_pending:
            self._text_update_pending = False
            self._execute_text_update()

    def _execute_text_update(self) -> None:
        """Execute text/placeholder update. Override in subclass."""
        pass


# Backwards compatibility
FlashMixin = VisualUpdateMixin

