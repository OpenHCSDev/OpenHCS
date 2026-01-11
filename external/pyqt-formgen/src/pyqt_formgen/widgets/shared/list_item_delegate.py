"""
Shared QListWidget item delegate for rendering multiline items with grey preview text.

Single source of truth for list item rendering across PipelineEditor, PlateManager,
and other widgets that display items with preview labels.
"""

from dataclasses import dataclass, field
from typing import List, Optional, Set
from PyQt6.QtWidgets import QStyledItemDelegate, QStyleOptionViewItem, QStyle
from PyQt6.QtGui import QPainter, QColor, QFont, QFontMetrics, QPen
from PyQt6.QtCore import Qt, QRect

from pyqt_formgen.widgets.shared.scope_color_utils import tint_color_perceptual

# Custom data role for scope color scheme (must match manager)
SCOPE_SCHEME_ROLE = Qt.ItemDataRole.UserRole + 10
# Flash key role - stores scope_id for flash color lookup
FLASH_KEY_ROLE = Qt.ItemDataRole.UserRole + 11
# Per-field styling roles
LAYOUT_ROLE = Qt.ItemDataRole.UserRole + 12  # StyledTextLayout for structured rendering
DIRTY_FIELDS_ROLE = Qt.ItemDataRole.UserRole + 13  # Set[str] - dotted paths of dirty fields
SIG_DIFF_FIELDS_ROLE = Qt.ItemDataRole.UserRole + 14  # Set[str] - dotted paths of sig-diff fields

# Backwards compat alias
SEGMENTS_ROLE = LAYOUT_ROLE


@dataclass(frozen=True)
class Segment:
    """A styled text segment with field path for dirty/sig-diff matching.

    Attributes:
        text: Display text for this segment
        field_path: Dotted path for styling lookup (e.g., 'path_planning_config.well_filter')
                   None = no styling, '' = root path (matches any dirty/sig-diff field)
    """
    text: str
    field_path: Optional[str] = None


@dataclass
class StyledTextLayout:
    """Structured layout for styled text rendering. No string parsing needed.

    The delegate renders segments directly from this structure, adding separators
    and brackets as needed. Display text is generated for Qt storage but never parsed.

    Attributes:
        name: Item name segment (field_path='' for root, inherits any dirty/sig-diff)
        status_prefix: Status prefix before name (e.g., "✓ Init ")
        first_line_segments: Segments after name on line 1 (inline preview format)
        detail_line: Plain text detail line (e.g., path) - no styling
        preview_segments: Preview line segments (e.g., W:8, Seq:C,Z, wf:[3])
        config_segments: Config indicator segments (e.g., NAP, FIJI, MAT) shown in brackets
        multiline: True = multiline format with └─ preview, False = inline (seg1 | seg2)
    """
    name: Segment
    status_prefix: str = ""
    first_line_segments: List[Segment] = field(default_factory=list)
    detail_line: str = ""
    preview_segments: List[Segment] = field(default_factory=list)
    config_segments: List[Segment] = field(default_factory=list)
    multiline: bool = False

    def to_display_text(self) -> str:
        """Generate display text for Qt storage and fallback rendering."""
        # Line 1: status + name + first_line preview
        line1 = f"{self.status_prefix}▶ {self.name.text}" if self.status_prefix else f"▶ {self.name.text}"
        if self.first_line_segments:
            preview = " | ".join(seg.text for seg in self.first_line_segments)
            line1 = f"{line1}  ({preview})"

        if not self.multiline:
            # Inline format: everything on line 1
            if self.preview_segments or self.config_segments:
                all_segs = self.preview_segments + self.config_segments
                preview = " | ".join(seg.text for seg in all_segs)
                if not self.first_line_segments:
                    line1 = f"{line1}  ({preview})"
            return line1

        # Multiline format
        lines = [line1]
        if self.detail_line:
            lines.append(f"  {self.detail_line}")

        # Preview line with └─
        preview_parts = []
        if self.preview_segments:
            preview_parts.append(" | ".join(seg.text for seg in self.preview_segments))
        if self.config_segments:
            labels = [seg.text for seg in self.config_segments]
            preview_parts.append(f"configs=[{', '.join(labels)}]")
        if preview_parts:
            lines.append(f"  └─ {' | '.join(preview_parts)}")

        return "\n".join(lines)

    def all_segments(self) -> List[Segment]:
        """Get all segments for dirty/sig-diff field set storage."""
        return [self.name] + self.first_line_segments + self.preview_segments + self.config_segments


class StyledText(str):
    """String subclass carrying layout for per-field styling.

    Since this IS a str, it passes through Qt unchanged. The layout
    attribute must be stored separately in item data (Qt doesn't preserve
    Python subclass attributes).
    """
    layout: Optional[StyledTextLayout]

    def __new__(cls, layout: StyledTextLayout):
        display_text = layout.to_display_text()
        instance = super().__new__(cls, display_text)
        instance.layout = layout
        return instance

    @property
    def segments(self) -> List[tuple]:
        """Backwards compat: return segments as list of tuples."""
        if self.layout:
            return [(seg.text, seg.field_path) for seg in self.layout.all_segments()]
        return []

# Border patterns matching ScopedBorderMixin
BORDER_PATTERNS = {
    "solid": (Qt.PenStyle.SolidLine, None),
    "dashed": (Qt.PenStyle.DashLine, [8, 6]),
    "dotted": (Qt.PenStyle.DotLine, [2, 6]),
    "dashdot": (Qt.PenStyle.DashDotLine, [8, 4, 2, 4]),
}


class MultilinePreviewItemDelegate(QStyledItemDelegate):
    """Custom delegate to render multiline items with grey preview text.

    TRUE O(1) ARCHITECTURE: Flash effects are rendered by WindowFlashOverlay.
    This delegate does NOT paint flash backgrounds - window overlay handles all flash
    rendering in a single paintEvent for O(1) per window.

    Supports:
    - Multiline text rendering (automatic height calculation)
    - Grey preview text for lines containing specific markers
    - Proper hover/selection/border rendering
    - Configurable colors for normal/preview/selected text
    """

    def __init__(self, name_color: QColor, preview_color: QColor, selected_text_color: QColor,
                 parent=None, manager=None):
        """Initialize delegate with color scheme.

        Args:
            name_color: Color for normal text lines
            preview_color: Color for preview text lines (grey)
            selected_text_color: Color for text when item is selected
            parent: Parent widget (QListWidget)
            manager: Manager widget (unused - kept for API compat)
        """
        super().__init__(parent)
        self.name_color = name_color
        self.preview_color = preview_color
        self.selected_text_color = selected_text_color
        self._manager = manager
        # NOTE: Flash rendering moved to WindowFlashOverlay for O(1) performance

    def paint(self, painter: QPainter, option: QStyleOptionViewItem, index) -> None:
        """Paint the item with multiline support and flash behind text."""
        from PyQt6.QtGui import QFont, QFontMetrics

        # Prepare a copy to let style draw backgrounds, hover, selection, borders, etc.
        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)

        # Capture text and prevent default text draw
        text = opt.text or ""
        opt.text = ""

        # Calculate border inset (used for background and flash)
        scheme = index.data(SCOPE_SCHEME_ROLE)
        border_inset = 0
        layers = None
        if scheme is not None:
            layers = getattr(scheme, "step_border_layers", None)
            if layers:
                border_inset = sum(layer[0] for layer in layers)
        content_rect = option.rect.adjusted(border_inset, border_inset, -border_inset, -border_inset)

        # Scope-based background: match border colors
        self._paint_scope_background(painter, content_rect, scheme, layers)

        # Flash effect - drawn BEHIND text but inside borders
        flash_key = index.data(FLASH_KEY_ROLE)
        if flash_key and self._manager is not None:
            flash_color = self._manager.get_flash_color_for_key(flash_key)
            if flash_color and flash_color.alpha() > 0:
                if scheme:
                    from pyqt_formgen.widgets.shared.scope_color_utils import tint_color_perceptual
                    base_rgb = getattr(scheme, "base_color_rgb", None)
                    item_layers = getattr(scheme, "step_border_layers", None)
                    if base_rgb and item_layers:
                        _, tint_idx, _ = (item_layers[0] + ("solid",))[:3]
                        computed_color = tint_color_perceptual(base_rgb, tint_idx).darker(120)
                        computed_color.setAlpha(flash_color.alpha())
                        flash_color = computed_color

                if layers and len(layers) > 1:
                    self._paint_checkerboard_flash(painter, content_rect, flash_color)
                else:
                    painter.fillRect(content_rect, flash_color)

        # Let the style draw selection, hover, borders
        self.parent().style().drawControl(QStyle.ControlElement.CE_ItemViewItem, opt, painter, self.parent())

        # Now draw text manually with custom colors
        painter.save()

        is_selected = bool(option.state & QStyle.StateFlag.State_Selected)
        is_disabled = index.data(Qt.ItemDataRole.UserRole + 1) or False

        # Get structured layout - no string parsing needed!
        layout = index.data(LAYOUT_ROLE)
        dirty_fields = index.data(DIRTY_FIELDS_ROLE) or set()
        sig_diff_fields = index.data(SIG_DIFF_FIELDS_ROLE) or set()

        base_font = QFont(option.font)
        base_font.setStrikeOut(is_disabled)
        base_font.setUnderline(False)

        fm = QFontMetrics(base_font)
        line_height = fm.height()
        text_rect = option.rect
        x_start = text_rect.left() + 5
        y_offset = text_rect.top() + fm.ascent() + 3

        if isinstance(layout, StyledTextLayout):
            # Structured rendering - iterate segments directly, no parsing
            self._paint_from_layout(
                painter, layout, dirty_fields, sig_diff_fields,
                base_font, fm, x_start, y_offset, line_height, is_selected
            )
        else:
            # Fallback: plain text rendering (no layout available)
            self._paint_plain_text(painter, text, base_font, x_start, y_offset, line_height, is_selected)

        painter.restore()

        if scheme is not None:
            self._paint_border_layers(painter, option.rect, scheme)

    def _has_field_match(self, path: Optional[str], field_set: Set[str]) -> bool:
        """Check if field_path matches any in the set.

        Path '' (root) matches if set is non-empty.
        Other paths: exact match or prefix match for container configs.
        """
        if path is None:
            return False
        if path == '':
            return bool(field_set)
        return path in field_set or any(f.startswith(path + '.') for f in field_set)

    def _draw_segment(
        self,
        painter: QPainter,
        x: int,
        y: int,
        segment: Segment,
        dirty_fields: Set[str],
        sig_diff_fields: Set[str],
        base_font: 'QFont',
        color: QColor,
    ) -> int:
        """Draw a segment with dirty/sig-diff styling. Returns new x position."""
        from PyQt6.QtGui import QFont, QFontMetrics

        is_dirty = self._has_field_match(segment.field_path, dirty_fields)
        has_sig_diff = self._has_field_match(segment.field_path, sig_diff_fields)

        # Draw text with underline if sig-diff
        font = QFont(base_font)
        font.setUnderline(has_sig_diff)
        painter.setFont(font)
        painter.setPen(color)
        painter.drawText(x, y, segment.text)
        x += QFontMetrics(font).horizontalAdvance(segment.text)

        # Draw asterisk WITHOUT underline if dirty
        if is_dirty:
            painter.setFont(base_font)
            painter.drawText(x, y, "*")
            x += QFontMetrics(base_font).horizontalAdvance("*")

        return x

    def _draw_plain(self, painter: QPainter, x: int, y: int, text: str, font: 'QFont', color: QColor) -> int:
        """Draw plain text without styling. Returns new x position."""
        from PyQt6.QtGui import QFontMetrics
        painter.setFont(font)
        painter.setPen(color)
        painter.drawText(x, y, text)
        return x + QFontMetrics(font).horizontalAdvance(text)

    def _paint_from_layout(
        self,
        painter: QPainter,
        layout: StyledTextLayout,
        dirty_fields: Set[str],
        sig_diff_fields: Set[str],
        base_font: 'QFont',
        fm: 'QFontMetrics',
        x_start: int,
        y_offset: int,
        line_height: int,
        is_selected: bool,
    ) -> None:
        """Paint from structured layout - no string parsing needed."""
        name_color = self.selected_text_color if is_selected else self.name_color
        preview_color = self.selected_text_color if is_selected else self.preview_color

        # === Line 1: status_prefix + "▶ " + name + first_line_segments ===
        x = x_start

        # Status prefix (e.g., "✓ Init ")
        if layout.status_prefix:
            x = self._draw_plain(painter, x, y_offset, layout.status_prefix, base_font, name_color)

        # Arrow prefix
        x = self._draw_plain(painter, x, y_offset, "▶ ", base_font, name_color)

        # Name segment with styling
        x = self._draw_segment(painter, x, y_offset, layout.name, dirty_fields, sig_diff_fields, base_font, name_color)

        # First line segments (inline preview on name line)
        if layout.first_line_segments:
            x = self._draw_plain(painter, x, y_offset, "  (", base_font, preview_color)
            for i, seg in enumerate(layout.first_line_segments):
                if i > 0:
                    x = self._draw_plain(painter, x, y_offset, " | ", base_font, preview_color)
                x = self._draw_segment(painter, x, y_offset, seg, dirty_fields, sig_diff_fields, base_font, preview_color)
            x = self._draw_plain(painter, x, y_offset, ")", base_font, preview_color)

        if not layout.multiline:
            # Inline format: preview_segments also on line 1 if no first_line_segments
            if layout.preview_segments and not layout.first_line_segments:
                x = self._draw_plain(painter, x, y_offset, "  (", base_font, preview_color)
                for i, seg in enumerate(layout.preview_segments):
                    if i > 0:
                        x = self._draw_plain(painter, x, y_offset, " | ", base_font, preview_color)
                    x = self._draw_segment(painter, x, y_offset, seg, dirty_fields, sig_diff_fields, base_font, preview_color)
                x = self._draw_plain(painter, x, y_offset, ")", base_font, preview_color)
            return

        # === Multiline format ===
        y_offset += line_height

        # Line 2: detail line (plain text, no styling)
        if layout.detail_line:
            self._draw_plain(painter, x_start, y_offset, f"  {layout.detail_line}", base_font, preview_color)
            y_offset += line_height

        # Line 3: "  └─ " + preview_segments + " | configs=[config_segments]"
        if layout.preview_segments or layout.config_segments:
            x = x_start
            x = self._draw_plain(painter, x, y_offset, "  └─ ", base_font, preview_color)

            # Preview segments (e.g., W:8, Seq:C,Z, wf:[3])
            for i, seg in enumerate(layout.preview_segments):
                if i > 0:
                    x = self._draw_plain(painter, x, y_offset, " | ", base_font, preview_color)
                x = self._draw_segment(painter, x, y_offset, seg, dirty_fields, sig_diff_fields, base_font, preview_color)

            # Separator between preview and config segments
            if layout.preview_segments and layout.config_segments:
                x = self._draw_plain(painter, x, y_offset, " | ", base_font, preview_color)

            # Config segments in brackets (e.g., configs=[NAP, FIJI, MAT])
            if layout.config_segments:
                x = self._draw_plain(painter, x, y_offset, "configs=[", base_font, preview_color)
                for i, seg in enumerate(layout.config_segments):
                    if i > 0:
                        x = self._draw_plain(painter, x, y_offset, ", ", base_font, preview_color)
                    x = self._draw_segment(painter, x, y_offset, seg, dirty_fields, sig_diff_fields, base_font, preview_color)
                x = self._draw_plain(painter, x, y_offset, "]", base_font, preview_color)

    def _paint_plain_text(
        self,
        painter: QPainter,
        text: str,
        base_font: 'QFont',
        x_start: int,
        y_offset: int,
        line_height: int,
        is_selected: bool,
    ) -> None:
        """Fallback: paint plain text without per-field styling."""
        text = text.replace('\u2028', '\n')
        lines = text.split('\n')
        name_color = self.selected_text_color if is_selected else self.name_color
        preview_color = self.selected_text_color if is_selected else self.preview_color

        for line_index, line in enumerate(lines):
            is_preview_line = line.strip().startswith('└─')
            color = preview_color if is_preview_line else name_color
            self._draw_plain(painter, x_start, y_offset, line, base_font, color)
            y_offset += line_height

    def _paint_scope_background(self, painter: QPainter, content_rect: QRect, scheme, layers) -> None:
        """Paint background matching border colors.

        If single layer: solid color matching border.
        If multiple layers: grid pattern of layer colors.
        """
        from pyqt_formgen.widgets.shared.scope_visual_config import (
            ScopeColorScheme,
            ScopeVisualConfig,
        )

        if not isinstance(scheme, ScopeColorScheme):
            return

        base_rgb = getattr(scheme, "base_color_rgb", None)
        if not base_rgb:
            return

        opacity = ScopeVisualConfig.STEP_ITEM_BG_OPACITY

        if not layers or len(layers) == 1:
            # Single layer: solid background matching first layer color
            if layers:
                _, tint_idx, _ = (layers[0] + ("solid",))[:3]
            else:
                tint_idx = 1  # default to middle tint
            color = tint_color_perceptual(base_rgb, tint_idx)
            color.setAlphaF(opacity)
            painter.fillRect(content_rect, color)
        else:
            # Multiple layers: draw checkerboard with 2 perceptually distinct lightness levels
            cell_size = 8  # pixels per grid cell
            painter.save()
            painter.setClipRect(content_rect)

            # Use dark (tint 0) and light (tint 2) variants - no hue shift
            color1 = tint_color_perceptual(base_rgb, 0)  # dark
            color2 = tint_color_perceptual(base_rgb, 2)  # light
            color1.setAlphaF(opacity)
            color2.setAlphaF(opacity)

            # Draw checkerboard
            for x in range(content_rect.left(), content_rect.right(), cell_size):
                for y in range(content_rect.top(), content_rect.bottom(), cell_size):
                    is_even = ((x // cell_size) + (y // cell_size)) % 2 == 0
                    cell_rect = QRect(x, y, cell_size, cell_size)
                    painter.fillRect(cell_rect.intersected(content_rect), color1 if is_even else color2)

            painter.restore()

    def _paint_checkerboard_flash(self, painter: QPainter, content_rect: QRect, flash_color: QColor) -> None:
        """Paint flash effect as checkerboard for multi-layer items."""
        cell_size = 8
        painter.save()
        painter.setClipRect(content_rect)

        # Create light/dark variants of flash color
        base_alpha = flash_color.alphaF()
        color1 = QColor(flash_color)
        color2 = QColor(flash_color)
        color1.setAlphaF(base_alpha * 0.6)  # darker cells
        color2.setAlphaF(base_alpha * 1.4)  # lighter cells (capped by Qt)

        for x in range(content_rect.left(), content_rect.right(), cell_size):
            for y in range(content_rect.top(), content_rect.bottom(), cell_size):
                is_even = ((x // cell_size) + (y // cell_size)) % 2 == 0
                cell_rect = QRect(x, y, cell_size, cell_size)
                painter.fillRect(cell_rect.intersected(content_rect), color1 if is_even else color2)

        painter.restore()

    def _paint_border_layers(self, painter: QPainter, rect: QRect, scheme) -> None:
        """Paint layered borders matching window border style.

        Uses same algorithm as ScopedBorderMixin._paint_border_layers() to ensure
        list items have identical borders to their corresponding windows.
        """
        from pyqt_formgen.widgets.shared.scope_visual_config import ScopeColorScheme

        if not isinstance(scheme, ScopeColorScheme):
            return

        layers = getattr(scheme, "step_border_layers", None)
        base_rgb = getattr(scheme, "base_color_rgb", None)

        if not layers or not base_rgb:
            # Fallback: simple border using orchestrator border color
            border_color = scheme.to_qcolor_orchestrator_border()
            painter.save()
            pen = QPen(border_color, 2)
            pen.setStyle(Qt.PenStyle.SolidLine)
            painter.setPen(pen)
            painter.drawRect(rect.adjusted(1, 1, -2, -2))
            painter.restore()
            return

        # Paint layered borders (same logic as ScopedBorderMixin)
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        inset = 0
        for layer in layers:
            width, tint_idx, pattern = (layer + ("solid",))[:3]
            color = tint_color_perceptual(base_rgb, tint_idx).darker(120)

            pen = QPen(color, width)
            style, dash_pattern = BORDER_PATTERNS.get(pattern, BORDER_PATTERNS["solid"])
            pen.setStyle(style)
            if dash_pattern:
                pen.setDashPattern(dash_pattern)

            offset = int(inset + width / 2)
            painter.setPen(pen)
            painter.drawRect(rect.adjusted(offset, offset, -offset - 1, -offset - 1))
            inset += width

        painter.restore()

    def sizeHint(self, option: QStyleOptionViewItem, index) -> 'QSize':
        """Calculate size hint based on number of lines in text."""
        from PyQt6.QtCore import QSize

        # Get text from index
        text = index.data(Qt.ItemDataRole.DisplayRole) or ""

        # Qt converts \n to \u2028 (Unicode line separator) in QListWidgetItem text
        # Normalize to \n for processing
        text = text.replace('\u2028', '\n')
        lines = text.split('\n')
        num_lines = len(lines)

        # Calculate height
        fm = QFontMetrics(option.font)
        line_height = fm.height()
        base_height = 25  # Base height for first line
        additional_height = 18  # Height per additional line

        if num_lines == 1:
            total_height = base_height
        else:
            total_height = base_height + (additional_height * (num_lines - 1))

        # Add some padding
        total_height += 4

        # Calculate width based on longest line (for horizontal scrolling)
        max_width = 0
        for line in lines:
            line_width = fm.horizontalAdvance(line)
            max_width = max(max_width, line_width)

        # Add padding for left offset and some extra space
        total_width = max_width + 20  # 10px padding on each side

        return QSize(total_width, total_height)
