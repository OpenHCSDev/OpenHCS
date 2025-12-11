"""
Shared QListWidget item delegate for rendering multiline items with grey preview text.

Single source of truth for list item rendering across PipelineEditor, PlateManager,
and other widgets that display items with preview labels.
"""

from typing import Tuple
from PyQt6.QtWidgets import QStyledItemDelegate, QStyleOptionViewItem, QStyle
from PyQt6.QtGui import QPainter, QColor, QFontMetrics, QPen
from PyQt6.QtCore import Qt, QRect

from openhcs.pyqt_gui.widgets.shared.scope_color_utils import tint_color_perceptual

# Custom data role for scope color scheme (must match manager)
SCOPE_SCHEME_ROLE = Qt.ItemDataRole.UserRole + 10
# Legacy role (kept for compatibility) - now stores full ScopeColorScheme
SCOPE_BORDER_ROLE = SCOPE_SCHEME_ROLE
# Flash key role - stores scope_id for flash color lookup
FLASH_KEY_ROLE = Qt.ItemDataRole.UserRole + 11

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
        # If multiple layers, create a grid pattern of the layer colors
        self._paint_scope_background(painter, content_rect, scheme, layers)

        # Flash effect - drawn BEHIND text but inside borders
        # For multi-layer items, flash uses checkerboard pattern
        flash_key = index.data(FLASH_KEY_ROLE)
        if flash_key and self._manager is not None:
            # Get flash alpha from coordinator (handles animation timing)
            flash_color = self._manager.get_flash_color_for_key(flash_key)
            if flash_color and flash_color.alpha() > 0:
                # CRITICAL: Use the scheme stored on THIS item for color computation
                # This ensures flash color matches border color even after reordering
                # (coordinator may compute from scope_id token, not visual position)
                if scheme:
                    from openhcs.pyqt_gui.widgets.shared.scope_color_utils import tint_color_perceptual
                    base_rgb = getattr(scheme, "base_color_rgb", None)
                    item_layers = getattr(scheme, "step_border_layers", None)
                    if base_rgb and item_layers:
                        _, tint_idx, _ = (item_layers[0] + ("solid",))[:3]
                        # Compute color matching border, but use coordinator's alpha
                        computed_color = tint_color_perceptual(base_rgb, tint_idx).darker(120)
                        computed_color.setAlpha(flash_color.alpha())
                        flash_color = computed_color

                if layers and len(layers) > 1:
                    # Multi-layer: flash with checkerboard pattern
                    self._paint_checkerboard_flash(painter, content_rect, flash_color)
                else:
                    painter.fillRect(content_rect, flash_color)

        # Let the style draw selection, hover, borders
        self.parent().style().drawControl(QStyle.ControlElement.CE_ItemViewItem, opt, painter, self.parent())

        # Now draw text manually with custom colors
        painter.save()

        # Determine text color based on selection state
        is_selected = option.state & QStyle.StateFlag.State_Selected

        # Check if item is disabled (stored in UserRole+1) - for PipelineEditor strikethrough
        is_disabled = index.data(Qt.ItemDataRole.UserRole + 1) or False

        # Use strikethrough font for disabled items
        from PyQt6.QtGui import QFont, QFontMetrics
        font = QFont(option.font)
        if is_disabled:
            font.setStrikeOut(True)
        painter.setFont(font)

        # Split text into lines
        # Qt converts \n to \u2028 (Unicode line separator) in QListWidgetItem text
        # So we need to split on both \n and \u2028
        text = text.replace('\u2028', '\n')  # Normalize to \n
        lines = text.split('\n')

        # Calculate line height
        fm = QFontMetrics(font)
        line_height = fm.height()

        # Starting position for text with proper padding
        text_rect = option.rect
        x_offset = text_rect.left() + 5  # Left padding
        y_offset = text_rect.top() + fm.ascent() + 3  # Top padding

        # Draw each line with appropriate color
        for line in lines:
            # Determine if this is a preview line (starts with "  └─" or contains "  (")
            is_preview_line = line.strip().startswith('└─')

            # Check for inline preview format: "name  (preview)"
            sep_idx = line.find("  (")
            if sep_idx != -1 and line.endswith(")") and not is_preview_line:
                # Inline preview format (PipelineEditor style)
                name_part = line[:sep_idx]
                preview_part = line[sep_idx:]

                # Draw name part
                if is_selected:
                    painter.setPen(self.selected_text_color)
                else:
                    painter.setPen(self.name_color)

                painter.drawText(x_offset, y_offset, name_part)

                # Draw preview part
                name_width = fm.horizontalAdvance(name_part)
                if is_selected:
                    painter.setPen(self.selected_text_color)
                else:
                    painter.setPen(self.preview_color)

                painter.drawText(x_offset + name_width, y_offset, preview_part)
            else:
                # Regular line or multiline preview format
                # Choose color
                if is_selected:
                    color = self.selected_text_color
                elif is_preview_line:
                    color = self.preview_color
                else:
                    color = self.name_color

                painter.setPen(color)

                # Draw the line
                painter.drawText(x_offset, y_offset, line)

            # Move to next line
            y_offset += line_height

        painter.restore()

        # Draw scope border using same layered pattern as window borders
        # (scheme already fetched at top of paint() for background inset calculation)
        if scheme is not None:
            self._paint_border_layers(painter, option.rect, scheme)

    def _paint_scope_background(self, painter: QPainter, content_rect: QRect, scheme, layers) -> None:
        """Paint background matching border colors.

        If single layer: solid color matching border.
        If multiple layers: grid pattern of layer colors.
        """
        from openhcs.pyqt_gui.widgets.shared.scope_visual_config import (
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
        from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ScopeColorScheme

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
