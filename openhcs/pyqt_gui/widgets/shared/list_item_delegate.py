"""
Shared QListWidget item delegate for rendering multiline items with grey preview text.

Single source of truth for list item rendering across PipelineEditor, PlateManager,
and other widgets that display items with preview labels.
"""

from PyQt6.QtWidgets import QStyledItemDelegate, QStyleOptionViewItem, QStyle
from PyQt6.QtGui import QPainter, QColor, QFontMetrics, QFont, QPen, QBrush
from PyQt6.QtCore import Qt, QRect


class MultilinePreviewItemDelegate(QStyledItemDelegate):
    """Custom delegate to render multiline items with grey preview text.
    
    Supports:
    - Multiline text rendering (automatic height calculation)
    - Grey preview text for lines containing specific markers
    - Proper hover/selection/border rendering
    - Configurable colors for normal/preview/selected text
    
    Text format:
    - Lines starting with "  └─" are rendered in grey (preview text)
    - All other lines are rendered in normal color
    - Selected items use selected text color
    """
    
    def __init__(self, name_color: QColor, preview_color: QColor, selected_text_color: QColor, parent=None):
        """Initialize delegate with color scheme.
        
        Args:
            name_color: Color for normal text lines
            preview_color: Color for preview text lines (grey)
            selected_text_color: Color for text when item is selected
            parent: Parent widget
        """
        super().__init__(parent)
        self.name_color = name_color
        self.preview_color = preview_color
        self.selected_text_color = selected_text_color
    
    def paint(self, painter: QPainter, option: QStyleOptionViewItem, index) -> None:
        """Paint the item with multiline support and grey preview text."""
        # Prepare a copy to let style draw backgrounds, hover, selection, borders, etc.
        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)

        # Capture text and prevent default text draw
        text = opt.text or ""
        opt.text = ""

        # CRITICAL: Draw custom background color FIRST (before style draws selection)
        # This allows scope-based colors to show through
        # BUT: Skip if item is currently flashing (flash animation manages background)
        from openhcs.pyqt_gui.widgets.shared.list_item_flash_animation import is_item_flashing
        import logging
        logger = logging.getLogger(__name__)

        is_flashing = is_item_flashing(self.parent(), index.row())
        logger.info(f"🎨 Delegate paint: row={index.row()}, is_flashing={is_flashing}")

        if is_flashing:
            # When flashing, paint the flash color directly and tell style to skip background
            logger.info(f"🎨 Item is flashing: painting flash color directly")
            background_brush = index.data(Qt.ItemDataRole.BackgroundRole)
            if background_brush is not None:
                if isinstance(background_brush, QBrush):
                    color = background_brush.color()
                    logger.info(f"🎨 Painting FLASH background: row={index.row()}, color={color.name()}, alpha={color.alpha()}")
                painter.save()
                painter.fillRect(option.rect, background_brush)
                painter.restore()

            # Remove background from style option so style doesn't overwrite our flash color
            opt_no_bg = QStyleOptionViewItem(opt)
            opt_no_bg.backgroundBrush = QBrush()  # Empty brush = no background
            self.parent().style().drawControl(QStyle.ControlElement.CE_ItemViewItem, opt_no_bg, painter, self.parent())
        else:
            # Normal case: paint background then let style draw everything
            background_brush = index.data(Qt.ItemDataRole.BackgroundRole)
            if background_brush is not None:
                if isinstance(background_brush, QBrush):
                    color = background_brush.color()
                    logger.info(f"🎨 Painting background: row={index.row()}, color={color.name()}, alpha={color.alpha()}")
                painter.save()
                painter.fillRect(option.rect, background_brush)
                painter.restore()

            # Let the style draw selection indicator, hover, borders
            self.parent().style().drawControl(QStyle.ControlElement.CE_ItemViewItem, opt, painter, self.parent())

        # Draw layered step borders if present
        # Border layers are stored as list of (width, tint_index, pattern) tuples
        border_layers = index.data(Qt.ItemDataRole.UserRole + 3)
        base_color_rgb = index.data(Qt.ItemDataRole.UserRole + 4)

        if border_layers and len(border_layers) > 0 and base_color_rgb:
            painter.save()

            # Tint factors for the 3 tints (MORE DRASTIC)
            tint_factors = [0.7, 1.0, 1.4]  # Darker, neutral, brighter

            # Draw each border layer from outside to inside
            # Each border is drawn with its center at 'inset + width/2' from the edge
            inset = 0
            for layer_data in border_layers:
                # Handle both old format (width, tint_index) and new format (width, tint_index, pattern)
                if len(layer_data) == 3:
                    width, tint_index, pattern = layer_data
                else:
                    width, tint_index = layer_data
                    pattern = 'solid'

                # Calculate tinted color for this border
                r, g, b = base_color_rgb
                tint_factor = tint_factors[tint_index]
                border_r = min(255, int(r * tint_factor))
                border_g = min(255, int(g * tint_factor))
                border_b = min(255, int(b * tint_factor))
                border_color = QColor(border_r, border_g, border_b).darker(120)

                # Set pen style based on pattern with MORE OBVIOUS spacing
                pen = QPen(border_color, width)
                if pattern == 'dashed':
                    pen.setStyle(Qt.PenStyle.DashLine)
                    pen.setDashPattern([8, 6])  # Longer dashes, more spacing
                elif pattern == 'dotted':
                    pen.setStyle(Qt.PenStyle.DotLine)
                    pen.setDashPattern([2, 6])  # Small dots, more spacing
                else:  # solid
                    pen.setStyle(Qt.PenStyle.SolidLine)

                # Draw this border layer
                # Position the border so its outer edge is at 'inset' pixels from the rect edge
                # Since pen draws centered, we offset by width/2
                border_offset = int(inset + (width / 2.0))
                painter.setPen(pen)
                painter.drawRect(option.rect.adjusted(border_offset, border_offset, -border_offset - 1, -border_offset - 1))

                # Move inward for next layer
                inset += width

            painter.restore()

        # Now draw text manually with custom colors
        painter.save()

        # Determine text color based on selection state
        is_selected = option.state & QStyle.StateFlag.State_Selected

        # Check if item is disabled (stored in UserRole+1) - for PipelineEditor strikethrough
        is_disabled = index.data(Qt.ItemDataRole.UserRole + 1) or False

        # Use strikethrough font for disabled items
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

        underline_first_line = bool(index.data(Qt.ItemDataRole.UserRole + 2))

        # Draw each line with appropriate color
        for line_index, line in enumerate(lines):
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

                if line_index == 0 and underline_first_line:
                    # Underline the plate name portion (text after the last '▶ ')
                    arrow_idx = line.rfind("▶ ")
                    if arrow_idx != -1:
                        prefix = line[:arrow_idx + 2]
                        name_part = line[arrow_idx + 2:]
                    else:
                        prefix = ""
                        name_part = line

                    painter.drawText(x_offset, y_offset, prefix)
                    prefix_width = fm.horizontalAdvance(prefix)

                    underline_font = QFont(font)
                    underline_font.setUnderline(True)
                    painter.setFont(underline_font)
                    painter.drawText(x_offset + prefix_width, y_offset, name_part)
                    painter.setFont(font)
                else:
                    # Draw the entire line normally
                    painter.drawText(x_offset, y_offset, line)

            # Move to next line
            y_offset += line_height

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
