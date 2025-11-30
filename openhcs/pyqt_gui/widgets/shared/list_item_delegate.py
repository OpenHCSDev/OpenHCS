"""
Shared QListWidget item delegate for rendering multiline items with grey preview text.

Single source of truth for list item rendering across PipelineEditor, PlateManager,
and other widgets that display items with preview labels.
"""

from PyQt6.QtWidgets import QStyledItemDelegate, QStyleOptionViewItem, QStyle
from PyQt6.QtGui import QPainter, QColor, QFontMetrics, QPen
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
        from PyQt6.QtGui import QBrush

        # Prepare a copy to let style draw backgrounds, hover, selection, borders, etc.
        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)

        # Capture text and prevent default text draw
        text = opt.text or ""
        opt.text = ""

        # Check selection/hover state
        is_selected = option.state & QStyle.StateFlag.State_Selected
        is_hover = option.state & QStyle.StateFlag.State_MouseOver

        # Draw scope-based background color from item's BackgroundRole
        # This is set via QListWidgetItem.setBackground() in _apply_list_item_scope_color
        item_bg = index.data(Qt.ItemDataRole.BackgroundRole)
        if item_bg:
            # Get the color from the brush
            bg_color = item_bg.color()

            # Invert opacity for selection: normal=30-40%, selected=70-80%
            if is_selected:
                # Invert: if alpha was 40% (102), make it 85% (217)
                inverted_alpha = min(255, 255 - bg_color.alpha() + 50)
                bg_color.setAlpha(inverted_alpha)
            elif is_hover:
                # Slight boost for hover
                boosted_alpha = min(255, bg_color.alpha() + 30)
                bg_color.setAlpha(boosted_alpha)

            painter.fillRect(option.rect, bg_color)

        # Clear style's background and selection drawing - we handle it ourselves
        opt.backgroundBrush = QBrush()
        if is_selected:
            # Remove selected state so style doesn't draw blue
            opt.state = opt.state & ~QStyle.StateFlag.State_Selected

        # Let the style draw hover effects and borders (but not selection background)
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

        # Draw scope border (stored in SCOPE_BORDER_ROLE = UserRole+10)
        border_color = index.data(Qt.ItemDataRole.UserRole + 10)
        if border_color and isinstance(border_color, QColor):
            painter.save()
            # Draw left border (2px wide) as scope indicator
            pen = QPen(border_color)
            pen.setWidth(3)
            painter.setPen(pen)
            rect = option.rect
            # Draw on left edge
            painter.drawLine(rect.left() + 1, rect.top(), rect.left() + 1, rect.bottom())
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

