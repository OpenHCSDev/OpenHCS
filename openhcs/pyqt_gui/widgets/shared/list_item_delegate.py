"""
Shared QListWidget item delegate for rendering multiline items with grey preview text.

Single source of truth for list item rendering across PipelineEditor, PlateManager,
and other widgets that display items with preview labels.
"""

from PyQt6.QtWidgets import QStyledItemDelegate, QStyleOptionViewItem, QStyle
from PyQt6.QtGui import QPainter, QColor, QFontMetrics
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

        # Let the style draw background, selection, hover, borders
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

