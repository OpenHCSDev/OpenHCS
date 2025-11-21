"""
No-scroll spinbox widgets for PyQt6.

Prevents accidental value changes from mouse wheel events.
"""

from PyQt6.QtWidgets import QSpinBox, QDoubleSpinBox, QComboBox, QCheckBox, QStyleOptionComboBox, QStyle
from PyQt6.QtGui import QWheelEvent, QFont, QColor, QPainter
from PyQt6.QtCore import Qt


class NoScrollSpinBox(QSpinBox):
    """SpinBox that ignores wheel events to prevent accidental value changes."""
    
    def wheelEvent(self, event: QWheelEvent):
        """Ignore wheel events to prevent accidental value changes."""
        event.ignore()


class NoScrollDoubleSpinBox(QDoubleSpinBox):
    """DoubleSpinBox that ignores wheel events to prevent accidental value changes."""
    
    def wheelEvent(self, event: QWheelEvent):
        """Ignore wheel events to prevent accidental value changes."""
        event.ignore()


class NoScrollComboBox(QComboBox):
    """ComboBox that ignores wheel events to prevent accidental value changes.

    Supports placeholder text when currentIndex == -1 (for None values).
    """

    def __init__(self, parent=None, placeholder=""):
        super().__init__(parent)
        self._placeholder = placeholder
        self._placeholder_active = True

    def wheelEvent(self, event: QWheelEvent):
        """Ignore wheel events to prevent accidental value changes."""
        event.ignore()

    def setPlaceholder(self, text: str):
        """Set the placeholder text shown when currentIndex == -1."""
        import logging
        logger = logging.getLogger(__name__)

        self._placeholder = text
        # CRITICAL FIX: Update placeholder_active flag based on current index
        # This ensures placeholder renders even if setCurrentIndex(-1) was called before setPlaceholder()
        self._placeholder_active = (self.currentIndex() == -1)

        # DEBUG: Log visibility and geometry
        if 'INCLUDE' in text or 'IPC' in text:
            logger.info(f"🔍 NoScrollComboBox.setPlaceholder: widget={self.objectName()}, text={text}, currentIndex={self.currentIndex()}, _placeholder_active={self._placeholder_active}, isVisible={self.isVisible()}, width={self.width()}, height={self.height()}")

        self.update()

        # CRITICAL FIX: Force repaint even if widget is not visible yet
        # This ensures placeholder renders when widget becomes visible
        # Without this, sync widget creation doesn't show placeholders on initial window open
        self.repaint()

        # DEBUG: Check if update was called
        if 'INCLUDE' in text or 'IPC' in text:
            logger.info(f"🔍 NoScrollComboBox.setPlaceholder: AFTER update() and repaint() called")

    def setCurrentIndex(self, index: int):
        """Override to track when placeholder should be active."""
        super().setCurrentIndex(index)
        self._placeholder_active = (index == -1)
        self.update()

    def paintEvent(self, event):
        """Override to draw placeholder text when currentIndex == -1."""
        import logging
        logger = logging.getLogger(__name__)

        # DEBUG: Log paintEvent calls for placeholders
        if self._placeholder and ('INCLUDE' in self._placeholder or 'IPC' in self._placeholder):
            logger.info(f"🔍 NoScrollComboBox.paintEvent: widget={self.objectName()}, _placeholder_active={self._placeholder_active}, currentIndex={self.currentIndex()}, _placeholder={self._placeholder}")

        if self._placeholder_active and self.currentIndex() == -1 and self._placeholder:
            # DEBUG: Log that we're drawing placeholder
            if 'INCLUDE' in self._placeholder or 'IPC' in self._placeholder:
                logger.info(f"🔍 NoScrollComboBox.paintEvent: DRAWING PLACEHOLDER for {self.objectName()}")

            # Use regular QPainter to have full control over text rendering
            painter = QPainter(self)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)

            # Draw the combobox frame using style
            option = QStyleOptionComboBox()
            self.initStyleOption(option)
            option.currentText = ""  # Don't let style draw the text
            self.style().drawComplexControl(QStyle.ComplexControl.CC_ComboBox, option, painter, self)

            # Now manually draw the placeholder text with our styling
            placeholder_color = QColor("#888888")
            font = QFont(self.font())
            font.setItalic(True)

            painter.setPen(placeholder_color)
            painter.setFont(font)

            # Get the text rect from the style
            text_rect = self.style().subControlRect(
                QStyle.ComplexControl.CC_ComboBox,
                option,
                QStyle.SubControl.SC_ComboBoxEditField,
                self
            )

            # Draw the placeholder text
            painter.drawText(text_rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, self._placeholder)
            painter.end()
        else:
            super().paintEvent(event)


class NoneAwareCheckBox(QCheckBox):
    """
    QCheckBox that supports None state for lazy dataclass contexts.

    Shows inherited value as grayed placeholder when value is None.
    Clicking converts placeholder to explicit value.
    """

    def __init__(self, parent=None):
        super().__init__(parent)
        self._is_placeholder = False

    def get_value(self):
        """Get value, returning None if in placeholder state."""
        if self._is_placeholder:
            return None
        return self.isChecked()

    def set_value(self, value):
        """Set value, handling None by leaving in placeholder state."""
        if value is None:
            # Don't change state - placeholder system will set the preview value
            self._is_placeholder = True
        else:
            self._is_placeholder = False
            self.setChecked(bool(value))

    def mousePressEvent(self, event):
        """On click, switch from placeholder to explicit value."""
        if self._is_placeholder:
            self._is_placeholder = False
            # Clear placeholder property so get_value returns actual boolean
            self.setProperty("is_placeholder_state", False)
        super().mousePressEvent(event)

    def paintEvent(self, event):
        """Draw with distinct placeholder styling based on inherited value.

        - Placeholder True: Dimmer/semi-transparent checkmark
        - Placeholder False: Darker background on checkbox indicator
        - Concrete True/False: Normal styling unchanged
        """
        if not self._is_placeholder:
            # Concrete value: Normal styling
            super().paintEvent(event)
            return

        # Placeholder styling
        from PyQt6.QtWidgets import QStyle, QStyleOptionButton

        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)

        # Get the checkbox style option
        option = QStyleOptionButton()
        self.initStyleOption(option)

        if self.isChecked():
            # Placeholder True: Draw with dimmer checkmark
            painter.setOpacity(0.4)
            self.style().drawControl(QStyle.ControlElement.CE_CheckBox, option, painter, self)
        else:
            # Placeholder False: Draw normal checkbox first, then add dark overlay
            self.style().drawControl(QStyle.ControlElement.CE_CheckBox, option, painter, self)

            # Get the indicator rectangle
            indicator_rect = self.style().subElementRect(
                QStyle.SubElement.SE_CheckBoxIndicator,
                option,
                self
            )

            # Draw a darker semi-transparent overlay on the indicator background
            painter.setOpacity(0.6)
            painter.fillRect(indicator_rect, QColor("#222222"))

        painter.end()


