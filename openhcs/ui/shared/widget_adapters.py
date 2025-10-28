"""
Widget adapters that wrap Qt widgets to implement OpenHCS ABCs.

Normalizes Qt's inconsistent APIs:
- QLineEdit.text() vs QSpinBox.value() vs QComboBox.currentData()
- QLineEdit.setText() vs QSpinBox.setValue() vs QComboBox.setCurrentIndex()
- QLineEdit.setPlaceholderText() vs QSpinBox.setSpecialValueText()

All adapters implement consistent interface via ABCs:
- get_value() / set_value() for all widgets
- set_placeholder() for all widgets
- connect_change_signal() for all widgets

Mirrors MemoryTypeConverter pattern - adapters normalize inconsistent APIs.
"""

from typing import Any, Callable, Optional
from enum import Enum

try:
    from PyQt6.QtWidgets import (
        QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QCheckBox, QWidget
    )
    from PyQt6.QtCore import Qt
    PYQT6_AVAILABLE = True
except ImportError:
    PYQT6_AVAILABLE = False
    # Create dummy base classes for type hints
    QLineEdit = QSpinBox = QDoubleSpinBox = QComboBox = QCheckBox = QWidget = object

from .widget_protocols import (
    ValueGettable, ValueSettable, PlaceholderCapable,
    RangeConfigurable, ChangeSignalEmitter
)
from .widget_registry import WidgetMeta


if PYQT6_AVAILABLE:
    
    class LineEditAdapter(QLineEdit, ValueGettable, ValueSettable, PlaceholderCapable,
                          ChangeSignalEmitter, metaclass=WidgetMeta):
        """
        Adapter for QLineEdit implementing OpenHCS ABCs.
        
        Normalizes Qt API to OpenHCS contracts:
        - .text() → .get_value()
        - .setText() → .set_value()
        - .setPlaceholderText() → .set_placeholder()
        - .textChanged → .connect_change_signal()
        """
        
        _widget_id = "line_edit"
        
        def get_value(self) -> Any:
            """Implement ValueGettable ABC."""
            text = self.text().strip()
            return None if text == "" else text
        
        def set_value(self, value: Any) -> None:
            """Implement ValueSettable ABC."""
            self.setText("" if value is None else str(value))
        
        def set_placeholder(self, text: str) -> None:
            """Implement PlaceholderCapable ABC."""
            self.setPlaceholderText(text)
        
        def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            self.textChanged.connect(lambda: callback(self.get_value()))
        
        def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            try:
                self.textChanged.disconnect(callback)
            except TypeError:
                # Signal not connected - ignore
                pass
    
    
    class SpinBoxAdapter(QSpinBox, ValueGettable, ValueSettable, PlaceholderCapable,
                         RangeConfigurable, ChangeSignalEmitter, metaclass=WidgetMeta):
        """
        Adapter for QSpinBox implementing OpenHCS ABCs.
        
        Handles None values using special value text mechanism.
        When value is None, displays placeholder text at minimum value.
        """
        
        _widget_id = "spin_box"
        
        def __init__(self, parent=None):
            super().__init__(parent)
            # Configure for None-aware behavior
            self.setSpecialValueText(" ")  # Empty special value = None
            self.setRange(-2147483648, 2147483647)  # Default int range
        
        def get_value(self) -> Any:
            """Implement ValueGettable ABC."""
            if self.value() == self.minimum() and self.specialValueText():
                return None
            return self.value()
        
        def set_value(self, value: Any) -> None:
            """Implement ValueSettable ABC."""
            if value is None:
                self.setValue(self.minimum())
            else:
                self.setValue(int(value))
        
        def set_placeholder(self, text: str) -> None:
            """Implement PlaceholderCapable ABC."""
            # For spinbox, placeholder is shown when at minimum with special value text
            self.setSpecialValueText(text)
        
        def configure_range(self, minimum: float, maximum: float) -> None:
            """Implement RangeConfigurable ABC."""
            self.setRange(int(minimum), int(maximum))
        
        def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            self.valueChanged.connect(lambda: callback(self.get_value()))
        
        def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            try:
                self.valueChanged.disconnect(callback)
            except TypeError:
                pass
    
    
    class DoubleSpinBoxAdapter(QDoubleSpinBox, ValueGettable, ValueSettable,
                               PlaceholderCapable, RangeConfigurable,
                               ChangeSignalEmitter, metaclass=WidgetMeta):
        """
        Adapter for QDoubleSpinBox implementing OpenHCS ABCs.
        
        Handles None values and floating-point ranges.
        """
        
        _widget_id = "double_spin_box"
        
        def __init__(self, parent=None):
            super().__init__(parent)
            self.setSpecialValueText(" ")
            self.setRange(-1e308, 1e308)  # Default float range
            self.setDecimals(6)  # Default precision
        
        def get_value(self) -> Any:
            """Implement ValueGettable ABC."""
            if self.value() == self.minimum() and self.specialValueText():
                return None
            return self.value()
        
        def set_value(self, value: Any) -> None:
            """Implement ValueSettable ABC."""
            if value is None:
                self.setValue(self.minimum())
            else:
                self.setValue(float(value))
        
        def set_placeholder(self, text: str) -> None:
            """Implement PlaceholderCapable ABC."""
            self.setSpecialValueText(text)
        
        def configure_range(self, minimum: float, maximum: float) -> None:
            """Implement RangeConfigurable ABC."""
            self.setRange(minimum, maximum)
        
        def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            self.valueChanged.connect(lambda: callback(self.get_value()))
        
        def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            try:
                self.valueChanged.disconnect(callback)
            except TypeError:
                pass
    
    
    class ComboBoxAdapter(QComboBox, ValueGettable, ValueSettable, PlaceholderCapable,
                         ChangeSignalEmitter, metaclass=WidgetMeta):
        """
        Adapter for QComboBox implementing OpenHCS ABCs.
        
        Stores actual values in itemData, not just display text.
        Supports enum population and selection.
        """
        
        _widget_id = "combo_box"
        
        def get_value(self) -> Any:
            """Implement ValueGettable ABC."""
            if self.currentIndex() < 0:
                return None
            return self.itemData(self.currentIndex())
        
        def set_value(self, value: Any) -> None:
            """Implement ValueSettable ABC."""
            # Find index of item with matching data
            for i in range(self.count()):
                if self.itemData(i) == value:
                    self.setCurrentIndex(i)
                    return
            # Value not found - clear selection
            self.setCurrentIndex(-1)
        
        def set_placeholder(self, text: str) -> None:
            """Implement PlaceholderCapable ABC."""
            # ComboBox placeholder is shown when no selection
            self.setPlaceholderText(text)
        
        def populate_enum(self, enum_type: type) -> None:
            """
            Populate combobox with enum values.
            
            Args:
                enum_type: The Enum class to populate from
            """
            if not isinstance(enum_type, type) or not issubclass(enum_type, Enum):
                raise TypeError(f"{enum_type} is not an Enum type")
            
            self.clear()
            for enum_value in enum_type:
                self.addItem(enum_value.name, enum_value)
        
        def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            self.currentIndexChanged.connect(lambda: callback(self.get_value()))
        
        def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            try:
                self.currentIndexChanged.disconnect(callback)
            except TypeError:
                pass
    
    
    class CheckBoxAdapter(QCheckBox, ValueGettable, ValueSettable,
                         ChangeSignalEmitter, metaclass=WidgetMeta):
        """
        Adapter for QCheckBox implementing OpenHCS ABCs.
        
        Returns bool values, treats None as False.
        """
        
        _widget_id = "check_box"
        
        def get_value(self) -> Any:
            """Implement ValueGettable ABC."""
            return self.isChecked()
        
        def set_value(self, value: Any) -> None:
            """Implement ValueSettable ABC."""
            self.setChecked(bool(value) if value is not None else False)
        
        def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            self.stateChanged.connect(lambda: callback(self.get_value()))
        
        def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
            """Implement ChangeSignalEmitter ABC."""
            try:
                self.stateChanged.disconnect(callback)
            except TypeError:
                pass

