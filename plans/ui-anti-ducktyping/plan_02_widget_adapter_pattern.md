# plan_02_widget_adapter_pattern.md
## Component: Widget Adapter Pattern for Qt Native Widgets

### Objective
Create adapter classes that wrap Qt native widgets (QLineEdit, QComboBox, QSpinBox) to implement OpenHCS widget protocols, eliminating the need for duck typing while maintaining compatibility with Qt's API.

### Problem Analysis

**Current Situation:**
Qt widgets have inconsistent APIs:
- `QLineEdit.text()` vs `QSpinBox.value()` vs `QComboBox.currentData()`
- `QLineEdit.setText()` vs `QSpinBox.setValue()` vs `QComboBox.setCurrentIndex()`
- `QLineEdit.setPlaceholderText()` vs `QSpinBox.setSpecialValueText()`

**Current Duck Typing Solution:**
```python
# SMELL: Try different methods until one works
WIDGET_GET_DISPATCH = [
    ('get_value', lambda w: w.get_value()),
    ('value', lambda w: w.value()),
    ('text', lambda w: w.text())
]
```

**Elegant Pattern to Emulate: MemoryTypeConverter**

From `openhcs/core/memory/conversion_helpers.py`:
```python
class MemoryTypeConverter(ABC):
    """Abstract base class for memory type converters."""
    
    @abstractmethod
    def to_numpy(self, data, gpu_id):
        """Extract to NumPy (type-specific implementation)."""
        pass
    
    @abstractmethod
    def from_numpy(self, data, gpu_id):
        """Create from NumPy (type-specific implementation)."""
        pass

# Auto-generate all 6 converter classes
_CONVERTERS = {
    mem_type: type(
        f"{mem_type.value.capitalize()}Converter",
        (MemoryTypeConverter,),
        _TYPE_OPERATIONS[mem_type]
    )()
    for mem_type in MemoryType
}
```

**Key Insight:** Each memory type has a converter that implements the same ABC interface, allowing polymorphic dispatch without duck typing. We need the same for widgets.

### Plan

#### 1. Create Base Widget Adapters

**File:** `openhcs/ui/shared/widget_adapters.py`

Adapter classes that wrap Qt widgets and implement protocols:

```python
from abc import ABC
from typing import Any, Optional
from PyQt6.QtWidgets import QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QCheckBox
from .widget_protocols import ValueGettable, ValueSettable, PlaceholderCapable, RangeConfigurable
from .widget_registry import WidgetMeta

class LineEditAdapter(QLineEdit, ValueGettable, ValueSettable, PlaceholderCapable, 
                      metaclass=WidgetMeta):
    """
    Adapter for QLineEdit that implements OpenHCS widget protocols.
    
    Wraps Qt's inconsistent API with explicit protocol implementation.
    """
    
    _widget_id = "line_edit"
    
    def get_value(self) -> Any:
        """Implement ValueGettable protocol."""
        text = self.text().strip()
        return None if text == "" else text
    
    def set_value(self, value: Any) -> None:
        """Implement ValueSettable protocol."""
        self.setText("" if value is None else str(value))
    
    def set_placeholder(self, text: str) -> None:
        """Implement PlaceholderCapable protocol."""
        self.setPlaceholderText(text)


class SpinBoxAdapter(QSpinBox, ValueGettable, ValueSettable, PlaceholderCapable,
                     RangeConfigurable, metaclass=WidgetMeta):
    """
    Adapter for QSpinBox that implements OpenHCS widget protocols.
    
    Handles None values using special value text mechanism.
    """
    
    _widget_id = "spin_box"
    
    def __init__(self, parent=None):
        super().__init__(parent)
        # Configure for None-aware behavior
        self.setSpecialValueText(" ")  # Empty special value = None
    
    def get_value(self) -> Any:
        """Implement ValueGettable protocol."""
        if self.value() == self.minimum() and self.specialValueText():
            return None
        return self.value()
    
    def set_value(self, value: Any) -> None:
        """Implement ValueSettable protocol."""
        if value is None:
            self.setValue(self.minimum())
        else:
            self.setValue(int(value))
    
    def set_placeholder(self, text: str) -> None:
        """Implement PlaceholderCapable protocol."""
        # For spinbox, placeholder is shown when at minimum with special value text
        self.setSpecialValueText(text)
    
    def configure_range(self, minimum: float, maximum: float) -> None:
        """Implement RangeConfigurable protocol."""
        self.setRange(int(minimum), int(maximum))


class DoubleSpinBoxAdapter(QDoubleSpinBox, ValueGettable, ValueSettable, 
                           PlaceholderCapable, RangeConfigurable, metaclass=WidgetMeta):
    """Adapter for QDoubleSpinBox with protocol implementation."""
    
    _widget_id = "double_spin_box"
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setSpecialValueText(" ")
    
    def get_value(self) -> Any:
        """Implement ValueGettable protocol."""
        if self.value() == self.minimum() and self.specialValueText():
            return None
        return self.value()
    
    def set_value(self, value: Any) -> None:
        """Implement ValueSettable protocol."""
        if value is None:
            self.setValue(self.minimum())
        else:
            self.setValue(float(value))
    
    def set_placeholder(self, text: str) -> None:
        """Implement PlaceholderCapable protocol."""
        self.setSpecialValueText(text)
    
    def configure_range(self, minimum: float, maximum: float) -> None:
        """Implement RangeConfigurable protocol."""
        self.setRange(minimum, maximum)


class ComboBoxAdapter(QComboBox, ValueGettable, ValueSettable, PlaceholderCapable,
                     metaclass=WidgetMeta):
    """
    Adapter for QComboBox with protocol implementation.
    
    Stores actual values in itemData, not just display text.
    """
    
    _widget_id = "combo_box"
    
    def get_value(self) -> Any:
        """Implement ValueGettable protocol."""
        if self.currentIndex() < 0:
            return None
        return self.itemData(self.currentIndex())
    
    def set_value(self, value: Any) -> None:
        """Implement ValueSettable protocol."""
        # Find index of item with matching data
        for i in range(self.count()):
            if self.itemData(i) == value:
                self.setCurrentIndex(i)
                return
        # Value not found - clear selection
        self.setCurrentIndex(-1)
    
    def set_placeholder(self, text: str) -> None:
        """Implement PlaceholderCapable protocol."""
        # ComboBox placeholder is shown when no selection
        self.setPlaceholderText(text)


class CheckBoxAdapter(QCheckBox, ValueGettable, ValueSettable, metaclass=WidgetMeta):
    """Adapter for QCheckBox with protocol implementation."""
    
    _widget_id = "check_box"
    
    def get_value(self) -> Any:
        """Implement ValueGettable protocol."""
        return self.isChecked()
    
    def set_value(self, value: Any) -> None:
        """Implement ValueSettable protocol."""
        self.setChecked(bool(value) if value is not None else False)
```

#### 2. Create Widget Factory with Type-Based Dispatch

**File:** `openhcs/ui/shared/widget_factory.py`

Factory that creates widgets using explicit type mapping (no duck typing):

```python
from typing import Type, Any, Dict, Callable
from enum import Enum
from .widget_adapters import (LineEditAdapter, SpinBoxAdapter, DoubleSpinBoxAdapter,
                              ComboBoxAdapter, CheckBoxAdapter)
from .widget_protocols import EnumSelectable

# Type-based widget creation dispatch - NO DUCK TYPING
WIDGET_TYPE_REGISTRY: Dict[Type, Callable] = {
    str: lambda: LineEditAdapter(),
    int: lambda: SpinBoxAdapter(),
    float: lambda: DoubleSpinBoxAdapter(),
    bool: lambda: CheckBoxAdapter(),
}

class WidgetFactory:
    """
    Widget factory using explicit type-based dispatch.
    
    Replaces duck typing with fail-loud type checking.
    Mirrors the pattern from MemoryType converters.
    """
    
    @staticmethod
    def create_widget(param_type: Type, param_name: str = "") -> Any:
        """
        Create widget for parameter type using explicit dispatch.
        
        Args:
            param_type: The parameter type to create widget for
            param_name: Optional parameter name for debugging
        
        Returns:
            Widget instance implementing required protocols
        
        Raises:
            TypeError: If no widget registered for this type
        """
        # Handle Optional[T] by unwrapping
        from typing import get_origin, get_args, Union
        if get_origin(param_type) is Union:
            args = get_args(param_type)
            if len(args) == 2 and type(None) in args:
                param_type = next(arg for arg in args if arg is not type(None))
        
        # Handle Enum types
        if isinstance(param_type, type) and issubclass(param_type, Enum):
            widget = ComboBoxAdapter()
            # Populate with enum values
            for enum_value in param_type:
                widget.addItem(enum_value.name, enum_value)
            return widget
        
        # Handle List[Enum] types
        if get_origin(param_type) is list:
            args = get_args(param_type)
            if args and isinstance(args[0], type) and issubclass(args[0], Enum):
                # Create multi-select widget for List[Enum]
                from .widget_adapters import EnumMultiSelectAdapter
                return EnumMultiSelectAdapter(args[0])
        
        # Explicit type dispatch - FAIL LOUD if type not registered
        factory = WIDGET_TYPE_REGISTRY.get(param_type)
        if factory is None:
            raise TypeError(
                f"No widget registered for type {param_type}. "
                f"Available types: {list(WIDGET_TYPE_REGISTRY.keys())}. "
                f"Add widget factory to WIDGET_TYPE_REGISTRY."
            )
        
        return factory()
```

### Findings

**Elegant Patterns from Memory System:**

1. **MemoryTypeConverter ABC** - All converters implement same interface
2. **Auto-generated converters** - Using `type()` to create classes dynamically
3. **Enum-driven dispatch** - `MemoryType.NUMPY.converter.to_torch()`
4. **Fail-loud validation** - Runtime checks ensure all methods exist

**Elegant Patterns from IO Backend:**

1. **StorageBackendMeta** - Auto-registration via metaclass
2. **Explicit backend type** - `_backend_type` attribute
3. **Global registry** - `STORAGE_BACKENDS` dict
4. **Lazy instantiation** - `get_backend_instance()` creates on demand

**Current Widget Inconsistencies:**

| Widget | Get Value | Set Value | Placeholder |
|--------|-----------|-----------|-------------|
| QLineEdit | `.text()` | `.setText()` | `.setPlaceholderText()` |
| QSpinBox | `.value()` | `.setValue()` | `.setSpecialValueText()` |
| QComboBox | `.itemData(currentIndex())` | `.setCurrentIndex()` | `.setPlaceholderText()` |
| QCheckBox | `.isChecked()` | `.setChecked()` | N/A |

**Solution:** Adapter pattern normalizes these to:
- `.get_value()` / `.set_value()` / `.set_placeholder()` for ALL widgets

### Implementation Draft

(Code will be written after smell loop approval)

