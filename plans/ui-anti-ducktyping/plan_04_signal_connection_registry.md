# plan_04_signal_connection_registry.md
## Component: Signal Connection Registry System

### Objective
Eliminate duck typing from signal connection logic by creating an explicit signal registry pattern, mirroring the ProcessingContract enum dispatch system.

### Problem Analysis

**Current Duck Typing in Signal Connections:**

From `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`:
```python
# SMELL: Attribute-based signal detection
def connect_change_signal(widget: Any, param_name: str, callback: Callable):
    """Connect widget's change signal using duck typing."""
    if hasattr(widget, 'textChanged'):
        widget.textChanged.connect(lambda: callback(param_name, widget.text()))
    elif hasattr(widget, 'stateChanged'):
        widget.stateChanged.connect(lambda: callback(param_name, widget.isChecked()))
    elif hasattr(widget, 'valueChanged'):
        widget.valueChanged.connect(lambda: callback(param_name, widget.value()))
    # ... more hasattr checks
```

**Why This Is Bad:**
1. Silent failures if signal name is misspelled
2. No compile-time checking
3. Can't discover which widgets support which signals
4. Violates fail-loud principle

**Elegant Pattern to Emulate: ProcessingContract Enum**

From `openhcs/processing/backends/lib_registry/unified_registry.py`:
```python
class ProcessingContract(Enum):
    """Unified contract classification with direct method execution."""
    PURE_3D = "_execute_pure_3d"
    PURE_2D = "_execute_pure_2d"
    FLEXIBLE = "_execute_flexible"
    VOLUMETRIC_TO_SLICE = "_execute_volumetric_to_slice"
    
    def execute(self, registry, func, image, *args, **kwargs):
        """Execute the contract method on the registry."""
        method = getattr(registry, self.value)
        return method(func, image, *args, **kwargs)
```

**Key Insight:** Enum-driven dispatch with explicit method names eliminates duck typing while maintaining polymorphism.

### Plan

#### 1. Create Signal Protocol ABC

**File:** `openhcs/ui/shared/widget_protocols.py` (extend existing)

Add signal protocol to existing protocols:

```python
from abc import ABC, abstractmethod
from typing import Callable

class ChangeSignalEmitter(ABC):
    """Widget that emits change signals."""
    
    @abstractmethod
    def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """
        Connect callback to widget's change signal.
        
        Args:
            callback: Function to call when widget value changes.
                     Receives the new value as argument.
        """
        pass
    
    @abstractmethod
    def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Disconnect callback from widget's change signal."""
        pass
```

#### 2. Implement Signal Protocol in Adapters

**File:** `openhcs/ui/shared/widget_adapters.py` (extend existing)

Add signal connection to each adapter:

```python
class LineEditAdapter(QLineEdit, ValueGettable, ValueSettable, PlaceholderCapable,
                      ChangeSignalEmitter, metaclass=WidgetMeta):
    """Adapter with explicit signal connection."""
    
    _widget_id = "line_edit"
    
    def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Implement ChangeSignalEmitter protocol."""
        # Explicit signal connection - no duck typing
        self.textChanged.connect(lambda: callback(self.get_value()))
    
    def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Implement ChangeSignalEmitter protocol."""
        try:
            self.textChanged.disconnect(callback)
        except TypeError:
            # Signal not connected - ignore
            pass


class SpinBoxAdapter(QSpinBox, ValueGettable, ValueSettable, PlaceholderCapable,
                     RangeConfigurable, ChangeSignalEmitter, metaclass=WidgetMeta):
    """Adapter with explicit signal connection."""
    
    _widget_id = "spin_box"
    
    def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Implement ChangeSignalEmitter protocol."""
        # Explicit signal connection - no duck typing
        self.valueChanged.connect(lambda: callback(self.get_value()))
    
    def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Implement ChangeSignalEmitter protocol."""
        try:
            self.valueChanged.disconnect(callback)
        except TypeError:
            pass


class ComboBoxAdapter(QComboBox, ValueGettable, ValueSettable, PlaceholderCapable,
                     ChangeSignalEmitter, metaclass=WidgetMeta):
    """Adapter with explicit signal connection."""
    
    _widget_id = "combo_box"
    
    def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Implement ChangeSignalEmitter protocol."""
        # Explicit signal connection - no duck typing
        self.currentIndexChanged.connect(lambda: callback(self.get_value()))
    
    def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Implement ChangeSignalEmitter protocol."""
        try:
            self.currentIndexChanged.disconnect(callback)
        except TypeError:
            pass


class CheckBoxAdapter(QCheckBox, ValueGettable, ValueSettable, ChangeSignalEmitter,
                     metaclass=WidgetMeta):
    """Adapter with explicit signal connection."""
    
    _widget_id = "check_box"
    
    def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Implement ChangeSignalEmitter protocol."""
        # Explicit signal connection - no duck typing
        self.stateChanged.connect(lambda: callback(self.get_value()))
    
    def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """Implement ChangeSignalEmitter protocol."""
        try:
            self.stateChanged.disconnect(callback)
        except TypeError:
            pass
```

#### 3. Update WidgetOperations for Signals

**File:** `openhcs/ui/shared/widget_operations.py` (extend existing)

Add signal operations:

```python
class WidgetOperations:
    """Centralized widget operations using protocol-based dispatch."""
    
    @staticmethod
    def connect_change_signal(widget: Any, callback: Callable[[Any], None]) -> None:
        """
        Connect change signal using explicit protocol check.
        
        REPLACES: Duck typing hasattr checks
        USES: Explicit ChangeSignalEmitter protocol
        """
        if not isinstance(widget, ChangeSignalEmitter):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement ChangeSignalEmitter protocol. "
                f"Add ChangeSignalEmitter to widget's base classes."
            )
        widget.connect_change_signal(callback)
    
    @staticmethod
    def disconnect_change_signal(widget: Any, callback: Callable[[Any], None]) -> None:
        """Disconnect change signal using explicit protocol check."""
        if not isinstance(widget, ChangeSignalEmitter):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement ChangeSignalEmitter protocol."
            )
        widget.disconnect_change_signal(callback)
```

#### 4. Simplify ParameterFormManager Signal Logic

**File:** `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

Replace duck typing with protocol-based signal connection:

```python
class ParameterFormManager(QWidget):
    """Parameter form manager with protocol-based signal connections."""
    
    def _create_regular_parameter_widget(self, param_info) -> QWidget:
        """Create widget with explicit signal connection."""
        # ... widget creation code ...
        
        # BEFORE: Duck typing signal connection
        # PyQt6WidgetEnhancer.connect_change_signal(widget, param_info.name, self._emit_parameter_change)
        
        # AFTER: Protocol-based signal connection
        try:
            self._widget_ops.connect_change_signal(
                widget,
                lambda value: self._emit_parameter_change(param_info.name, value)
            )
        except TypeError as e:
            # Widget doesn't support change signals - fail loud
            raise TypeError(
                f"Widget for parameter '{param_info.name}' must implement "
                f"ChangeSignalEmitter protocol: {e}"
            )
        
        return container
```

### Findings

**Current Signal Connection Duck Typing:**

From `widget_strategies.py`:
```python
# SMELL: Attribute-based signal detection
SIGNAL_CONNECTIONS = {
    'textChanged': lambda w, cb: w.textChanged.connect(cb),
    'stateChanged': lambda w, cb: w.stateChanged.connect(cb),
    'valueChanged': lambda w, cb: w.valueChanged.connect(cb),
    'currentIndexChanged': lambda w, cb: w.currentIndexChanged.connect(cb),
}

def connect_change_signal(widget, param_name, callback):
    for signal_name, connector in SIGNAL_CONNECTIONS.items():
        if hasattr(widget, signal_name):
            connector(widget, lambda: callback(param_name, get_value(widget)))
            return
```

**Problems:**
1. Silent failure if no signal found
2. Can't verify signal exists at compile time
3. Callback signature inconsistent (sometimes gets value, sometimes doesn't)
4. No way to discover which widgets support signals

**Solution Benefits:**

1. **Explicit Contract:**
   - `ChangeSignalEmitter` protocol declares signal support
   - Compile-time checking via `isinstance()`
   - Fail-loud if widget doesn't implement protocol

2. **Consistent Callback Signature:**
   - All callbacks receive `(value)` argument
   - Widget handles value extraction internally
   - No need for separate `get_value()` call

3. **Discoverable:**
   - Can query `WIDGET_CAPABILITIES` to see which widgets support signals
   - IDE autocomplete shows `connect_change_signal()` method
   - Easy to find all signal-emitting widgets

4. **Type Safe:**
   - Renaming signal method = compiler error
   - Typos caught immediately
   - Refactoring is safe

### Implementation Draft

(Code will be written after smell loop approval)

