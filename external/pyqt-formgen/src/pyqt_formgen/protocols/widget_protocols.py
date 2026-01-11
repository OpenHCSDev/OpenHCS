"""
Widget ABC contracts for OpenHCS UI frameworks.

Defines explicit contracts that all widgets must implement, eliminating duck typing
in favor of fail-loud inheritance-based architecture.

Design Philosophy:
- Explicit inheritance over duck typing
- Fail-loud over fail-silent
- Discoverable over scattered
- Multiple inheritance for composable capabilities

Inspired by OpenHCS patterns:
- StorageBackendMeta: Metaclass auto-registration
- MemoryTypeConverter: ABC contracts with adapters
- LibraryRegistryBase: Centralized operations
"""

from abc import ABC, abstractmethod
from typing import Any, Callable


class ValueGettable(ABC):
    """
    ABC for widgets that can return a value.
    
    All input widgets must implement this to participate in form value extraction.
    """
    
    @abstractmethod
    def get_value(self) -> Any:
        """
        Get the current value from the widget.
        
        Returns:
            The widget's current value. None if no value set.
        """
        pass


class ValueSettable(ABC):
    """
    ABC for widgets that can accept a value.
    
    All input widgets must implement this to participate in form value updates.
    """
    
    @abstractmethod
    def set_value(self, value: Any) -> None:
        """
        Set the widget's value.
        
        Args:
            value: The value to set. None clears the widget.
        """
        pass


class PlaceholderCapable(ABC):
    """
    ABC for widgets that can display placeholder text.
    
    Placeholders show inherited/default values without setting actual values.
    """
    
    @abstractmethod
    def set_placeholder(self, text: str) -> None:
        """
        Set placeholder text for the widget.
        
        Args:
            text: Placeholder text to display (e.g., "Pipeline default: 42")
        """
        pass


class RangeConfigurable(ABC):
    """
    ABC for widgets that support numeric range configuration.
    
    Typically implemented by numeric input widgets (spinboxes, sliders).
    """
    
    @abstractmethod
    def configure_range(self, minimum: float, maximum: float) -> None:
        """
        Configure the valid range for numeric input.
        
        Args:
            minimum: Minimum allowed value
            maximum: Maximum allowed value
        """
        pass


class EnumSelectable(ABC):
    """
    ABC for widgets that can select from enum values.
    
    Typically implemented by dropdowns and radio button groups.
    """
    
    @abstractmethod
    def set_enum_options(self, enum_type: type) -> None:
        """
        Configure widget with enum options.
        
        Args:
            enum_type: The Enum class to populate options from
        """
        pass
    
    @abstractmethod
    def get_selected_enum(self) -> Any:
        """
        Get the currently selected enum value.
        
        Returns:
            The selected enum member, or None if no selection
        """
        pass


class ChangeSignalEmitter(ABC):
    """
    ABC for widgets that emit change signals.
    
    Provides explicit contract for signal connection, eliminating duck typing
    of signal names (textChanged vs valueChanged vs currentIndexChanged).
    """
    
    @abstractmethod
    def connect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """
        Connect callback to widget's change signal.
        
        The callback will be invoked whenever the widget's value changes,
        receiving the new value as its argument.
        
        Args:
            callback: Function to call when widget value changes.
                     Signature: callback(new_value: Any) -> None
        """
        pass
    
    @abstractmethod
    def disconnect_change_signal(self, callback: Callable[[Any], None]) -> None:
        """
        Disconnect callback from widget's change signal.
        
        Args:
            callback: The callback function to disconnect
        """
        pass

