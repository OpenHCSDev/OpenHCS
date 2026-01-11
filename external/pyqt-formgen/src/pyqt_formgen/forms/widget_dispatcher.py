"""
Widget dispatcher with fail-loud ABC checking.

Replaces duck typing (hasattr checks) with explicit isinstance checks against ABCs.
All methods fail loud if widget doesn't implement required ABC.

Design Philosophy:
- Explicit over implicit
- Fail-loud over fail-silent
- Type-safe over duck-typed
"""

from typing import Any, Callable
from pyqt_formgen.protocols import (
    ValueGettable, ValueSettable, PlaceholderCapable,
    RangeConfigurable, EnumSelectable, ChangeSignalEmitter
)


class WidgetDispatcher:
    """
    ABC-based widget dispatch - NO DUCK TYPING.
    
    Replaces hasattr checks with explicit isinstance checks.
    Fails loud if widget doesn't implement required ABC.
    
    Example:
        # BEFORE (duck typing):
        if hasattr(widget, 'get_value'):
            value = widget.get_value()
        
        # AFTER (ABC-based):
        value = WidgetDispatcher.get_value(widget)  # Raises TypeError if not ValueGettable
    """
    
    @staticmethod
    def get_value(widget: Any) -> Any:
        """
        Get value from widget using explicit ABC check.
        
        Args:
            widget: The widget to get value from
        
        Returns:
            The widget's current value
        
        Raises:
            TypeError: If widget doesn't implement ValueGettable ABC
        """
        if not isinstance(widget, ValueGettable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement ValueGettable ABC. "
                f"Add ValueGettable to widget's base classes and implement get_value() method."
            )
        return widget.get_value()
    
    @staticmethod
    def set_value(widget: Any, value: Any) -> None:
        """
        Set value on widget using explicit ABC check.
        
        Args:
            widget: The widget to set value on
            value: The value to set
        
        Raises:
            TypeError: If widget doesn't implement ValueSettable ABC
        """
        if not isinstance(widget, ValueSettable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement ValueSettable ABC. "
                f"Add ValueSettable to widget's base classes and implement set_value() method."
            )
        widget.set_value(value)
    
    @staticmethod
    def set_placeholder(widget: Any, text: str) -> None:
        """
        Set placeholder using explicit ABC check.
        
        Args:
            widget: The widget to set placeholder on
            text: The placeholder text
        
        Raises:
            TypeError: If widget doesn't implement PlaceholderCapable ABC
        """
        if not isinstance(widget, PlaceholderCapable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement PlaceholderCapable ABC. "
                f"Add PlaceholderCapable to widget's base classes and implement set_placeholder() method."
            )
        widget.set_placeholder(text)
    
    @staticmethod
    def configure_range(widget: Any, minimum: float, maximum: float) -> None:
        """
        Configure range using explicit ABC check.
        
        Args:
            widget: The widget to configure
            minimum: Minimum value
            maximum: Maximum value
        
        Raises:
            TypeError: If widget doesn't implement RangeConfigurable ABC
        """
        if not isinstance(widget, RangeConfigurable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement RangeConfigurable ABC. "
                f"Add RangeConfigurable to widget's base classes and implement configure_range() method."
            )
        widget.configure_range(minimum, maximum)
    
    @staticmethod
    def set_enum_options(widget: Any, enum_type: type) -> None:
        """
        Set enum options using explicit ABC check.
        
        Args:
            widget: The widget to configure
            enum_type: The Enum class
        
        Raises:
            TypeError: If widget doesn't implement EnumSelectable ABC
        """
        if not isinstance(widget, EnumSelectable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement EnumSelectable ABC. "
                f"Add EnumSelectable to widget's base classes and implement set_enum_options() method."
            )
        widget.set_enum_options(enum_type)
    
    @staticmethod
    def get_selected_enum(widget: Any) -> Any:
        """
        Get selected enum using explicit ABC check.
        
        Args:
            widget: The widget to get selection from
        
        Returns:
            The selected enum value
        
        Raises:
            TypeError: If widget doesn't implement EnumSelectable ABC
        """
        if not isinstance(widget, EnumSelectable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement EnumSelectable ABC. "
                f"Add EnumSelectable to widget's base classes."
            )
        return widget.get_selected_enum()
    
    @staticmethod
    def connect_change_signal(widget: Any, callback: Callable[[Any], None]) -> None:
        """
        Connect change signal using explicit ABC check.
        
        Args:
            widget: The widget to connect signal on
            callback: Callback function receiving new value
        
        Raises:
            TypeError: If widget doesn't implement ChangeSignalEmitter ABC
        """
        if not isinstance(widget, ChangeSignalEmitter):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement ChangeSignalEmitter ABC. "
                f"Add ChangeSignalEmitter to widget's base classes and implement "
                f"connect_change_signal() method."
            )
        widget.connect_change_signal(callback)
    
    @staticmethod
    def disconnect_change_signal(widget: Any, callback: Callable[[Any], None]) -> None:
        """
        Disconnect change signal using explicit ABC check.
        
        Args:
            widget: The widget to disconnect signal from
            callback: Callback function to disconnect
        
        Raises:
            TypeError: If widget doesn't implement ChangeSignalEmitter ABC
        """
        if not isinstance(widget, ChangeSignalEmitter):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement ChangeSignalEmitter ABC."
            )
        widget.disconnect_change_signal(callback)

