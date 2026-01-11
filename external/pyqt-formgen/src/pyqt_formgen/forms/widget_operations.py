"""
Centralized widget operations using ABC-based dispatch.

Replaces scattered duck typing with explicit ABC checks.
Eliminates WIDGET_UPDATE_DISPATCH and WIDGET_GET_DISPATCH tables.

Design:
- Single source of truth for widget operations
- ABC-based dispatch (no hasattr checks)
- Fail-loud on missing implementations
- Discoverable via registry
"""

from typing import Any, Callable
from .widget_dispatcher import WidgetDispatcher
from pyqt_formgen.protocols import (
    ValueGettable, ValueSettable, PlaceholderCapable,
    RangeConfigurable, ChangeSignalEmitter
)
from .widget_registry import WIDGET_IMPLEMENTATIONS


class WidgetOperations:
    """
    Centralized widget operations using ABC-based dispatch.
    
    Replaces scattered duck typing with explicit ABC checks.
    Eliminates WIDGET_UPDATE_DISPATCH and WIDGET_GET_DISPATCH.
    
    Example:
        ops = WidgetOperations()
        
        # Get value (fails loud if widget doesn't implement ValueGettable)
        value = ops.get_value(widget)
        
        # Set value (fails loud if widget doesn't implement ValueSettable)
        ops.set_value(widget, 42)
        
        # Set placeholder (fails loud if widget doesn't implement PlaceholderCapable)
        ops.set_placeholder(widget, "Pipeline default: 100")
    """
    
    @staticmethod
    def get_value(widget: Any) -> Any:
        """
        Get value from any widget implementing ValueGettable.
        
        Args:
            widget: The widget to get value from
        
        Returns:
            The widget's current value
        
        Raises:
            TypeError: If widget doesn't implement ValueGettable ABC
        """
        return WidgetDispatcher.get_value(widget)
    
    @staticmethod
    def set_value(widget: Any, value: Any) -> None:
        """
        Set value on any widget implementing ValueSettable.
        
        Args:
            widget: The widget to set value on
            value: The value to set
        
        Raises:
            TypeError: If widget doesn't implement ValueSettable ABC
        """
        WidgetDispatcher.set_value(widget, value)
    
    @staticmethod
    def set_placeholder(widget: Any, text: str) -> None:
        """
        Set placeholder on any widget implementing PlaceholderCapable.
        
        Args:
            widget: The widget to set placeholder on
            text: The placeholder text
        
        Raises:
            TypeError: If widget doesn't implement PlaceholderCapable ABC
        """
        WidgetDispatcher.set_placeholder(widget, text)
    
    @staticmethod
    def configure_range(widget: Any, minimum: float, maximum: float) -> None:
        """
        Configure range on any widget implementing RangeConfigurable.
        
        Args:
            widget: The widget to configure
            minimum: Minimum value
            maximum: Maximum value
        
        Raises:
            TypeError: If widget doesn't implement RangeConfigurable ABC
        """
        WidgetDispatcher.configure_range(widget, minimum, maximum)
    
    @staticmethod
    def connect_change_signal(widget: Any, callback: Callable[[Any], None]) -> None:
        """
        Connect change signal on any widget implementing ChangeSignalEmitter.
        
        Args:
            widget: The widget to connect signal on
            callback: Callback function receiving new value
        
        Raises:
            TypeError: If widget doesn't implement ChangeSignalEmitter ABC
        """
        WidgetDispatcher.connect_change_signal(widget, callback)
    
    @staticmethod
    def disconnect_change_signal(widget: Any, callback: Callable[[Any], None]) -> None:
        """
        Disconnect change signal on any widget implementing ChangeSignalEmitter.
        
        Args:
            widget: The widget to disconnect signal from
            callback: Callback function to disconnect
        
        Raises:
            TypeError: If widget doesn't implement ChangeSignalEmitter ABC
        """
        WidgetDispatcher.disconnect_change_signal(widget, callback)
    
    @staticmethod
    def get_all_value_widgets(container: Any) -> list:
        """
        Get all widgets that implement ValueGettable ABC.

        Replaces findChildren() with explicit type lists.
        Uses ABC checking instead of duck typing.
        
        Args:
            container: The container widget to search in
        
        Returns:
            List of widgets implementing ValueGettable

        Example:
            >>> ops = WidgetOperations()
            >>> form = MyFormWidget()
            >>> value_widgets = ops.get_all_value_widgets(form)
            >>> values = {w.objectName(): ops.get_value(w) for w in value_widgets}
        """
        # Start with registered widget types
        widget_types = tuple(WIDGET_IMPLEMENTATIONS.values())
        collected = []
        if widget_types:
            collected.extend(container.findChildren(widget_types))

        # Fallback: also include any child that declares ValueGettable via ABC
        # (e.g., NoneAwareLineEdit/CheckBox which are registered virtually, not in WIDGET_IMPLEMENTATIONS)
        try:
            from PyQt6.QtCore import QObject
            for widget in container.findChildren(QObject):
                if isinstance(widget, ValueGettable):
                    collected.append(widget)
        except Exception:
            # If PyQt isn't available in a non-GUI context, gracefully return what we have
            pass

        # Deduplicate while preserving order
        seen_ids = set()
        value_widgets = []
        for widget in collected:
            wid = id(widget)
            if wid in seen_ids:
                continue
            seen_ids.add(wid)
            if isinstance(widget, ValueGettable):
                value_widgets.append(widget)

        return value_widgets
    
    @staticmethod
    def try_set_placeholder(widget: Any, text: str) -> bool:
        """
        Try to set placeholder, return False if widget doesn't support it.
        
        This is the ONLY acceptable use of "try" pattern - when placeholder
        support is truly optional and we want to gracefully skip widgets
        that don't support it.
        
        Args:
            widget: The widget to set placeholder on
            text: The placeholder text
        
        Returns:
            True if placeholder was set, False if widget doesn't support it
        """
        if not isinstance(widget, PlaceholderCapable):
            return False
        
        try:
            widget.set_placeholder(text)
            return True
        except Exception:
            # Unexpected error - log but don't crash
            import logging
            logging.getLogger(__name__).warning(
                f"Failed to set placeholder on {type(widget).__name__}: {text}",
                exc_info=True
            )
            return False
    
    @staticmethod
    def try_configure_range(widget: Any, minimum: float, maximum: float) -> bool:
        """
        Try to configure range, return False if widget doesn't support it.
        
        Similar to try_set_placeholder - acceptable for optional configuration.
        
        Args:
            widget: The widget to configure
            minimum: Minimum value
            maximum: Maximum value
        
        Returns:
            True if range was configured, False if widget doesn't support it
        """
        if not isinstance(widget, RangeConfigurable):
            return False
        
        try:
            widget.configure_range(minimum, maximum)
            return True
        except Exception:
            import logging
            logging.getLogger(__name__).warning(
                f"Failed to configure range on {type(widget).__name__}: [{minimum}, {maximum}]",
                exc_info=True
            )
            return False
