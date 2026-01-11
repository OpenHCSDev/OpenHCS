"""
Widget registry with metaclass auto-registration.

Mirrors StorageBackendMeta pattern - widgets auto-register when their classes
are defined, eliminating manual registration boilerplate.

Design:
- WidgetMeta metaclass handles auto-registration
- WIDGET_IMPLEMENTATIONS: Global registry of all widget types
- WIDGET_CAPABILITIES: Tracks which ABCs each widget implements
- Fail-loud if widget missing _widget_id or abstract methods
"""

from abc import ABCMeta
from typing import Dict, Type, Set
import logging

logger = logging.getLogger(__name__)

# Global registry of widget implementations
# Maps widget_id -> widget class
WIDGET_IMPLEMENTATIONS: Dict[str, Type] = {}

# Track which ABCs each widget implements
# Maps widget class -> set of ABC classes
WIDGET_CAPABILITIES: Dict[Type, Set[Type]] = {}


class WidgetMeta(ABCMeta):
    """
    Metaclass for automatic widget registration.
    
    Mirrors StorageBackendMeta pattern:
    1. Only registers concrete implementations (no abstract methods)
    2. Requires _widget_id attribute for identification
    3. Auto-populates WIDGET_IMPLEMENTATIONS registry
    4. Tracks capabilities (which ABCs implemented)
    
    Example:
        class LineEditAdapter(QLineEdit, ValueGettable, ValueSettable, 
                              metaclass=WidgetMeta):
            _widget_id = "line_edit"
            
            def get_value(self) -> Any:
                return self.text()
            
            def set_value(self, value: Any) -> None:
                self.setText(str(value) if value is not None else "")
    
    The widget auto-registers in WIDGET_IMPLEMENTATIONS["line_edit"] when
    the class is defined.
    """
    
    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)
        
        # Only register concrete implementations (no abstract methods remaining)
        if not getattr(new_class, '__abstractmethods__', None):
            # Extract widget identifier
            widget_id = getattr(new_class, '_widget_id', None)
            
            if widget_id is None:
                # No _widget_id - skip registration (might be intermediate base class)
                logger.debug(f"Skipping registration for {name} - no _widget_id attribute")
                return new_class
            
            # Check for duplicate registration
            if widget_id in WIDGET_IMPLEMENTATIONS:
                existing = WIDGET_IMPLEMENTATIONS[widget_id]
                logger.warning(
                    f"Widget ID '{widget_id}' already registered to {existing.__name__}. "
                    f"Overwriting with {name}."
                )
            
            # Auto-register in global registry
            WIDGET_IMPLEMENTATIONS[widget_id] = new_class
            
            # Track capabilities (which ABCs this widget implements)
            capabilities = set()
            
            # Import ABCs to check against
            from pyqt_formgen.protocols import (
                ValueGettable, ValueSettable, PlaceholderCapable,
                RangeConfigurable, EnumSelectable, ChangeSignalEmitter
            )
            
            abc_types = {
                ValueGettable, ValueSettable, PlaceholderCapable,
                RangeConfigurable, EnumSelectable, ChangeSignalEmitter
            }
            
            # Check which ABCs this widget implements
            for abc_type in abc_types:
                if issubclass(new_class, abc_type):
                    capabilities.add(abc_type)
            
            WIDGET_CAPABILITIES[new_class] = capabilities
            
            logger.debug(
                f"Auto-registered {name} as '{widget_id}' with capabilities: "
                f"{[c.__name__ for c in capabilities]}"
            )
        else:
            # Abstract class - log for debugging
            abstract_methods = getattr(new_class, '__abstractmethods__', set())
            logger.debug(
                f"Skipping registration for {name} - abstract methods remaining: "
                f"{abstract_methods}"
            )
        
        return new_class


def get_widget_class(widget_id: str) -> Type:
    """
    Get widget class by ID.
    
    Args:
        widget_id: The widget identifier (e.g., "line_edit")
    
    Returns:
        The widget class
    
    Raises:
        KeyError: If widget_id not registered
    """
    if widget_id not in WIDGET_IMPLEMENTATIONS:
        raise KeyError(
            f"No widget registered with ID '{widget_id}'. "
            f"Available widgets: {list(WIDGET_IMPLEMENTATIONS.keys())}"
        )
    return WIDGET_IMPLEMENTATIONS[widget_id]


def get_widget_capabilities(widget_class: Type) -> Set[Type]:
    """
    Get the ABCs that a widget class implements.
    
    Args:
        widget_class: The widget class to query
    
    Returns:
        Set of ABC classes the widget implements
    """
    return WIDGET_CAPABILITIES.get(widget_class, set())


def list_widgets_with_capability(capability: Type) -> list[Type]:
    """
    Find all widgets that implement a specific ABC.
    
    Args:
        capability: The ABC class to search for (e.g., ValueGettable)
    
    Returns:
        List of widget classes implementing the ABC
    
    Example:
        >>> from pyqt_formgen.protocols import PlaceholderCapable
        >>> widgets = list_widgets_with_capability(PlaceholderCapable)
        >>> print([w.__name__ for w in widgets])
        ['LineEditAdapter', 'SpinBoxAdapter', 'ComboBoxAdapter']
    """
    return [
        widget_class
        for widget_class, capabilities in WIDGET_CAPABILITIES.items()
        if capability in capabilities
    ]

