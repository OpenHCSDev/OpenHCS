"""
Widget factory with explicit type-based dispatch.

Replaces duck typing with fail-loud type checking.
Mirrors MemoryType converter pattern - explicit type → widget mapping.

Design:
- WIDGET_TYPE_REGISTRY: Type → factory function mapping
- Explicit dispatch (no hasattr checks)
- Fail-loud if type not registered
- Handles Optional[T], Enum, List[Enum] types
"""

from typing import Type, Any, Dict, Callable, get_origin, get_args, Union
from enum import Enum
import logging

logger = logging.getLogger(__name__)

# Type-based widget creation dispatch - NO DUCK TYPING
# Maps Python type → widget factory function
WIDGET_TYPE_REGISTRY: Dict[Type, Callable] = {}


def _init_widget_type_registry():
    """
    Initialize widget type registry with Qt adapters.
    
    Lazy initialization to avoid import errors when PyQt6 not available.
    """
    global WIDGET_TYPE_REGISTRY
    
    if WIDGET_TYPE_REGISTRY:
        # Already initialized
        return
    
    try:
        from pyqt_formgen.protocols.widget_adapters import (
            LineEditAdapter, SpinBoxAdapter, DoubleSpinBoxAdapter,
            ComboBoxAdapter, CheckBoxAdapter
        )
        
        WIDGET_TYPE_REGISTRY.update({
            str: lambda: LineEditAdapter(),
            int: lambda: SpinBoxAdapter(),
            float: lambda: DoubleSpinBoxAdapter(),
            bool: lambda: CheckBoxAdapter(),
        })
        
        logger.debug("Initialized WIDGET_TYPE_REGISTRY with Qt adapters")
    except ImportError as e:
        logger.warning(f"Could not initialize Qt widget adapters: {e}")


def resolve_optional(param_type: Type) -> Type:
    """
    Resolve Optional[T] to T.
    
    Args:
        param_type: Type to resolve (e.g., Optional[int])
    
    Returns:
        Unwrapped type (e.g., int)
    """
    if get_origin(param_type) is Union:
        args = get_args(param_type)
        if len(args) == 2 and type(None) in args:
            return next(arg for arg in args if arg is not type(None))
    return param_type


def is_enum_type(param_type: Type) -> bool:
    """
    Check if type is an Enum.
    
    Args:
        param_type: Type to check
    
    Returns:
        True if param_type is an Enum subclass
    """
    return isinstance(param_type, type) and issubclass(param_type, Enum)


def is_list_of_enums(param_type: Type) -> bool:
    """
    Check if type is List[Enum].
    
    Args:
        param_type: Type to check
    
    Returns:
        True if param_type is List[SomeEnum]
    """
    if get_origin(param_type) is list:
        args = get_args(param_type)
        if args and is_enum_type(args[0]):
            return True
    return False


def get_enum_from_list(param_type: Type) -> Type:
    """
    Extract enum type from List[Enum].
    
    Args:
        param_type: List[Enum] type
    
    Returns:
        The Enum type
    """
    return get_args(param_type)[0]


class WidgetFactory:
    """
    Widget factory using explicit type-based dispatch.
    
    Replaces duck typing with fail-loud type checking.
    Mirrors the pattern from MemoryType converters.
    
    Example:
        factory = WidgetFactory()
        
        # Create widget for int parameter
        widget = factory.create_widget(int, "my_param")
        # Returns SpinBoxAdapter instance
        
        # Create widget for Enum parameter
        widget = factory.create_widget(MyEnum, "mode")
        # Returns ComboBoxAdapter populated with enum values
    """
    
    def __init__(self):
        """Initialize factory and ensure registry is populated."""
        _init_widget_type_registry()
    
    def create_widget(self, param_type: Type, param_name: str = "") -> Any:
        """
        Create widget for parameter type using explicit dispatch.
        
        Args:
            param_type: The parameter type to create widget for
            param_name: Optional parameter name for debugging
        
        Returns:
            Widget instance implementing required ABCs
        
        Raises:
            TypeError: If no widget registered for this type
        
        Example:
            >>> factory = WidgetFactory()
            >>> widget = factory.create_widget(int, "threshold")
            >>> isinstance(widget, SpinBoxAdapter)
            True
        """
        # Handle Optional[T] by unwrapping
        original_type = param_type
        param_type = resolve_optional(param_type)
        
        # Handle Enum types
        if is_enum_type(param_type):
            return self._create_enum_widget(param_type)
        
        # Handle List[Enum] types
        if is_list_of_enums(param_type):
            enum_type = get_enum_from_list(param_type)
            return self._create_enum_list_widget(enum_type)
        
        # Explicit type dispatch - FAIL LOUD if type not registered
        factory_func = WIDGET_TYPE_REGISTRY.get(param_type)
        if factory_func is None:
            raise TypeError(
                f"No widget registered for type {param_type} (parameter: '{param_name}'). "
                f"Available types: {list(WIDGET_TYPE_REGISTRY.keys())}. "
                f"Add widget factory to WIDGET_TYPE_REGISTRY or create custom adapter."
            )
        
        widget = factory_func()
        logger.debug(f"Created {type(widget).__name__} for parameter '{param_name}' (type: {param_type})")
        return widget
    
    def _create_enum_widget(self, enum_type: Type) -> Any:
        """
        Create ComboBox widget for Enum type.
        
        Args:
            enum_type: The Enum class
        
        Returns:
            ComboBoxAdapter populated with enum values
        """
        from pyqt_formgen.protocols.widget_adapters import ComboBoxAdapter
        
        widget = ComboBoxAdapter()
        widget.populate_enum(enum_type)
        logger.debug(f"Created ComboBoxAdapter for enum {enum_type.__name__}")
        return widget
    
    def _create_enum_list_widget(self, enum_type: Type) -> Any:
        """
        Create multi-select widget for List[Enum] type.
        
        Args:
            enum_type: The Enum class
        
        Returns:
            Multi-select widget (TODO: implement EnumMultiSelectAdapter)
        
        Note:
            Currently falls back to single-select ComboBox.
            Future: Implement proper multi-select widget.
        """
        # TODO: Implement EnumMultiSelectAdapter for List[Enum]
        # For now, fall back to single-select
        logger.warning(
            f"List[{enum_type.__name__}] not fully supported yet. "
            f"Using single-select ComboBox as fallback."
        )
        return self._create_enum_widget(enum_type)
    
    def register_widget_type(self, param_type: Type, factory_func: Callable) -> None:
        """
        Register custom widget factory for a type.
        
        Args:
            param_type: The Python type to register
            factory_func: Function that creates widget instance (no args)
        
        Example:
            >>> def create_path_widget():
            ...     return PathSelectorWidget()
            >>> factory = WidgetFactory()
            >>> factory.register_widget_type(Path, create_path_widget)
        """
        if param_type in WIDGET_TYPE_REGISTRY:
            logger.warning(
                f"Overwriting existing widget factory for type {param_type}"
            )
        
        WIDGET_TYPE_REGISTRY[param_type] = factory_func
        logger.debug(f"Registered widget factory for type {param_type}")

