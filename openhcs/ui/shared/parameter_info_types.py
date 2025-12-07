"""
Discriminated union types for parameter information.

This module implements React-style discriminated unions for type-safe parameter handling.
Instead of using boolean flags (is_optional, is_nested), we use polymorphic types that
are automatically selected based on type annotations.

Key features:
1. Metaclass auto-registration - all ParameterInfo subclasses auto-register
2. Type-driven factory - create_parameter_info() uses type introspection
3. Zero boilerplate - just define new dataclass with matches() predicate
4. Type-safe dispatch - services use class name for automatic dispatch

Pattern (React-style):
    Instead of:
        @dataclass
        class ParameterInfo:
            is_optional: bool
            is_nested: bool
        
        if info.is_optional and info.is_nested:
            # handle optional dataclass
    
    Use:
        @dataclass
        class OptionalDataclassInfo(metaclass=ParameterInfoMeta):
            @staticmethod
            def matches(param_type): ...
        
        if isinstance(info, OptionalDataclassInfo):
            # Type checker knows info is OptionalDataclassInfo!

Architecture:
    - ParameterInfoMeta: Metaclass that auto-registers all subclasses
    - ParameterInfoBase: Base class for all parameter info types
    - OptionalDataclassInfo: Optional[Dataclass] parameters (checkbox-controlled)
    - DirectDataclassInfo: Direct Dataclass parameters (always exists)
    - GenericInfo: Generic parameters (simple widgets)
    - create_parameter_info(): Factory that auto-selects correct type
"""

from typing import Type, Any, Optional, List, Union, get_origin, get_args
from dataclasses import dataclass, is_dataclass
from abc import ABC, ABCMeta
import logging

logger = logging.getLogger(__name__)


@dataclass
class ParameterInfoBase(ABC):
    """ABC for parameter information objects - enforces explicit interface."""
    name: str
    type: Type
    current_value: Any
    description: Optional[str] = None

    # Widget creation type - subclasses override. Imported lazily to avoid circular imports.
    widget_creation_type: str = "REGULAR"  # Default, overridden by subclasses


class ParameterInfoMeta(ABCMeta):
    """
    Metaclass for auto-registration of ParameterInfo types.
    
    All classes with a matches() method are automatically registered
    in the global registry for use by the factory function.
    
    This eliminates manual registration and enables zero-boilerplate
    addition of new parameter types.
    """
    _registry: List[Type] = []
    
    def __new__(mcs, name, bases, namespace):
        cls = super().__new__(mcs, name, bases, namespace)
        
        # Auto-register if it has a matches() predicate
        if 'matches' in namespace and callable(namespace['matches']):
            mcs._registry.append(cls)
            logger.debug(f"Auto-registered ParameterInfo type: {name}")
        
        return cls
    
    @classmethod
    def get_registry(mcs) -> List[Type]:
        """Get all registered ParameterInfo types."""
        return mcs._registry.copy()


@dataclass
class OptionalDataclassInfo(ParameterInfoBase, metaclass=ParameterInfoMeta):
    """
    Parameter info for Optional[Dataclass] types.

    These parameters:
    - Have a checkbox to enable/disable
    - Have a nested form that appears when enabled
    - Can be None when checkbox is unchecked
    - Support lazy inheritance from parent configs

    Examples:
        def process(config: Optional[ProcessingConfig]): ...
        def analyze(settings: Optional[AnalysisSettings]): ...
    """
    default_value: Any = None
    is_required: bool = True
    widget_creation_type: str = "OPTIONAL_NESTED"

    @staticmethod
    def matches(param_type: Type) -> bool:
        """
        Predicate: Does this type annotation match Optional[Dataclass]?

        Returns True if:
        - Type is Union[T, None] (i.e., Optional[T])
        - T is a dataclass
        """
        # Check if Optional (Union with None)
        is_optional = get_origin(param_type) is Union and type(None) in get_args(param_type)
        if not is_optional:
            return False

        # Get inner type and check if dataclass
        inner_type = next(arg for arg in get_args(param_type) if arg is not type(None))
        return is_dataclass(inner_type)


@dataclass
class DirectDataclassInfo(ParameterInfoBase, metaclass=ParameterInfoMeta):
    """
    Parameter info for direct Dataclass types (non-optional).

    These parameters:
    - Always exist (never None)
    - Have a nested form that's always visible
    - Preserve object identity during reset
    - Don't have a checkbox

    Examples:
        def process(config: ProcessingConfig): ...
        def analyze(settings: AnalysisSettings): ...
    """
    default_value: Any = None
    is_required: bool = True
    widget_creation_type: str = "NESTED"

    @staticmethod
    def matches(param_type: Type) -> bool:
        """
        Predicate: Does this type annotation match a direct Dataclass?

        Returns True if:
        - Type is a dataclass
        - Type is NOT Optional
        """
        return is_dataclass(param_type)


@dataclass
class GenericInfo(ParameterInfoBase, metaclass=ParameterInfoMeta):
    """
    Parameter info for generic types (int, str, Path, etc.).

    These parameters:
    - Use simple widgets (QLineEdit, QSpinBox, etc.)
    - Don't have nested forms
    - Support lazy inheritance via placeholders
    - Are the most common parameter type

    Examples:
        def process(threshold: int): ...
        def analyze(input_path: Path): ...
        def filter(sigma: float): ...
    """
    default_value: Any = None
    is_required: bool = True

    @staticmethod
    def matches(param_type: Type) -> bool:
        """
        Predicate: Fallback - matches everything.

        This should be registered LAST in the registry so it acts
        as a catch-all for any types not matched by other predicates.
        """
        return True


# Union type for type hints (React-style)
ParameterInfo = Union[OptionalDataclassInfo, DirectDataclassInfo, GenericInfo]


def create_parameter_info(
    name: str,
    param_type: Type,
    current_value: Any,
    default_value: Any = None,
    description: Optional[str] = None,
    is_required: bool = True
) -> ParameterInfo:
    """
    Factory function that auto-selects the correct ParameterInfo subclass.
    
    Uses type introspection to determine which ParameterInfo type to create.
    This eliminates manual if-elif-else chains and enables type-safe dispatch.
    
    Args:
        name: Parameter name
        param_type: Parameter type annotation
        current_value: Current parameter value
        default_value: Default parameter value
        description: Parameter description
        is_required: Whether parameter is required
    
    Returns:
        Correct ParameterInfo subclass instance
    
    Raises:
        ValueError: If no matching ParameterInfo type found
    
    Examples:
        >>> from typing import Optional
        >>> @dataclass
        ... class Config: pass
        
        >>> info1 = create_parameter_info('config', Optional[Config], None)
        >>> type(info1).__name__
        'OptionalDataclassInfo'
        
        >>> info2 = create_parameter_info('config', Config, Config())
        >>> type(info2).__name__
        'DirectDataclassInfo'
        
        >>> info3 = create_parameter_info('value', int, 42)
        >>> type(info3).__name__
        'GenericInfo'
    """
    # Iterate through registered types and find first match
    for info_class in ParameterInfoMeta.get_registry():
        if info_class.matches(param_type):
            return info_class(
                name=name,
                type=param_type,
                current_value=current_value,
                default_value=default_value,
                description=description,
                is_required=is_required
            )
    
    # Should never reach here due to GenericInfo fallback
    raise ValueError(
        f"No matching ParameterInfo type for {param_type}. "
        f"This should never happen - GenericInfo should match everything."
    )

