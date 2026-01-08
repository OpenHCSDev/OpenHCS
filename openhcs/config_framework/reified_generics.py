"""
Reified Generics Prototype - Runtime-preserved type parameters.

This module provides a proof-of-concept implementation of reified generics,
where `List[int]` and `List[str]` are distinct types at runtime.

Core concepts:
- ReifiedMeta: Metaclass with custom __instancecheck__ and __subclasscheck__
- Type caching: Same parameterization returns same type object
- Covariance: issubclass(List[int], List[object]) works correctly

Usage:
    from openhcs.config_framework.reified_generics import List, Dict
    
    x = List[int]([1, 2, 3])
    isinstance(x, List[int])   # True
    isinstance(x, List[str])   # False
    type(x).__args__           # (int,)
"""

from typing import Dict as TypingDict, Tuple, Any, TypeVar, get_args, get_origin
import weakref

# =============================================================================
# TYPE CACHE - Reuse pattern from lazy_factory._lazy_class_cache
# =============================================================================

_reified_cache: TypingDict[Tuple[type, tuple], type] = {}


def _get_cached_type(origin: type, args: tuple) -> type:
    """Get or create cached reified type."""
    key = (origin, args)
    if key in _reified_cache:
        return _reified_cache[key]
    return None


def _cache_type(origin: type, args: tuple, reified_type: type) -> None:
    """Cache a reified type."""
    _reified_cache[(origin, args)] = reified_type


# =============================================================================
# REIFIED METACLASS - Pattern from GlobalConfigMeta.__instancecheck__
# =============================================================================

class ReifiedMeta(type):
    """
    Metaclass for reified generic types.
    
    Provides custom isinstance/issubclass behavior that respects type parameters.
    """
    
    def __instancecheck__(cls, instance: Any) -> bool:
        """Check if instance is of this reified type."""
        if not hasattr(cls, '__args__') or not hasattr(cls, '__origin__'):
            return super().__instancecheck__(instance)
        
        inst_type = type(instance)
        
        # Fast path: exact type match (reified instance)
        if inst_type is cls:
            return True
        
        # Check if instance has reified type info
        if hasattr(inst_type, '__args__') and hasattr(inst_type, '__origin__'):
            # Same origin and args = same type
            if inst_type.__origin__ is cls.__origin__:
                return inst_type.__args__ == cls.__args__
        
        # Fallback: check origin only (plain list passed to List[int])
        # This is the "trust mode" - we check the container type, not elements
        if isinstance(instance, cls.__origin__):
            # For non-reified instances, we can optionally check elements
            # For now, return False to enforce reified construction
            return False
        
        return False
    
    def __subclasscheck__(cls, subclass: type) -> bool:
        """Check subclass with covariance support."""
        if not hasattr(cls, '__args__') or not hasattr(cls, '__origin__'):
            return super().__subclasscheck__(subclass)
        
        # Handle reified subclass
        if hasattr(subclass, '__args__') and hasattr(subclass, '__origin__'):
            # Same origin required
            if subclass.__origin__ is not cls.__origin__:
                # Check if subclass origin inherits from cls origin
                if not issubclass(subclass.__origin__, cls.__origin__):
                    return False
            
            # Covariance: subclass args must be subtypes of cls args
            if len(subclass.__args__) != len(cls.__args__):
                return False
            
            for sub_arg, cls_arg in zip(subclass.__args__, cls.__args__):
                # Handle non-type args (like Literal values)
                if not isinstance(sub_arg, type) or not isinstance(cls_arg, type):
                    if sub_arg != cls_arg:
                        return False
                elif not issubclass(sub_arg, cls_arg):
                    return False
            
            return True
        
        # Plain type vs reified: list is subclass of List[object] (top type)
        if issubclass(subclass, cls.__origin__):
            # Only if cls has object/Any as all args
            return all(arg is object for arg in cls.__args__)
        
        return False
    
    def __hash__(cls) -> int:
        """Reified types are hashable for use as dict keys."""
        if hasattr(cls, '__origin__') and hasattr(cls, '__args__'):
            return hash((cls.__origin__, cls.__args__))
        return super().__hash__()
    
    def __eq__(cls, other: Any) -> bool:
        """Equality based on origin and args."""
        if not isinstance(other, type):
            return False
        if hasattr(cls, '__origin__') and hasattr(other, '__origin__'):
            if hasattr(cls, '__args__') and hasattr(other, '__args__'):
                return cls.__origin__ is other.__origin__ and cls.__args__ == other.__args__
        return cls is other
    
    def __repr__(cls) -> str:
        if hasattr(cls, '__origin__') and hasattr(cls, '__args__'):
            args_str = ', '.join(
                arg.__name__ if hasattr(arg, '__name__') else repr(arg)
                for arg in cls.__args__
            )
            return f"{cls.__origin__.__name__}[{args_str}]"
        return super().__repr__()


# =============================================================================
# REIFIED TYPE FACTORY
# =============================================================================

def _make_reified_type(origin: type, args: tuple) -> type:
    """Create a new reified type for origin[args]."""
    # Check cache first
    cached = _get_cached_type(origin, args)
    if cached is not None:
        return cached

    # Create type name
    args_str = ', '.join(
        arg.__name__ if hasattr(arg, '__name__') else repr(arg)
        for arg in args
    )
    type_name = f'{origin.__name__}[{args_str}]'

    # Create the reified type using metaclass
    reified_type = ReifiedMeta(
        type_name,
        (origin,),
        {
            '__origin__': origin,
            '__args__': args,
            '__reified__': True,
            '__module__': origin.__module__,
        }
    )

    # Cache and return
    _cache_type(origin, args, reified_type)
    return reified_type


# =============================================================================
# REIFIED WRAPPER CLASSES - Drop-in replacements for stdlib generics
# =============================================================================

class ReifiedList(list):
    """
    Reified list that preserves type parameters at runtime.

    Usage:
        x = List[int]([1, 2, 3])
        type(x)  # List[int]
        isinstance(x, List[int])  # True
    """
    __origin__ = list
    __args__: tuple = ()
    __reified__ = True

    def __class_getitem__(cls, params):
        """Create or retrieve cached reified type."""
        if not isinstance(params, tuple):
            params = (params,)
        return _make_reified_type(list, params)

    def __repr__(self):
        return f"{type(self)!r}({super().__repr__()})"


class ReifiedDict(dict):
    """
    Reified dict that preserves type parameters at runtime.

    Usage:
        x = Dict[str, int]({"a": 1})
        type(x)  # Dict[str, int]
        isinstance(x, Dict[str, int])  # True
    """
    __origin__ = dict
    __args__: tuple = ()
    __reified__ = True

    def __class_getitem__(cls, params):
        """Create or retrieve cached reified type."""
        if not isinstance(params, tuple):
            params = (params,)
        return _make_reified_type(dict, params)

    def __repr__(self):
        return f"{type(self)!r}({super().__repr__()})"


class ReifiedSet(set):
    """Reified set that preserves type parameters at runtime."""
    __origin__ = set
    __args__: tuple = ()
    __reified__ = True

    def __class_getitem__(cls, params):
        if not isinstance(params, tuple):
            params = (params,)
        return _make_reified_type(set, params)


class ReifiedTuple(tuple):
    """Reified tuple that preserves type parameters at runtime."""
    __origin__ = tuple
    __args__: tuple = ()
    __reified__ = True

    def __class_getitem__(cls, params):
        if not isinstance(params, tuple):
            params = (params,)
        return _make_reified_type(tuple, params)


# =============================================================================
# PUBLIC API - Aliased names matching typing module
# =============================================================================

List = ReifiedList
Dict = ReifiedDict
Set = ReifiedSet
Tuple = ReifiedTuple


# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def is_reified(t: type) -> bool:
    """Check if a type is a reified generic."""
    return getattr(t, '__reified__', False)


def get_reified_args(t: type) -> tuple:
    """Get type arguments from a reified type."""
    return getattr(t, '__args__', ())


def get_reified_origin(t: type) -> type:
    """Get origin type from a reified type."""
    return getattr(t, '__origin__', t)


def clear_cache() -> None:
    """Clear the reified type cache (for testing)."""
    _reified_cache.clear()


# =============================================================================
# DECORATOR FOR CUSTOM CLASSES
# =============================================================================

def reified(cls: type) -> type:
    """
    Decorator to make a class support reified generics.

    Usage:
        @reified
        class Container:
            def __init__(self, items):
                self.items = items

        x = Container[int]([1, 2, 3])
        isinstance(x, Container[int])  # True
    """
    original_class_getitem = getattr(cls, '__class_getitem__', None)

    def __class_getitem__(cls_inner, params):
        if not isinstance(params, tuple):
            params = (params,)
        return _make_reified_type(cls, params)

    cls.__class_getitem__ = classmethod(lambda c, p: __class_getitem__(c, p))
    cls.__origin__ = cls
    cls.__reified__ = True

    return cls

