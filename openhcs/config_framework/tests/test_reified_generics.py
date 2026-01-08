"""
Tests for reified generics prototype.

Tests cover:
- Type identity and caching
- isinstance behavior
- issubclass with covariance
- Hash and equality
- Custom class decorator
"""

import pytest
from openhcs.config_framework.reified_generics import (
    List, Dict, Set, Tuple,
    ReifiedMeta,
    is_reified, get_reified_args, get_reified_origin,
    clear_cache, reified,
    _make_reified_type,
)


class TestTypeCaching:
    """Test that same parameterization returns same type object."""
    
    def setup_method(self):
        clear_cache()
    
    def test_list_int_identity(self):
        """List[int] is List[int] (cached)."""
        assert List[int] is List[int]
    
    def test_list_str_identity(self):
        """List[str] is List[str] (cached)."""
        assert List[str] is List[str]
    
    def test_different_params_different_types(self):
        """List[int] is not List[str]."""
        assert List[int] is not List[str]
    
    def test_dict_caching(self):
        """Dict[str, int] is Dict[str, int]."""
        assert Dict[str, int] is Dict[str, int]
    
    def test_dict_different_params(self):
        """Dict[str, int] is not Dict[int, str]."""
        assert Dict[str, int] is not Dict[int, str]


class TestInstanceCheck:
    """Test isinstance behavior with reified types."""
    
    def setup_method(self):
        clear_cache()
    
    def test_reified_list_isinstance(self):
        """isinstance(List[int]([1,2]), List[int]) is True."""
        x = List[int]([1, 2, 3])
        assert isinstance(x, List[int])
    
    def test_reified_list_not_isinstance_different_param(self):
        """isinstance(List[int]([1,2]), List[str]) is False."""
        x = List[int]([1, 2, 3])
        assert not isinstance(x, List[str])

    def test_reified_list_metadata_only(self):
        """Metadata-only: contents are not inspected."""
        x = List[int]([1, "a"])
        assert isinstance(x, List[int])

    def test_reified_list_isinstance_origin(self):
        """isinstance(List[int]([1,2]), list) is True."""
        x = List[int]([1, 2, 3])
        assert isinstance(x, list)
    
    def test_plain_list_not_isinstance_reified(self):
        """isinstance([1,2], List[int]) is False (not reified)."""
        x = [1, 2, 3]
        assert not isinstance(x, List[int])
    
    def test_dict_isinstance(self):
        """isinstance(Dict[str,int]({...}), Dict[str,int]) is True."""
        x = Dict[str, int]({"a": 1, "b": 2})
        assert isinstance(x, Dict[str, int])
        assert not isinstance(x, Dict[int, str])


class TestSubclassCheck:
    """Test issubclass behavior with covariance."""
    
    def setup_method(self):
        clear_cache()
    
    def test_same_type_subclass(self):
        """issubclass(List[int], List[int]) is True."""
        assert issubclass(List[int], List[int])
    
    def test_covariant_subclass(self):
        """issubclass(List[int], List[object]) is True (covariance)."""
        assert issubclass(List[int], List[object])
    
    def test_not_subclass_different_param(self):
        """issubclass(List[int], List[str]) is False."""
        assert not issubclass(List[int], List[str])
    
    def test_contravariant_not_subclass(self):
        """issubclass(List[object], List[int]) is False."""
        assert not issubclass(List[object], List[int])


class TestTypeAttributes:
    """Test __origin__, __args__, __reified__ attributes."""
    
    def setup_method(self):
        clear_cache()
    
    def test_origin(self):
        """List[int].__origin__ is list."""
        assert List[int].__origin__ is list
    
    def test_args(self):
        """List[int].__args__ is (int,)."""
        assert List[int].__args__ == (int,)
    
    def test_dict_args(self):
        """Dict[str, int].__args__ is (str, int)."""
        assert Dict[str, int].__args__ == (str, int)
    
    def test_reified_flag(self):
        """List[int].__reified__ is True."""
        assert List[int].__reified__ is True
    
    def test_instance_type_has_args(self):
        """type(List[int]([...])).__args__ is (int,)."""
        x = List[int]([1, 2, 3])
        assert type(x).__args__ == (int,)


class TestHashAndEquality:
    """Test hash and equality for use as dict keys."""
    
    def setup_method(self):
        clear_cache()
    
    def test_hash_consistent(self):
        """hash(List[int]) == hash(List[int])."""
        assert hash(List[int]) == hash(List[int])
    
    def test_hash_different_for_different_params(self):
        """hash(List[int]) != hash(List[str])."""
        assert hash(List[int]) != hash(List[str])
    
    def test_usable_as_dict_key(self):
        """Reified types can be dict keys."""
        handlers = {
            List[int]: "int_handler",
            List[str]: "str_handler",
        }
        assert handlers[List[int]] == "int_handler"
        assert handlers[List[str]] == "str_handler"
    
    def test_equality(self):
        """List[int] == List[int]."""
        assert List[int] == List[int]
        assert not (List[int] == List[str])


class TestCustomClassDecorator:
    """Test @reified decorator for custom classes."""
    
    def setup_method(self):
        clear_cache()
    
    def test_reified_decorator(self):
        """@reified makes custom class support generics."""
        @reified
        class Container:
            def __init__(self, items):
                self.items = items
        
        # Parameterization works
        IntContainer = Container[int]
        assert IntContainer.__args__ == (int,)
        assert IntContainer.__origin__ is Container
        
        # Caching works
        assert Container[int] is Container[int]
        assert Container[int] is not Container[str]
