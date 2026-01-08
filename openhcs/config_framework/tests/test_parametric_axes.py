"""
Tests for parametric axes prototype.

Tests cover:
- axes_type() factory function
- @with_axes decorator
- __axes__ introspection
- Individual axis access via __<name>__
- Utility functions
"""

import pytest
from openhcs.config_framework.parametric_axes import (
    axes_type, with_axes, AxesMeta,
    get_axes, get_axis, has_axis,
)


class TestAxesTypeFactory:
    """Test axes_type() factory function."""
    
    def test_basic_axes(self):
        """Create type with scope axis."""
        MyType = axes_type("MyType", (), {}, scope="/pipeline/step_0")
        
        assert MyType.__name__ == "MyType"
        assert MyType.__axes__ == {"scope": "/pipeline/step_0"}
    
    def test_multiple_axes(self):
        """Create type with multiple axes."""
        registry = {"handlers": []}
        MyType = axes_type("MyType", (), {},
                          scope="/pipeline/step_0",
                          registry=registry,
                          version="1.0")
        
        assert MyType.__axes__["scope"] == "/pipeline/step_0"
        assert MyType.__axes__["registry"] is registry
        assert MyType.__axes__["version"] == "1.0"
    
    def test_convenience_attributes(self):
        """Individual axes accessible as __<name>__."""
        MyType = axes_type("MyType", (), {}, scope="/test", priority=10)
        
        assert MyType.__scope__ == "/test"
        assert MyType.__priority__ == 10
    
    def test_with_bases(self):
        """Axes work with inheritance."""
        class Base:
            pass
        
        Child = axes_type("Child", (Base,), {}, scope="/child")
        
        assert issubclass(Child, Base)
        assert Child.__axes__ == {"scope": "/child"}
    
    def test_with_namespace(self):
        """Axes work with class namespace."""
        MyType = axes_type("MyType", (), {"x": 1, "foo": lambda self: 42},
                          scope="/test")
        
        assert MyType.x == 1
        assert MyType.__axes__ == {"scope": "/test"}
    
    def test_empty_axes(self):
        """Type with no axes has empty __axes__."""
        MyType = axes_type("MyType", (), {})
        
        assert MyType.__axes__ == {}


class TestWithAxesDecorator:
    """Test @with_axes decorator."""
    
    def test_basic_decorator(self):
        """Decorator attaches axes to class."""
        @with_axes(scope="/decorated")
        class MyClass:
            pass
        
        assert MyClass.__axes__ == {"scope": "/decorated"}
    
    def test_decorator_multiple_axes(self):
        """Decorator with multiple axes."""
        @with_axes(scope="/test", registry="handlers", version=2)
        class MyClass:
            value = 42
        
        assert MyClass.__axes__["scope"] == "/test"
        assert MyClass.__axes__["registry"] == "handlers"
        assert MyClass.__axes__["version"] == 2
        assert MyClass.value == 42
    
    def test_decorator_preserves_inheritance(self):
        """Decorator preserves base classes."""
        class Base:
            base_attr = "base"
        
        @with_axes(scope="/child")
        class Child(Base):
            child_attr = "child"
        
        assert issubclass(Child, Base)
        assert Child.base_attr == "base"
        assert Child.child_attr == "child"
        assert Child.__axes__ == {"scope": "/child"}
    
    def test_decorator_preserves_methods(self):
        """Decorator preserves methods."""
        @with_axes(scope="/test")
        class MyClass:
            def method(self):
                return "hello"
        
        obj = MyClass()
        assert obj.method() == "hello"


class TestUtilityFunctions:
    """Test utility functions."""
    
    def test_get_axes(self):
        """get_axes returns all axes."""
        MyType = axes_type("MyType", (), {}, a=1, b=2)
        
        assert get_axes(MyType) == {"a": 1, "b": 2}
    
    def test_get_axes_plain_class(self):
        """get_axes returns {} for plain class."""
        class Plain:
            pass
        
        assert get_axes(Plain) == {}
    
    def test_get_axis(self):
        """get_axis returns specific axis."""
        MyType = axes_type("MyType", (), {}, scope="/test")
        
        assert get_axis(MyType, "scope") == "/test"
        assert get_axis(MyType, "missing") is None
        assert get_axis(MyType, "missing", "default") == "default"
    
    def test_has_axis(self):
        """has_axis checks axis presence."""
        MyType = axes_type("MyType", (), {}, scope="/test")
        
        assert has_axis(MyType, "scope") is True
        assert has_axis(MyType, "missing") is False


class TestRepr:
    """Test string representation."""
    
    def test_repr_with_axes(self):
        """Repr shows axes."""
        MyType = axes_type("MyType", (), {}, scope="/test")
        
        r = repr(MyType)
        assert "MyType" in r
        assert "scope" in r


class TestRealWorldExample:
    """Test real-world usage patterns from OpenHCS."""
    
    def test_step_with_scope(self):
        """Simulate OpenHCS step registration."""
        class Step:
            pass
        
        # What we currently do with ObjectStateRegistry.register()
        # Now expressible directly:
        ProcessingStep = axes_type(
            "ProcessingStep", (Step,), {},
            scope="/pipeline/step_0",
            registry="processing_steps"
        )
        
        assert ProcessingStep.__scope__ == "/pipeline/step_0"
        assert ProcessingStep.__registry__ == "processing_steps"
    
    def test_handler_with_registry(self):
        """Simulate OpenHCS handler registration."""
        HANDLERS = {}
        
        @with_axes(registry=HANDLERS, format_name="imagexpress")
        class ImageXpressHandler:
            pass
        
        # Framework can now introspect uniformly:
        axes = get_axes(ImageXpressHandler)
        axes["registry"][axes["format_name"]] = ImageXpressHandler
        
        assert HANDLERS["imagexpress"] is ImageXpressHandler

