# openhcs/core/pipeline/pipeline_utils.py
"""Utility functions for the OpenHCS pipeline system."""
from typing import Any, Callable, Optional

def get_core_callable(func_pattern: Any) -> Optional[Callable[..., Any]]:
    """
    Extracts the first effective Python callable from a func_pattern.
    A func_pattern can be a direct callable, a (callable, kwargs) tuple,
    a list (chain) where the first element is one of these types,
    or a dict pattern where we extract from the first value.
    """
    # Check for FunctionReference first
    try:
        from openhcs.core.pipeline.compiler import FunctionReference
        if isinstance(func_pattern, FunctionReference):
            return func_pattern.resolve()
    except ImportError:
        pass

    if callable(func_pattern) and not isinstance(func_pattern, type):
        # It's a direct callable (and not an uninstantiated class)
        return func_pattern
    elif isinstance(func_pattern, tuple) and func_pattern:
        # It's a (callable, kwargs) tuple, check first element
        first_element = func_pattern[0]

        # Check if first element is a FunctionReference
        try:
            from openhcs.core.pipeline.compiler import FunctionReference
            if isinstance(first_element, FunctionReference):
                return first_element.resolve()
        except ImportError:
            pass

        # Check if first element is a regular callable
        if callable(first_element) and not isinstance(first_element, type):
            return first_element
    elif isinstance(func_pattern, list) and func_pattern:
        # It's a list (chain), recursively call for the first item
        return get_core_callable(func_pattern[0])
    elif isinstance(func_pattern, dict) and func_pattern:
        # It's a dict pattern, extract from the first value
        # For transformed dict patterns, we want the transformed function with namespaced outputs
        for key, value in func_pattern.items():
            core_callable = get_core_callable(value)
            if core_callable:
                return core_callable
    return None

