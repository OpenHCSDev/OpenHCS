"""
Custom function registration system for OpenHCS.

This module enables users to define custom processing functions via code editor
and have them automatically registered in the function registry. Custom functions
are persisted to disk and auto-loaded on startup.

Core Components:
    - CustomFunctionManager: Manages custom function lifecycle (register, load, delete)
    - ValidationError: Exception raised for invalid custom function code
    - get_default_template: Returns default numpy template for custom functions
    - CustomFunctionSignals: Qt signals for UI updates when custom functions change

Example:
    >>> from openhcs.processing.custom_functions import CustomFunctionManager
    >>> manager = CustomFunctionManager()
    >>> code = '''
    ... from openhcs.core.memory.decorators import numpy
    ...
    ... @numpy
    ... def my_function(image, scale=1.0):
    ...     return image * scale
    ... '''
    >>> funcs = manager.register_from_code(code, persist=True)
    >>> print(f"Registered: {funcs[0].__name__}")
"""

from openhcs.processing.custom_functions.manager import CustomFunctionManager
from openhcs.processing.custom_functions.templates import (
    get_default_template,
    get_template_for_memory_type,
    AVAILABLE_MEMORY_TYPES,
)
from openhcs.processing.custom_functions.validation import ValidationError
from openhcs.processing.custom_functions.signals import CustomFunctionSignals, custom_function_signals

__all__ = [
    'CustomFunctionManager',
    'ValidationError',
    'get_default_template',
    'get_template_for_memory_type',
    'AVAILABLE_MEMORY_TYPES',
    'CustomFunctionSignals',
    'custom_function_signals',
]
