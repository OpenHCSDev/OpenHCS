"""
UI utilities for pyqt-formgen.

Simple formatting and debug utilities used across the forms layer.
"""

import logging
from enum import Enum
from typing import Any


def format_param_name(name: str) -> str:
    """Convert snake_case to Title Case: 'param_name' -> 'Param Name'"""
    return name.replace('_', ' ').title()


def format_checkbox_label(name: str) -> str:
    """Create checkbox label: 'param_name' -> 'Enable Param Name'"""
    return f"Enable {format_param_name(name)}"


def format_field_label(name: str) -> str:
    """Create field label: 'param_name' -> 'Param Name:'"""
    return f"{format_param_name(name)}:"


def format_field_id(parent: str, param: str) -> str:
    """Generate field ID: 'parent', 'param' -> 'parent_param'"""
    return f"{parent}_{param}"


def debug_param(param_name: str, value: Any, context: str = "") -> None:
    """Simple parameter debug logging"""
    context_str = f" [{context}]" if context else ""
    logging.debug(f"PARAM: {param_name} = {value}{context_str}")


def format_enum_display(enum_value: Enum) -> str:
    """Get enum display text: Enum.VALUE -> 'VALUE'"""
    return enum_value.name.upper()


def format_enum_placeholder(enum_value: Enum, prefix: str = "Pipeline default: ") -> str:
    """Get enum placeholder: Enum.VALUE -> 'Pipeline default: VALUE'"""
    return f"{prefix}{format_enum_display(enum_value)}"

