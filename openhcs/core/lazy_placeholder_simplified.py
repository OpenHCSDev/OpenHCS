"""
Simplified lazy placeholder service using new contextvars system.

Provides placeholder text resolution for lazy configuration dataclasses
using the new contextvars-based context management.
"""

from typing import Any, Optional
import dataclasses
import logging

logger = logging.getLogger(__name__)


# _has_concrete_field_override moved to dual_axis_resolver_recursive.py
# Placeholder service should not contain inheritance logic


class LazyDefaultPlaceholderService:
    """
    Simplified placeholder service using new contextvars system.
    
    Provides consistent placeholder pattern for lazy configuration classes
    using the same resolution mechanism as the compiler.
    """
    
    PLACEHOLDER_PREFIX = "Default"
    NONE_VALUE_TEXT = "(none)"

    @staticmethod
    def has_lazy_resolution(dataclass_type: type) -> bool:
        """Check if dataclass has lazy resolution methods (created by factory)."""
        from typing import get_origin, get_args, Union
        
        # Unwrap Optional types (Union[Type, None])
        if get_origin(dataclass_type) is Union:
            args = get_args(dataclass_type)
            if len(args) == 2 and type(None) in args:
                dataclass_type = next(arg for arg in args if arg is not type(None))
        
        return (hasattr(dataclass_type, '_resolve_field_value') and
                hasattr(dataclass_type, 'to_base_config'))

    @staticmethod
    def get_lazy_resolved_placeholder(
        dataclass_type: type,
        field_name: str,
        placeholder_prefix: Optional[str] = None,
        context_obj: Optional[Any] = None
    ) -> Optional[str]:
        """
        Get placeholder text using the new contextvars system.

        Args:
            dataclass_type: The dataclass type to resolve for
            field_name: Name of the field to resolve
            placeholder_prefix: Optional prefix for placeholder text
            context_obj: Optional context object (orchestrator, step, dataclass instance, etc.) - unused since context should be set externally

        Returns:
            Formatted placeholder text or None if no resolution possible
        """
        prefix = placeholder_prefix or LazyDefaultPlaceholderService.PLACEHOLDER_PREFIX

        # Check if this is a lazy dataclass
        is_lazy = LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type)

        # If not lazy, try to find the lazy version
        if not is_lazy:
            lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(dataclass_type)
            if lazy_type:
                dataclass_type = lazy_type
            else:
                # Use direct class default for non-lazy types
                result = LazyDefaultPlaceholderService._get_class_default_placeholder(
                    dataclass_type, field_name, prefix
                )
                return result

        # Simple approach: Create new instance and let lazy system handle context resolution
        # The context_obj parameter is unused since context should be set externally via config_context()
        try:
            instance = dataclass_type()
            resolved_value = getattr(instance, field_name)
            result = LazyDefaultPlaceholderService._format_placeholder_text(resolved_value, prefix)
        except Exception as e:
            logger.debug(f"Failed to resolve {dataclass_type.__name__}.{field_name}: {e}")
            # Fallback to class default
            class_default = LazyDefaultPlaceholderService._get_class_default_value(dataclass_type, field_name)
            result = LazyDefaultPlaceholderService._format_placeholder_text(class_default, prefix)

        return result

    @staticmethod
    def _get_lazy_type_for_base(base_type: type) -> Optional[type]:
        """Get the lazy type for a base dataclass type (reverse lookup)."""
        from openhcs.config_framework.lazy_factory import _lazy_type_registry

        for lazy_type, registered_base_type in _lazy_type_registry.items():
            if registered_base_type == base_type:
                return lazy_type
        return None



    @staticmethod
    def _get_class_default_placeholder(dataclass_type: type, field_name: str, prefix: str) -> Optional[str]:
        """Get placeholder for non-lazy dataclasses using class defaults."""
        try:
            # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
            class_default = object.__getattribute__(dataclass_type, field_name)
            if class_default is not None:
                return LazyDefaultPlaceholderService._format_placeholder_text(class_default, prefix)
        except AttributeError:
            pass
        return None

    @staticmethod
    def _get_class_default_value(dataclass_type: type, field_name: str) -> Any:
        """Get class default value for a field."""
        try:
            # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
            return object.__getattribute__(dataclass_type, field_name)
        except AttributeError:
            return None

    @staticmethod
    def _format_placeholder_text(resolved_value: Any, prefix: str) -> Optional[str]:
        """Format resolved value into placeholder text."""
        if resolved_value is None:
            value_text = LazyDefaultPlaceholderService.NONE_VALUE_TEXT
        elif hasattr(resolved_value, '__dataclass_fields__'):
            value_text = LazyDefaultPlaceholderService._format_nested_dataclass_summary(resolved_value)
        else:
            # Apply proper formatting for different value types
            if hasattr(resolved_value, 'value') and hasattr(resolved_value, 'name'):  # Enum
                try:
                    from openhcs.ui.shared.ui_utils import format_enum_display
                    value_text = format_enum_display(resolved_value)
                except ImportError:
                    value_text = str(resolved_value)
            else:
                value_text = str(resolved_value)
        
        # Apply prefix formatting
        if not prefix:
            return value_text
        elif prefix.endswith(': '):
            return f"{prefix}{value_text}"
        elif prefix.endswith(':'):
            return f"{prefix} {value_text}"
        else:
            return f"{prefix}: {value_text}"

    @staticmethod
    def _format_nested_dataclass_summary(dataclass_instance) -> str:
        """
        Format nested dataclass with all field values for user-friendly placeholders.
        """
        
        class_name = dataclass_instance.__class__.__name__
        all_fields = [f.name for f in dataclasses.fields(dataclass_instance)]
        
        field_summaries = []
        for field_name in all_fields:
            try:
                value = getattr(dataclass_instance, field_name)
                
                # Skip None values to keep summary concise
                if value is None:
                    continue
                
                # Format different value types appropriately
                if hasattr(value, 'value') and hasattr(value, 'name'):  # Enum
                    try:
                        from openhcs.ui.shared.ui_utils import format_enum_display
                        formatted_value = format_enum_display(value)
                    except ImportError:
                        formatted_value = str(value)
                elif isinstance(value, str) and len(value) > 20:  # Long strings
                    formatted_value = f"{value[:17]}..."
                elif dataclasses.is_dataclass(value):  # Nested dataclass
                    formatted_value = f"{value.__class__.__name__}(...)"
                else:
                    formatted_value = str(value)
                
                field_summaries.append(f"{field_name}={formatted_value}")
                
            except (AttributeError, Exception):
                continue
        
        if field_summaries:
            return ", ".join(field_summaries)
        else:
            return f"{class_name} (default settings)"


# Backward compatibility functions
def get_lazy_resolved_placeholder(*args, **kwargs):
    """Backward compatibility wrapper."""
    return LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(*args, **kwargs)
