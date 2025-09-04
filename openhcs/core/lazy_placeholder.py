"""
Lazy placeholder service for UI components.

Provides placeholder text resolution for lazy configuration dataclasses.
"""

from typing import Any, Optional, Type
import dataclasses

# Import functions from their new locations after refactoring
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.context.global_config import get_current_global_config, set_current_global_config
from openhcs.core.lazy_config import get_base_type_for_lazy


def _resolve_field_with_composition_awareness(instance, field_name: str):
    """
    Generic composition-aware field resolution supporting both inheritance and composition.

    Supports both patterns:
    1. Inheritance: field_name exists directly and inherits from global config
    2. Composition: field_name exists in nested composed dataclasses

    Args:
        instance: The dataclass instance to search in (uses working lazy resolution)
        field_name: The field name to find (may be direct or in composed dataclasses)

    Returns:
        The resolved field value using working lazy resolution, or None if not found
    """
    from dataclasses import fields, is_dataclass

    # Check if field exists directly on this instance (avoid triggering lazy resolution)
    direct_field_names = {f.name for f in fields(type(instance))}

    if field_name in direct_field_names:
        # INHERITANCE PATTERN: Field exists directly - use working lazy resolution code path
        try:
            return getattr(instance, field_name)
        except AttributeError:
            return None

    # COMPOSITION PATTERN: Field doesn't exist directly - traverse composed dataclasses
    result = _search_in_composed_dataclasses(instance, field_name)
    if result is not None:
        return result

    # INHERITANCE FALLBACK: Check if field exists in global config with different naming
    # e.g., well_filter might inherit from well_filter_config.well_filter
    result = _search_in_global_config_inheritance(instance, field_name)
    if result is not None:
        return result

    return None


def _search_in_composed_dataclasses(instance, field_name: str):
    """Search for field_name in composed dataclasses using working lazy resolution."""
    from dataclasses import fields, is_dataclass

    for field in fields(type(instance)):
        try:
            # Use working lazy resolution to get nested value
            nested_value = getattr(instance, field.name)
            if nested_value is not None and is_dataclass(nested_value):
                # Recursively search using working lazy resolution (generic N-levels deep)
                result = _resolve_field_with_composition_awareness(nested_value, field_name)
                if result is not None:
                    return result
            elif nested_value is None:
                # Handle optional nested configs: try both global config and default instances
                if hasattr(instance, '_resolve_field_value'):
                    # First try global config lookup
                    result = _handle_optional_nested_config(instance, field.name, field_name)
                    if result is not None:
                        return result

                # CRITICAL FIX: Also try creating default instance for deeply nested Optional fields
                result = _create_default_instance_and_search(instance, field.name, field_name)
                if result is not None:
                    return result
        except AttributeError:
            continue

    return None


def _create_default_instance_and_search(instance, nested_field_name: str, target_field_name: str):
    """Create default instance for Optional nested config and search for target field."""
    from dataclasses import fields, is_dataclass
    from typing import Union

    try:
        # Get the nested config class from the field type
        for field in fields(type(instance)):
            if field.name == nested_field_name:
                nested_config_class = field.type

                # Handle Optional[ConfigClass] types
                if hasattr(nested_config_class, '__origin__') and nested_config_class.__origin__ is Union:
                    # Extract the actual config class from Optional[ConfigClass]
                    nested_config_class = next(
                        (arg for arg in nested_config_class.__args__
                         if arg is not type(None) and is_dataclass(arg)),
                        None
                    )

                if nested_config_class and is_dataclass(nested_config_class):
                    # Create default instance and search in it recursively
                    default_nested = nested_config_class()
                    result = _resolve_field_with_composition_awareness(default_nested, target_field_name)
                    if result is not None:
                        return result
                break
    except (AttributeError, TypeError):
        pass

    return None


def _create_default_instance_and_search(instance, nested_field_name: str, target_field_name: str):
    """Create default instance for Optional nested config and search for target field."""
    from dataclasses import fields, is_dataclass
    from typing import Union

    try:
        # Get the nested config class from the field type
        for field in fields(type(instance)):
            if field.name == nested_field_name:
                nested_config_class = field.type

                # Handle Optional[ConfigClass] types
                if hasattr(nested_config_class, '__origin__') and nested_config_class.__origin__ is Union:
                    # Extract the actual config class from Optional[ConfigClass]
                    nested_config_class = next(
                        (arg for arg in nested_config_class.__args__
                         if arg is not type(None) and is_dataclass(arg)),
                        None
                    )

                if nested_config_class and is_dataclass(nested_config_class):
                    # Create default instance and search in it recursively
                    default_nested = nested_config_class()
                    result = _resolve_field_with_composition_awareness(default_nested, target_field_name)
                    if result is not None:
                        return result
                break
    except (AttributeError, TypeError):
        pass

    return None


def _handle_optional_nested_config(instance, nested_field_name: str, target_field_name: str):
    """Handle optional nested configs that are None by checking global config and defaults."""
    from openhcs.core.context.global_config import get_current_global_config
    from openhcs.core.lazy_config import get_base_type_for_lazy
    from dataclasses import is_dataclass, fields

    try:
        base_type = get_base_type_for_lazy(type(instance))
        if base_type:
            global_config = get_current_global_config(base_type)
            if global_config and hasattr(global_config, nested_field_name):
                global_nested = getattr(global_config, nested_field_name)
                if global_nested is not None and is_dataclass(global_nested):
                    # Search in the global nested config
                    result = _resolve_field_with_composition_awareness(global_nested, target_field_name)
                    if result is not None:
                        return result

                # CRITICAL FIX: If global nested config is None or doesn't have the field,
                # fall back to the default values of the nested config class
                if global_nested is None:
                    # Get the nested config class from the field type
                    for field in fields(type(global_config)):
                        if field.name == nested_field_name:
                            nested_config_class = field.type

                            # Handle Optional[ConfigClass] types
                            if hasattr(nested_config_class, '__origin__'):
                                from typing import Union
                                if nested_config_class.__origin__ is Union:
                                    # Extract the actual config class from Optional[ConfigClass]
                                    nested_config_class = next(
                                        (arg for arg in nested_config_class.__args__
                                         if arg is not type(None) and is_dataclass(arg)),
                                        None
                                    )

                            if nested_config_class and is_dataclass(nested_config_class):
                                # Create default instance and search in it
                                default_nested = nested_config_class()
                                result = _resolve_field_with_composition_awareness(default_nested, target_field_name)
                                if result is not None:
                                    return result
                            break
    except (AttributeError, TypeError):
        pass

    return None


def _search_in_global_config_inheritance(instance, field_name: str):
    """Search for field_name in global config using inheritance patterns."""
    from openhcs.core.context.global_config import get_current_global_config
    from openhcs.core.config import GlobalPipelineConfig
    from dataclasses import fields, is_dataclass

    try:
        # Step configs inherit from GlobalPipelineConfig, not their own base type
        global_config = get_current_global_config(GlobalPipelineConfig)
        if global_config:
            # Check for inheritance patterns like:
            # field_name -> field_name_config.field_name
            # well_filter -> well_filter_config.well_filter
            # well_filter_mode -> well_filter_config.well_filter_mode

            # Try the base field name pattern first
            base_field_name = field_name
            if field_name.endswith('_mode'):
                # For fields like well_filter_mode, try well_filter_config
                base_field_name = field_name.replace('_mode', '')

            potential_config_field = f"{base_field_name}_config"

            if hasattr(global_config, potential_config_field):
                config_value = getattr(global_config, potential_config_field)
                if config_value is not None and is_dataclass(config_value):
                    if hasattr(config_value, field_name):
                        return getattr(config_value, field_name)

                # CRITICAL FIX: If config_value is None, fall back to default values
                elif config_value is None:
                    # Get the config class type from the field definition
                    for field in fields(type(global_config)):
                        if field.name == potential_config_field:
                            config_class = field.type
                            if is_dataclass(config_class):
                                # Create default instance and check for the field
                                default_config = config_class()
                                if hasattr(default_config, field_name):
                                    default_value = getattr(default_config, field_name)
                                    # Only return non-None default values
                                    if default_value is not None:
                                        return default_value
                            break
    except (AttributeError, TypeError):
        pass

    return None


class LazyDefaultPlaceholderService:
    """
    Enhanced service supporting factory-created lazy classes with flexible resolution.

    Provides consistent placeholder pattern for both static and dynamic lazy configuration classes.
    """

    # Configurable placeholder prefix - default for when no prefix is explicitly provided
    PLACEHOLDER_PREFIX = "Default"

    @staticmethod
    def has_lazy_resolution(dataclass_type: type) -> bool:
        """Check if dataclass has lazy resolution methods (created by factory)."""
        # Handle Optional[LazyDataclass] types by unwrapping them first
        from typing import get_origin, get_args, Union

        # Unwrap Optional types (Union[Type, None])
        if get_origin(dataclass_type) is Union:
            args = get_args(dataclass_type)
            if len(args) == 2 and type(None) in args:
                # Get the non-None type from Optional[Type]
                dataclass_type = next(arg for arg in args if arg is not type(None))

        return (hasattr(dataclass_type, '_resolve_field_value') and
                hasattr(dataclass_type, 'to_base_config'))

    NONE_VALUE_TEXT = "(none)"

    @staticmethod
    def get_lazy_resolved_placeholder(
        dataclass_type: type,
        field_name: str,
        app_config: Optional[Any] = None,
        force_static_defaults: bool = False,
        placeholder_prefix: Optional[str] = None
    ) -> Optional[str]:
        """Get placeholder text for lazy-resolved field with flexible resolution."""
        if not LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type):
            return None

        prefix = placeholder_prefix or LazyDefaultPlaceholderService.PLACEHOLDER_PREFIX

        # SIMPLIFIED: Always use the actual lazy resolution logic for consistency
        if force_static_defaults:
            # For static defaults, temporarily clear context to get base class defaults
            current_context = get_current_global_config(GlobalPipelineConfig)
            set_current_global_config(GlobalPipelineConfig, None)
            try:
                resolved_value = dataclass_type()._resolve_field_value(field_name) if hasattr(dataclass_type, '_resolve_field_value') else getattr(dataclass_type(), field_name)
            finally:
                set_current_global_config(GlobalPipelineConfig, current_context)
        elif app_config:
            # For app config, set it as context and use lazy resolution
            current_context = get_current_global_config(GlobalPipelineConfig)
            set_current_global_config(GlobalPipelineConfig, app_config)
            try:
                resolved_value = dataclass_type()._resolve_field_value(field_name) if hasattr(dataclass_type, '_resolve_field_value') else getattr(dataclass_type(), field_name)
            finally:
                set_current_global_config(GlobalPipelineConfig, current_context)
        else:
            # Default: Use current thread-local context with actual lazy resolution
            if hasattr(dataclass_type, '_resolve_field_value'):
                # Generic composition-aware placeholder resolution
                lazy_instance = dataclass_type()
                resolved_value = _resolve_field_with_composition_awareness(lazy_instance, field_name)
            else:
                # Fallback for non-lazy dataclasses
                resolved_value = getattr(dataclass_type(), field_name, None)

        # Format output
        if resolved_value is None:
            value_text = LazyDefaultPlaceholderService.NONE_VALUE_TEXT
        elif hasattr(resolved_value, '__dataclass_fields__'):
            # CRITICAL FIX: When resolved value is a dataclass, use composition-aware resolution
            # to extract the specific field at arbitrary nesting levels
            specific_field_value = _resolve_field_with_composition_awareness(resolved_value, field_name)
            if specific_field_value is not None:
                # Successfully extracted the specific field value
                value_text = str(specific_field_value)
            elif LazyDefaultPlaceholderService.has_lazy_resolution(type(resolved_value)):
                return LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                    type(resolved_value), field_name, app_config, force_static_defaults, prefix)
            else:
                value_text = LazyDefaultPlaceholderService._format_nested_dataclass_summary(resolved_value)
        else:
            # Apply proper formatting for different value types
            if hasattr(resolved_value, 'value') and hasattr(resolved_value, 'name'):  # Enum
                from openhcs.ui.shared.ui_utils import format_enum_display
                value_text = format_enum_display(resolved_value)
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
    def _get_base_class_from_lazy(lazy_class: Type) -> Type:
        """
        Extract the base class from a lazy dataclass using type registry.
        """
        # First check the type registry
        base_type = get_base_type_for_lazy(lazy_class)
        if base_type:
            return base_type

        # Check if the lazy class has a to_base_config method
        if hasattr(lazy_class, 'to_base_config'):
            # Create a dummy instance to inspect the to_base_config method
            dummy_instance = lazy_class()
            base_instance = dummy_instance.to_base_config()
            return type(base_instance)

        # If no mapping found, raise an error - this indicates missing registration
        raise ValueError(
            f"No base type registered for lazy class {lazy_class.__name__}. "
            f"Use register_lazy_type_mapping() to register the mapping."
        )

    @staticmethod
    def _format_nested_dataclass_summary(dataclass_instance) -> str:
        """
        Format nested dataclass with all field values for user-friendly placeholders.

        Uses generic dataclass introspection to show all fields with their current values,
        providing a complete and maintainable summary without hardcoded field mappings.
        """
        import dataclasses

        class_name = dataclass_instance.__class__.__name__

        # Get all fields from the dataclass using introspection
        all_fields = [f.name for f in dataclasses.fields(dataclass_instance)]

        # Extract all field values
        field_summaries = []
        for field_name in all_fields:
            try:
                value = getattr(dataclass_instance, field_name)

                # Skip None values to keep summary concise
                if value is None:
                    continue

                # Format different value types appropriately
                if hasattr(value, 'value') and hasattr(value, 'name'):  # Enum
                    from openhcs.ui.shared.ui_utils import format_enum_display
                    formatted_value = format_enum_display(value)
                elif isinstance(value, str) and len(value) > 20:  # Long strings
                    formatted_value = f"{value[:17]}..."
                elif dataclasses.is_dataclass(value):  # Nested dataclass
                    formatted_value = f"{value.__class__.__name__}(...)"
                else:
                    formatted_value = str(value)

                field_summaries.append(f"{field_name}={formatted_value}")

            except (AttributeError, Exception):
                # Skip fields that can't be accessed
                continue

        if field_summaries:
            return ", ".join(field_summaries)
        else:
            # Fallback when no non-None fields are found
            return f"{class_name} (default settings)"