"""
Lazy placeholder service for UI components.

Provides placeholder text resolution for lazy configuration dataclasses.
"""

from typing import Any, Optional, Type
import dataclasses

# Import functions from their new locations after refactoring
from openhcs.core.context.global_config import get_current_global_config, set_current_global_config
from openhcs.core.lazy_config import get_base_type_for_lazy
from openhcs.core.field_path_detection import FieldPathDetector
from openhcs.core.field_path_detection import FieldPathNavigator
from openhcs.core.config import GlobalPipelineConfig


def _has_concrete_field_override(source_class, field_name: str) -> bool:
    """
    Check if a class has a concrete field override (not None).

    This determines inheritance design based on static class definition:
    - Concrete default (not None) = never inherits
    - None default = always inherits (inherit_as_none design)
    """
    # CRITICAL FIX: Check class attribute directly, not dataclass field default
    # The @global_pipeline_config decorator modifies field defaults to None
    # but the class attribute retains the original concrete value
    if hasattr(source_class, field_name):
        class_attr_value = getattr(source_class, field_name)
        has_override = class_attr_value is not None

        # Debug for well_filter field
        if field_name == "well_filter":
            print(f"🔍 OVERRIDE CHECK: {source_class.__name__}.{field_name} class_attr='{class_attr_value}' has_override={has_override}")

        return has_override

    return False


def _apply_subclass_precedence(concrete_values, field_name: str):
    """
    Apply generic subclass precedence to resolve field collisions.

    When multiple classes define the same field, subclasses take precedence
    over their parent classes. This handles cases like:
    - StepWellFilterConfig.well_filter takes precedence over WellFilterConfig.well_filter
    - Any subclass takes precedence over its parent for colliding fields

    Args:
        concrete_values: List of (value, source_class, field_path, config_instance)
        field_name: Name of the field being resolved

    Returns:
        Filtered list with parent class values removed when subclass has concrete value
    """
    if len(concrete_values) <= 1:
        return concrete_values

    debug_field = any(field_name == "well_filter" for value, source_class, field_path, config_instance in concrete_values)
    if debug_field:
        print(f"🔍 DEBUG: Applying subclass precedence for {len(concrete_values)} concrete values")

    # Group by class hierarchy - remove parent values when subclass has concrete value
    classes_with_values = [source_class for _, source_class, _, _ in concrete_values]
    filtered_values = []

    for value, source_class, field_path, config_instance in concrete_values:
        # Check if this class has any subclasses in the list with concrete values
        has_subclass_with_value = any(
            other_class != source_class and issubclass(other_class, source_class)
            for other_class in classes_with_values
        )

        if not has_subclass_with_value:
            # No subclass has a concrete value, so include this one
            filtered_values.append((value, source_class, field_path, config_instance))
            if debug_field:
                print(f"🔍 DEBUG: Including {source_class.__name__}.{field_name} = '{value}' (no subclass override)")
        else:
            if debug_field:
                print(f"🔍 DEBUG: Excluding {source_class.__name__}.{field_name} = '{value}' (subclass takes precedence)")

    return filtered_values







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

    @staticmethod
    def _get_lazy_type_for_base(base_type: type) -> Optional[type]:
        """Get the lazy type for a base dataclass type (reverse lookup)."""
        from openhcs.core.lazy_config import _lazy_type_registry

        # Reverse lookup in the lazy type registry
        for lazy_type, registered_base_type in _lazy_type_registry.items():
            if registered_base_type == base_type:
                return lazy_type
        return None

    NONE_VALUE_TEXT = "(none)"

    @staticmethod
    def _get_regular_dataclass_placeholder(
        dataclass_type: type,
        field_name: str,
        placeholder_prefix: Optional[str] = None
    ) -> Optional[str]:
        """Get placeholder for regular dataclasses - delegate to dual-axis resolver."""
        prefix = placeholder_prefix or LazyDefaultPlaceholderService.PLACEHOLDER_PREFIX

        try:
            # Use recursive dual-axis resolver - it handles everything correctly
            from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver

            resolver = get_recursive_resolver()

            # Create a dummy instance to resolve the field
            dummy_instance = dataclass_type()
            resolved_value = resolver.resolve_field(dummy_instance, field_name)

            if resolved_value is not None:
                return f"{prefix}: {resolved_value}"

            # Fallback to class default
            if hasattr(dataclass_type, field_name):
                class_default = getattr(dataclass_type, field_name)
                if class_default is not None:
                    return f"{prefix}: {class_default}"

            return None
        except Exception:
            return None







    @staticmethod
    def get_lazy_resolved_placeholder(
        dataclass_type: type,
        field_name: str,
        app_config: Optional[Any] = None,
        force_static_defaults: bool = False,
        placeholder_prefix: Optional[str] = None,
        ignore_concrete_override: bool = False,
        orchestrator: Optional[Any] = None
    ) -> Optional[str]:
        """Get placeholder text using the exact same mechanism as the compiler."""
        # Check if this is a lazy dataclass
        is_lazy = LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type)

        # If not lazy, try to find the lazy version of this base type
        if not is_lazy:
            lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(dataclass_type)
            if lazy_type:
                dataclass_type = lazy_type
                is_lazy = True
            else:
                return LazyDefaultPlaceholderService._get_regular_dataclass_placeholder(
                    dataclass_type, field_name, placeholder_prefix
                )

        # Simple fallback: use default prefix
        if placeholder_prefix is None:
            placeholder_prefix = "Default"

        prefix = placeholder_prefix or LazyDefaultPlaceholderService.PLACEHOLDER_PREFIX

        # Simplified: Always use dual-axis resolver for consistent placeholder behavior
        try:
            from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver
            resolver = get_recursive_resolver()

            # Create a dummy instance to resolve the field
            temp_instance = dataclass_type()
            resolved_value = resolver.resolve_field(temp_instance, field_name)
        except Exception:
            resolved_value = None

        return LazyDefaultPlaceholderService._format_placeholder_text(resolved_value, prefix)

    @staticmethod
    def _find_field_in_config(config, target_type: type, field_name: str):
        """
        Find a field value in the effective config by searching for instances of target_type.

        This searches through the config hierarchy to find the appropriate instance
        that contains the field we're looking for.
        """
        import dataclasses

        # Direct field access if config is the target type
        if isinstance(config, target_type):
            return getattr(config, field_name, None)

        # Search through all fields in the config
        if dataclasses.is_dataclass(config):
            for field in dataclasses.fields(config):
                field_value = getattr(config, field.name, None)
                if field_value is None:
                    continue

                # Check if this field is an instance of target_type
                if isinstance(field_value, target_type):
                    return getattr(field_value, field_name, None)

                # Recursively search nested configs
                if dataclasses.is_dataclass(field_value):
                    nested_result = LazyDefaultPlaceholderService._find_field_in_config(
                        field_value, target_type, field_name
                    )
                    if nested_result is not None:
                        return nested_result

        return None

    @staticmethod
    def get_lazy_resolved_placeholder_with_context(
        dataclass_type: type,
        field_name: str,
        temporary_context: Any,
        placeholder_prefix: Optional[str] = None
    ) -> Optional[str]:
        """Get placeholder text using temporary context for live updates."""
        # Check if this is a lazy dataclass
        is_lazy = LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type)
        if not is_lazy:
            return None

        prefix = placeholder_prefix or LazyDefaultPlaceholderService.PLACEHOLDER_PREFIX

        # Create a temporary lazy instance and resolve using the provided context
        try:
            from openhcs.core.dual_axis_resolver_recursive import RecursiveContextualResolver, _get_global_config_type_for_target
            from openhcs.core.context.global_config import get_current_global_config
            from openhcs.core.lazy_config import get_base_type_for_lazy

            # Get the base type for the dataclass
            base_type = get_base_type_for_lazy(dataclass_type) or dataclass_type

            # Create resolver
            resolver = RecursiveContextualResolver()

            # Build context hierarchy with temporary context as most specific
            context_hierarchy = [temporary_context]

            # Add thread-local as fallback
            global_config_type = _get_global_config_type_for_target(base_type)
            if global_config_type:
                thread_local_context = get_current_global_config(global_config_type)
                if thread_local_context and thread_local_context != temporary_context:
                    context_hierarchy.append(thread_local_context)

            # Resolve using the context hierarchy
            resolved_value = resolver._resolve_field_recursive(base_type, field_name, context_hierarchy)
        except Exception:
            resolved_value = None

        return LazyDefaultPlaceholderService._format_placeholder_text(resolved_value, prefix)



    @staticmethod
    def _format_placeholder_text(resolved_value: Any, prefix: str) -> Optional[str]:
        """Format resolved value into placeholder text."""
        # Format output
        if resolved_value is None:
            value_text = LazyDefaultPlaceholderService.NONE_VALUE_TEXT
        elif hasattr(resolved_value, '__dataclass_fields__'):
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