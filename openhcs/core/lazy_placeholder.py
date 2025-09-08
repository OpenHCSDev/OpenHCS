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
from openhcs.core.lazy_config import FieldPathNavigator
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


def _resolve_field_with_mro_awareness(global_config, target_dataclass_type, field_name: str):
    """
    Resolve field using LAZY-FIRST resolution order.

    For lazy dataclasses, the resolution order is:
    1. Check lazy dataclass instances for concrete values (highest MRO precedence first)
    2. Follow the lazy resolution chain through the context
    3. Only fall back to static defaults if no concrete values found
    """
    from openhcs.core.field_path_detection import FieldPathDetector
    from openhcs.core.lazy_config import get_base_type_for_lazy, FieldPathNavigator

    if not global_config:
        return None

    # Get the base class if this is a lazy type
    base_class = get_base_type_for_lazy(target_dataclass_type)
    if not base_class:
        base_class = target_dataclass_type

    # Block inheritance if target class has concrete static default
    if _has_concrete_field_override(base_class, field_name):
        # CRITICAL FIX: Use class attribute directly, not dataclass field default
        # The @global_pipeline_config decorator modifies field defaults to None
        # but preserves the original concrete value as a class attribute
        concrete_value = getattr(base_class, field_name)
        if field_name == "well_filter":
            print(f"🔍 CONCRETE OVERRIDE: {base_class.__name__}.{field_name} = {concrete_value} (blocking inheritance)")
        return concrete_value

    # DEBUG: Show what context we're using for resolution
    if field_name == "well_filter":
        print(f"🔍 LAZY RESOLUTION DEBUG: Resolving {base_class.__name__}.{field_name}")
        if hasattr(global_config, 'step_well_filter_config'):
            step_config = global_config.step_well_filter_config
            print(f"🔍 LAZY RESOLUTION DEBUG: Context has step_well_filter_config.well_filter = '{step_config.well_filter}'")

    # STEP 1: Check lazy dataclass instances for concrete values (MRO order)
    # CRITICAL FIX: Include target class if it has concrete override, exclude if inherit-as-none
    if _has_concrete_field_override(base_class, field_name):
        # Concrete override classes should use their own values, not inherit
        mro_types = [base_class] + [cls for cls in base_class.__mro__[1:] if hasattr(cls, '__dataclass_fields__') and field_name in cls.__dataclass_fields__]
    else:
        # Inherit-as-none classes should inherit from parents, not use their own static defaults
        mro_types = [cls for cls in base_class.__mro__[1:] if hasattr(cls, '__dataclass_fields__') and field_name in cls.__dataclass_fields__]

    # CRITICAL FIX: Collect ALL concrete values first, then apply subclass precedence
    concrete_values = []  # List of (value, source_class, field_path, config_instance)

    for mro_class in mro_types:
        field_paths = FieldPathDetector.find_all_field_paths_unified(type(global_config), mro_class)

        for field_path in field_paths:
            config_instance = FieldPathNavigator.navigate_to_instance(global_config, field_path)
            if config_instance and hasattr(config_instance, field_name):
                value = getattr(config_instance, field_name)
                # CRITICAL FIX: Only treat as concrete if value is not None AND class has concrete override
                # This prevents inherit-as-none classes from contributing None values that block inheritance
                if value is not None and _has_concrete_field_override(mro_class, field_name):
                    concrete_values.append((value, mro_class, field_path, config_instance))
                elif value is not None and not _has_concrete_field_override(mro_class, field_name):
                    # This is a user-set value in an inherit-as-none class - also concrete
                    concrete_values.append((value, mro_class, field_path, config_instance))
                elif value is None and _has_concrete_field_override(mro_class, field_name) and mro_class == base_class:
                    # SPECIAL CASE: When target class field is reset to None but has concrete override,
                    # use the class default instead of looking for inheritance
                    class_default = getattr(mro_class, field_name)
                    if field_name == "well_filter":
                        print(f"🔍 RESET TO CLASS DEFAULT: {mro_class.__name__}.{field_name} reset to None, using class default '{class_default}'")
                    return class_default

    # GENERIC SUBCLASS PRECEDENCE: Filter out parent class values when subclass has concrete value
    if len(concrete_values) > 1:
        filtered_values = _apply_subclass_precedence(concrete_values, field_name)
        if filtered_values:
            value, source_class, field_path, _ = filtered_values[0]
            return value
    elif len(concrete_values) == 1:
        value, source_class, field_path, _ = concrete_values[0]
        return value

    # STEP 2: If no concrete values found, create lazy instance and let it resolve
    try:
        temp_instance = target_dataclass_type()
        if hasattr(temp_instance, '_resolve_field_value'):
            resolved_value = temp_instance._resolve_field_value(field_name)
            return resolved_value
        else:
            # Final fallback to getattr
            resolved_value = getattr(temp_instance, field_name)
            return resolved_value
    except Exception as e:
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
                # CRITICAL FIX: Use MRO-aware resolution instead of composition-only search
                # This ensures we respect inheritance precedence when searching the context
                current_app_config = get_current_global_config(GlobalPipelineConfig)

                # SIMPLIFIED: Use LAZY-FIRST resolution only for consistency
                resolved_value = _resolve_field_with_mro_awareness(current_app_config, dataclass_type, field_name)



                # If not found via LAZY-FIRST, fall back to lazy resolution (no composition search)
                if resolved_value is None and hasattr(dataclass_type, '_resolve_field_value'):
                    temp_instance = dataclass_type()
                    resolved_value = _resolve_field_with_mro_awareness(temp_instance, dataclass_type, field_name)
                elif resolved_value is None:
                    # Final fallback: create instance and use getattr
                    resolved_value = getattr(dataclass_type(), field_name)
            finally:
                set_current_global_config(GlobalPipelineConfig, current_context)
        else:
            # Default: Use current thread-local context with actual lazy resolution
            if hasattr(dataclass_type, '_resolve_field_value'):
                # UNIFIED: Use MRO-aware resolution to respect concrete overrides
                current_app_config = get_current_global_config(GlobalPipelineConfig)
                resolved_value = _resolve_field_with_mro_awareness(current_app_config, dataclass_type, field_name)
            else:
                # Fallback for non-lazy dataclasses
                resolved_value = getattr(dataclass_type(), field_name, None)

        # Format output
        if resolved_value is None:
            value_text = LazyDefaultPlaceholderService.NONE_VALUE_TEXT
        elif hasattr(resolved_value, '__dataclass_fields__'):
            # UNIFIED: When resolved value is a dataclass, use MRO-aware resolution
            # to extract the specific field respecting concrete overrides
            current_app_config = get_current_global_config(GlobalPipelineConfig)
            specific_field_value = _resolve_field_with_mro_awareness(current_app_config, type(resolved_value), field_name)
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