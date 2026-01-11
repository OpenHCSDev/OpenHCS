"""
Shared service layer for parameter form managers.

This module provides a framework-agnostic service layer that eliminates the
architectural dependency between PyQt and Textual implementations by providing
shared business logic and data management.

Uses React-style discriminated unions for type-safe parameter handling.
"""

import dataclasses
from dataclasses import dataclass
from typing import Dict, Any, Type, Optional, List, Tuple

from objectstate import LazyDefaultPlaceholderService
# Old field path detection removed - using simple field name matching
from pyqt_formgen.forms.parameter_form_constants import CONSTANTS
from .parameter_type_utils import ParameterTypeUtils
from pyqt_formgen.forms.ui_utils import debug_param, format_param_name
from .parameter_info_types import (
    ParameterInfo,
    create_parameter_info
)


@dataclass
class ParameterAnalysisInput:
    """
    Type-safe input for parameter analysis.

    Field names match UnifiedParameterInfo for automatic extraction.
    This enforces unification across all functions that analyze parameters.
    """
    default_value: Dict[str, Any]
    param_type: Dict[str, Type]
    field_id: str
    description: Optional[Dict[str, str]] = None
    parent_obj_type: Optional[Type] = None


@dataclass
class FormStructure:
    """
    Structure information for a parameter form.

    Uses discriminated union ParameterInfo types for type-safe dispatch.

    Attributes:
        field_id: Unique identifier for the form
        parameters: List of parameter information (discriminated union types)
        nested_forms: Dictionary of nested form structures
        has_optional_dataclasses: Whether form has optional dataclass parameters
    """
    field_id: str
    parameters: List[ParameterInfo]
    nested_forms: Dict[str, 'FormStructure']
    has_optional_dataclasses: bool = False

    def get_parameter_info(self, param_name: str) -> ParameterInfo:
        """
        Get ParameterInfo for a parameter by name.

        Args:
            param_name: Name of the parameter

        Returns:
            ParameterInfo instance (discriminated union type)

        Raises:
            KeyError: If parameter not found
        """
        for param_info in self.parameters:
            if param_info.name == param_name:
                return param_info
        raise KeyError(f"Parameter '{param_name}' not found in form structure")


class ParameterFormService:
    """
    Framework-agnostic service for parameter form business logic.
    
    This service provides shared functionality for both PyQt and Textual
    parameter form managers, eliminating the need for cross-framework
    dependencies and providing a clean separation of concerns.
    """
    
    def __init__(self):
        """
        Initialize the parameter form service.
        """
        self._type_utils = ParameterTypeUtils()
    
    def analyze_parameters(self, input: ParameterAnalysisInput) -> FormStructure:
        """
        Analyze parameters and create form structure.

        This method analyzes the parameters and their types to create a complete
        form structure that can be used by any UI framework.

        Args:
            input: Type-safe parameter analysis input (field names match UnifiedParameterInfo)

        Returns:
            Complete form structure information
        """
        debug_param("analyze_parameters", f"field_id={input.field_id}, parameter_count={len(input.default_value)}")

        param_infos = []
        nested_forms = {}
        has_optional_dataclasses = False

        for param_name, parameter_type in input.param_type.items():
            current_value = input.default_value.get(param_name)

            # Check if this parameter should be hidden from UI
            if self._should_hide_from_ui(input.parent_obj_type, param_name, parameter_type):
                debug_param("analyze_parameters", f"Hiding parameter {param_name} from UI (ui_hidden=True)")
                continue

            # Create parameter info
            param_info = self._create_parameter_info(
                param_name, parameter_type, current_value, input.description
            )
            param_infos.append(param_info)

            # Check for nested dataclasses using isinstance (type-safe!)
            from .parameter_info_types import OptionalDataclassInfo, DirectDataclassInfo

            if isinstance(param_info, (OptionalDataclassInfo, DirectDataclassInfo)):
                # Get actual field path from FieldPathDetector (no artificial "nested_" prefix)
                # Unwrap Optional types to get the actual dataclass type for field path detection
                unwrapped_param_type = self._type_utils.get_optional_inner_type(parameter_type) if self._type_utils.is_optional_dataclass(parameter_type) else parameter_type

                # For function parameters (no parent dataclass), use parameter name directly
                if input.parent_obj_type is None:
                    nested_field_id = param_name
                else:
                    nested_field_id = self.get_field_path_with_fail_loud(input.parent_obj_type, unwrapped_param_type)

                nested_structure = self._analyze_nested_dataclass(
                    param_name, parameter_type, current_value, nested_field_id, input.parent_obj_type
                )
                nested_forms[param_name] = nested_structure

            # Check for optional dataclasses using isinstance (type-safe!)
            if isinstance(param_info, OptionalDataclassInfo):
                has_optional_dataclasses = True

        return FormStructure(
            field_id=input.field_id,
            parameters=param_infos,
            nested_forms=nested_forms,
            has_optional_dataclasses=has_optional_dataclasses
        )

    def _should_hide_from_ui(self, parent_obj_type: Optional[Type], param_name: str, param_type: Type) -> bool:
        """
        Check if a parameter should be hidden from the UI.

        Args:
            parent_obj_type: The parent dataclass type (None for function parameters)
            param_name: Name of the parameter
            param_type: Type of the parameter

        Returns:
            True if the parameter should be hidden from UI
        """
        import dataclasses

        # Check if parent class declares this field as having a special editor
        # (e.g., FunctionStep._ui_special_fields = ('func',) - rendered as FunctionPatternEditor)
        if parent_obj_type is not None:
            special_fields = getattr(parent_obj_type, '_ui_special_fields', ())
            if param_name in special_fields:
                return True

        # If no parent dataclass, can't check field metadata
        if parent_obj_type is None:
            # Still check if the type itself has _ui_hidden
            unwrapped_type = self._type_utils.get_optional_inner_type(param_type) if self._type_utils.is_optional_dataclass(param_type) else param_type
            if hasattr(unwrapped_type, '__dict__') and '_ui_hidden' in unwrapped_type.__dict__ and unwrapped_type._ui_hidden:
                return True
            return False

        # Check field metadata for ui_hidden flag
        try:
            field_obj = next(f for f in dataclasses.fields(parent_obj_type) if f.name == param_name)
            if field_obj.metadata.get('ui_hidden', False):
                return True
        except (StopIteration, TypeError, AttributeError):
            pass

        # Check if type itself has _ui_hidden attribute
        # IMPORTANT: Check __dict__ directly to avoid inheriting _ui_hidden from parent classes
        unwrapped_type = self._type_utils.get_optional_inner_type(param_type) if self._type_utils.is_optional_dataclass(param_type) else param_type
        if hasattr(unwrapped_type, '__dict__') and '_ui_hidden' in unwrapped_type.__dict__ and unwrapped_type._ui_hidden:
            return True

        return False

    def convert_value_to_type(self, value: Any, param_type: Type, param_name: str, obj_type: Type = None) -> Any:
        """
        Convert a value to the appropriate type for a parameter.

        This method provides centralized type conversion logic that can be
        used by any UI framework.

        Args:
            value: The value to convert
            param_type: The target parameter type
            param_name: The parameter name (for debugging)
            obj_type: The dataclass type (for sibling inheritance checks)

        Returns:
            The converted value
        """
        debug_param("convert_value", f"param={param_name}, input_type={type(value).__name__}, target_type={param_type.__name__ if hasattr(param_type, '__name__') else str(param_type)}")

        if value is None:
            return None

        # Handle string "None" literal
        if isinstance(value, str) and value == CONSTANTS.NONE_STRING_LITERAL:
            return None

        # Handle enum types
        if self._type_utils.is_enum_type(param_type):
            return param_type(value)

        # Handle list of enums
        if self._type_utils.is_list_of_enums(param_type):
            # If value is already a list (from checkbox group widget), return as-is
            if isinstance(value, list):
                return value
            enum_type = self._type_utils.get_enum_from_list_type(param_type)
            if enum_type:
                return [enum_type(value)]

        # Handle Union types (e.g., Union[List[str], str, int])
        # Try to convert to the most specific type that matches
        from typing import get_origin, get_args, Union
        if get_origin(param_type) is Union:
            union_args = get_args(param_type)
            # Filter out NoneType
            non_none_types = [t for t in union_args if t is not type(None)]

            # If value is a string, try to convert to int first, then keep as str
            if isinstance(value, str) and value != CONSTANTS.EMPTY_STRING:
                # Try int conversion first
                if int in non_none_types:
                    try:
                        return int(value)
                    except (ValueError, TypeError):
                        pass
                # Try float conversion
                if float in non_none_types:
                    try:
                        return float(value)
                    except (ValueError, TypeError):
                        pass
                # Keep as string if str is in the union
                if str in non_none_types:
                    return value

        # Handle basic types
        if param_type == bool and isinstance(value, str):
            return self._type_utils.convert_string_to_bool(value)
        if param_type in (int, float) and isinstance(value, str):
            if value == CONSTANTS.EMPTY_STRING:
                return None
            try:
                return param_type(value)
            except (ValueError, TypeError):
                return None

        # Handle empty strings in lazy context - convert to None for all parameter types
        # This is critical for lazy dataclass behavior where None triggers placeholder resolution
        if isinstance(value, str) and value == CONSTANTS.EMPTY_STRING:
            return None

        # Handle string types - also convert empty strings to None for consistency
        if param_type == str and isinstance(value, str) and value == CONSTANTS.EMPTY_STRING:
            return None

        # Handle sibling-inheritable fields - allow None even for non-Optional types
        if value is None and obj_type is not None:
            if is_field_sibling_inheritable(obj_type, param_name):
                return None

        return value

    def get_parameter_display_info(self, param_name: str, param_type: Type,
                                 description: Optional[str] = None) -> Dict[str, str]:
        """
        Get display information for a parameter.
        
        Args:
            param_name: The parameter name
            param_type: The parameter type
            description: Optional parameter description
            
        Returns:
            Dictionary with display information
        """
        return {
            'display_name': format_param_name(param_name),
            'field_label': f"{format_param_name(param_name)}:",
            'checkbox_label': f"Enable {format_param_name(param_name)}",
            'group_title': format_param_name(param_name),
            'description': description or f"Parameter: {format_param_name(param_name)}",
            'tooltip': f"{format_param_name(param_name)} ({param_type.__name__ if hasattr(param_type, '__name__') else str(param_type)})"
        }
    
    def format_widget_name(self, field_path: str, param_name: str) -> str:
        """Convert field path to widget name - replaces generate_field_ids() complexity"""
        return f"{field_path}_{param_name}"

    def get_field_path_with_fail_loud(self, parent_type: Type, param_type: Type) -> str:
        """Get field path using simple field name matching."""
        import dataclasses

        # Simple approach: find field by type matching
        if dataclasses.is_dataclass(parent_type):
            for field in dataclasses.fields(parent_type):
                if field.type == param_type:
                    return field.name

        # Fallback: use class name as field name (common pattern)
        field_name = param_type.__name__.lower().replace('config', '')
        return field_name

    def generate_field_ids_direct(self, base_field_id: str, param_name: str) -> Dict[str, str]:
        """Generate field IDs directly without artificial complexity."""
        widget_id = f"{base_field_id}_{param_name}"
        return {
            'widget_id': widget_id,
            'reset_button_id': f"reset_{widget_id}",
            'optional_checkbox_id': f"{base_field_id}_{param_name}_enabled"
        }

    def validate_field_path_mapping(self):
        """Ensure all form field_ids map correctly to context fields"""
        import dataclasses

        # Get all dataclass fields from GlobalPipelineConfig
        context_fields = {f.name for f in dataclasses.fields(GlobalPipelineConfig)
                         if dataclasses.is_dataclass(f.type)}

        print("Context fields:", context_fields)
        # Should include: well_filter_config, zarr_config, step_materialization_config, etc.

        # Verify form managers use these exact field names (no "nested_" prefix)
        assert "well_filter_config" in context_fields
        assert "nested_well_filter_config" not in context_fields  # Should not exist

        return True
    
    def should_use_concrete_values(self, current_value: Any, is_global_editing: bool = False) -> bool:
        """
        Determine whether to use concrete values for a dataclass parameter.
        
        Args:
            current_value: The current parameter value
            is_global_editing: Whether in global configuration editing mode
            
        Returns:
            True if concrete values should be used
        """
        if current_value is None:
            return False
        
        if is_global_editing:
            return True
        
        # If current_value is a concrete dataclass instance, use its values
        if self._type_utils.is_concrete_dataclass(current_value):
            return True
        
        # For lazy dataclasses, return True so we can extract raw values from them
        if self._type_utils.is_lazy_dataclass(current_value):
            return True
        
        return False
    
    def extract_nested_parameters(self, dataclass_instance: Any, obj_type: Type,
                                parent_obj_type: Optional[Type] = None) -> Tuple[Dict[str, Any], Dict[str, Type]]:
        """
        Extract parameters and types from a dataclass instance.

        This method always preserves concrete field values when a dataclass instance exists,
        regardless of parent context. Placeholder behavior is handled at the widget level,
        not by discarding concrete values during parameter extraction.
        """
        if not dataclasses.is_dataclass(obj_type):
            return {}, {}

        parameters = {}
        parameter_types = {}

        for field in dataclasses.fields(obj_type):
            # Always extract actual field values when dataclass instance exists
            # This preserves concrete user-entered values in nested lazy dataclass forms
            if dataclass_instance is not None:
                current_value = self._get_field_value(dataclass_instance, field)
            else:
                current_value = None  # Only use None when no instance exists

            parameters[field.name] = current_value
            parameter_types[field.name] = field.type

        return parameters, parameter_types



    def _get_field_value(self, dataclass_instance: Any, field: Any) -> Any:
        """Extract a single field value from a dataclass instance."""
        if dataclass_instance is None:
            return field.default

        field_name = field.name

        if self._type_utils.has_resolve_field_value(dataclass_instance):
            # Lazy dataclass - get raw value
            return object.__getattribute__(dataclass_instance, field_name) if hasattr(dataclass_instance, field_name) else field.default
        else:
            # Concrete dataclass - get attribute value
            return getattr(dataclass_instance, field_name, field.default)

    def _create_parameter_info(self, param_name: str, param_type: Type, current_value: Any,
                             parameter_info: Optional[Dict] = None) -> ParameterInfo:
        """
        Create parameter information object using discriminated union factory.

        Uses type introspection to automatically select the correct ParameterInfo
        subclass (OptionalDataclassInfo, DirectDataclassInfo, or GenericInfo).
        """
        # Get description from parameter info
        description = None
        if parameter_info and param_name in parameter_info:
            info_obj = parameter_info[param_name]
            # CRITICAL FIX: Handle both object-style and string-style parameter info
            if isinstance(info_obj, str):
                # Simple string description
                description = info_obj
            else:
                # Object with description attribute
                description = getattr(info_obj, 'description', None)

        # Use factory to create correct ParameterInfo subclass
        # Factory uses type introspection to determine which type to create
        return create_parameter_info(
            name=param_name,
            param_type=param_type,
            current_value=current_value,
            description=description
        )
    
    # Class-level cache for nested dataclass parameter info (descriptions only)
    _nested_param_info_cache = {}

    def _analyze_nested_dataclass(self, param_name: str, param_type: Type, current_value: Any,
                                nested_field_id: str, parent_obj_type: Type = None) -> FormStructure:
        """Analyze a nested dataclass parameter."""
        # Get the actual dataclass type
        if self._type_utils.is_optional_dataclass(param_type):
            obj_type = self._type_utils.get_optional_inner_type(param_type)
        else:
            obj_type = param_type

        # Extract nested parameters using parent context
        nested_params, nested_types = self.extract_nested_parameters(
            current_value, obj_type, parent_obj_type
        )

        # OPTIMIZATION: Cache parameter info (descriptions) by dataclass type
        # We only need descriptions, not instance values, so analyze the type once and reuse
        cache_key = obj_type
        if cache_key in self._nested_param_info_cache:
            nested_param_info = self._nested_param_info_cache[cache_key]
        else:
            # Recursively analyze nested structure with proper descriptions for nested fields
            # Use existing infrastructure to extract field descriptions for the nested dataclass
            from python_introspect import UnifiedParameterAnalyzer
            # OPTIMIZATION: Always analyze the TYPE, not the instance
            # This allows caching and avoids extracting field values we don't need
            nested_param_info = UnifiedParameterAnalyzer.analyze(obj_type)
            self._nested_param_info_cache[cache_key] = nested_param_info

        # Create type-safe input for recursive analysis
        nested_input = ParameterAnalysisInput(
            default_value=nested_params,
            param_type=nested_types,
            field_id=nested_field_id,
            description={name: info.description for name, info in nested_param_info.items()} if nested_param_info else None,
            parent_obj_type=obj_type
        )

        return self.analyze_parameters(nested_input)

    def get_placeholder_text(self, param_name: str, obj_type: Type,
                           placeholder_prefix: str = "Pipeline default") -> Optional[str]:
        """
        Get placeholder text using existing OpenHCS infrastructure.

        Context must be established by the caller using config_context() before calling this method.
        This allows the caller to build proper context stacks (parent + overlay) for accurate
        placeholder resolution.

        Args:
            param_name: Name of the parameter to get placeholder for
            obj_type: The specific dataclass type (GlobalPipelineConfig or PipelineConfig)
            placeholder_prefix: Prefix for the placeholder text

        Returns:
            Formatted placeholder text or None if no resolution possible

        The editing mode is automatically derived from the dataclass type's lazy resolution capabilities:
        - Has lazy resolution (PipelineConfig) → orchestrator config editing
        - No lazy resolution (GlobalPipelineConfig) → global config editing
        """
        # Service just resolves placeholders, caller manages context
        return LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            obj_type, param_name, placeholder_prefix
        )

    def reset_nested_managers(self, nested_managers: Dict[str, Any],
                            obj_type: Type, current_config: Any) -> None:
        """Reset all nested managers - fail loud, no defensive programming."""
        for nested_manager in nested_managers.values():
            # All nested managers must have reset_all_parameters method
            nested_manager.reset_all_parameters()



    def get_reset_value_for_parameter(self, param_name: str, param_type: Type,
                                    obj_type: Type, is_global_config_editing: Optional[bool] = None) -> Any:
        """
        Get appropriate reset value using existing OpenHCS patterns.

        Args:
            param_name: Name of the parameter to reset
            param_type: Type of the parameter (int, str, bool, etc.)
            obj_type: The specific dataclass type
            is_global_config_editing: Whether we're in global config editing mode (auto-detected if None)

        Returns:
            - For global config editing: Actual default values
            - For lazy config editing: None to show placeholder text
        """
        # Context-driven behavior: Use the editing context to determine reset behavior
        # This follows the architectural principle that behavior is determined by context
        # of usage rather than intrinsic properties of the dataclass.

        # Context-driven behavior: Use explicit context when provided
        # Auto-detect editing mode if not explicitly provided
        if is_global_config_editing is None:
            # Fallback: Use existing lazy resolution detection for backward compatibility
            is_global_config_editing = not LazyDefaultPlaceholderService.has_lazy_resolution(obj_type)

        # Context-driven behavior: Reset behavior depends on editing context
        if is_global_config_editing:
            # Global config editing: Reset to actual default values
            # Users expect to see concrete defaults when editing global configuration
            return self._get_actual_dataclass_field_default(param_name, obj_type)
        else:
            # CRITICAL FIX: For lazy config editing, always return None
            # This ensures reset shows inheritance chain values (like compiler resolution)
            # instead of concrete values from thread-local context
            return None

    def _get_actual_dataclass_field_default(self, param_name: str, obj_type: Type) -> Any:
        """
        Get the actual default value for a parameter.

        Works uniformly for dataclasses, functions, and any other object type.
        Always returns None for non-existent fields (fail-soft for dynamic properties).

        Returns:
        - If class attribute is None → return None (show placeholder)
        - If class attribute has concrete value → return that value
        - If field(default_factory) → call default_factory and return result
        - If field doesn't exist → return None (dynamic property)
        """
        from dataclasses import fields, MISSING, is_dataclass
        import inspect

        # For pure functions: get default from signature
        if callable(obj_type) and not is_dataclass(obj_type) and not hasattr(obj_type, '__mro__'):
            sig = inspect.signature(obj_type)
            if param_name in sig.parameters:
                default = sig.parameters[param_name].default
                return None if default is inspect.Parameter.empty else default
            return None  # Dynamic property, not in signature

        # For all other types (dataclasses, ABCs, classes): check class attribute first
        if hasattr(obj_type, param_name):
            return getattr(obj_type, param_name)

        # For dataclasses: check if it's a field(default_factory=...) field
        if is_dataclass(obj_type):
            dataclass_fields = {f.name: f for f in fields(obj_type)}
            if param_name not in dataclass_fields:
                return None  # Dynamic property, not a dataclass field

            field_info = dataclass_fields[param_name]

            # Handle field(default_factory=...) case
            if field_info.default_factory is not MISSING:
                try:
                    return field_info.default_factory()
                except Exception as e:
                    raise ValueError(f"Failed to call default_factory for field '{param_name}': {e}") from e

            # Handle field with explicit default
            if field_info.default is not MISSING:
                return field_info.default

            # Field has no default (should not happen in practice)
            return None

        # For non-dataclass types: return None (dynamic property)
        return None
