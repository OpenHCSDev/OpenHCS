"""
Shared utility for updating forms from code editor changes.

This module provides utilities for parsing edited code and updating form managers
with only the explicitly set fields, preserving None values for unspecified fields.
"""

import re
import logging
from dataclasses import fields, is_dataclass
from typing import Set, Any

logger = logging.getLogger(__name__)


class CodeEditorFormUpdater:
    """Utility for updating forms from code editor changes."""

    @staticmethod
    def extract_explicitly_set_fields(code: str, class_name: str, variable_name: str = 'config') -> Set[str]:
        """
        Parse code to extract which fields were explicitly set.

        Args:
            code: The Python code string
            class_name: The class name to look for (e.g., 'PipelineConfig', 'FunctionStep')
            variable_name: The variable name to look for (default: 'config')

        Returns:
            Set of field names that appear in the constructor call.
            For nested fields, includes both parent and child field names.

        Example:
            code = '''
            config = PipelineConfig(
                well_filter_config=LazyWellFilterConfig(
                    well_filter=2
                )
            )
            '''
            Returns: {'well_filter_config', 'well_filter'}
        """
        # Find the variable = ClassName(...) pattern
        # Match the class name and capture everything inside parentheses
        pattern = rf'{variable_name}\s*=\s*{class_name}\s*\((.*?)\)\s*$'
        match = re.search(pattern, code, re.DOTALL | re.MULTILINE)

        if not match:
            return set()

        constructor_args = match.group(1)

        # Extract field names (simple pattern: field_name=...)
        # This handles both simple fields and nested dataclass fields
        field_pattern = r'(\w+)\s*='
        fields_found = set(re.findall(field_pattern, constructor_args))

        logger.debug(f"Explicitly set fields from code: {fields_found}")
        return fields_found

    @staticmethod
    def update_form_from_dataclass(form_manager, new_instance: Any, explicitly_set_fields: Set[str],
                                   broadcast_callback=None):
        """
        Update form manager with values from a new dataclass instance.

        Only updates fields that were explicitly set in the code editor,
        preserving None values for fields not mentioned.

        Args:
            form_manager: ParameterFormManager instance
            new_instance: New dataclass instance with updated values
            explicitly_set_fields: Set of field names that were explicitly set in code
            broadcast_callback: Optional callback to broadcast changes (e.g., to event bus)
        """
        # Only update fields that were explicitly set in the code
        # This preserves None values for fields not mentioned in the code
        for field in fields(new_instance):
            if field.name in explicitly_set_fields:
                new_value = getattr(new_instance, field.name)
                if field.name in form_manager.parameters:
                    # For nested dataclasses, recursively update nested fields
                    if is_dataclass(new_value) and not isinstance(new_value, type):
                        CodeEditorFormUpdater._update_nested_dataclass(
                            form_manager, field.name, new_value, explicitly_set_fields
                        )
                    else:
                        form_manager.update_parameter(field.name, new_value)

        # CRITICAL: Refresh placeholders with live context AND emit signal for cross-window updates
        # Code editor saves should trigger cross-window refreshes just like form edits
        form_manager._refresh_with_live_context()
        # CRITICAL: Emit context_refreshed signal to notify other open windows
        # This ensures Step editors, PipelineConfig editors, etc. see the code editor changes
        form_manager.context_refreshed.emit(form_manager.object_instance, form_manager.context_obj)

        # CRITICAL: Broadcast to event bus if callback provided
        # This is the OpenHCS "set and forget" pattern - one broadcast reaches everyone
        if broadcast_callback:
            broadcast_callback(new_instance)

    @staticmethod
    def _update_nested_dataclass(form_manager, field_name: str, new_value: Any, explicitly_set_fields: Set[str]):
        """
        Recursively update a nested dataclass field and all its children.

        Args:
            form_manager: ParameterFormManager instance
            field_name: Name of the nested dataclass field
            new_value: New dataclass instance
            explicitly_set_fields: Set of field names that were explicitly set in code
        """
        # Update the parent field first
        form_manager.update_parameter(field_name, new_value)

        # Get the nested manager for this field
        nested_manager = form_manager.nested_managers.get(field_name)
        if nested_manager:
            # Update each field in the nested manager
            # CRITICAL: Only update fields that were explicitly set in the code
            for field in fields(new_value):
                # Check if this nested field was explicitly set
                if field.name in explicitly_set_fields:
                    nested_field_value = getattr(new_value, field.name)
                    if field.name in nested_manager.parameters:
                        # Recursively handle nested dataclasses
                        if is_dataclass(nested_field_value) and not isinstance(nested_field_value, type):
                            CodeEditorFormUpdater._update_nested_dataclass_in_manager(
                                nested_manager, field.name, nested_field_value, explicitly_set_fields
                            )
                        else:
                            nested_manager.update_parameter(field.name, nested_field_value)

    @staticmethod
    def _update_nested_dataclass_in_manager(manager, field_name: str, new_value: Any, explicitly_set_fields: Set[str]):
        """
        Helper to update nested dataclass within a specific manager.

        Args:
            manager: Nested ParameterFormManager instance
            field_name: Name of the nested dataclass field
            new_value: New dataclass instance
            explicitly_set_fields: Set of field names that were explicitly set in code
        """
        manager.update_parameter(field_name, new_value)

        nested_manager = manager.nested_managers.get(field_name)
        if nested_manager:
            # CRITICAL: Only update fields that were explicitly set in the code
            for field in fields(new_value):
                # Check if this nested field was explicitly set
                if field.name in explicitly_set_fields:
                    nested_field_value = getattr(new_value, field.name)
                    if field.name in nested_manager.parameters:
                        if is_dataclass(nested_field_value) and not isinstance(nested_field_value, type):
                            CodeEditorFormUpdater._update_nested_dataclass_in_manager(
                                nested_manager, field.name, nested_field_value, explicitly_set_fields
                            )
                        else:
                            nested_manager.update_parameter(field.name, nested_field_value)

