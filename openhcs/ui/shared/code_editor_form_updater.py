"""
Shared utility for updating forms from code editor changes.

This module provides utilities for parsing edited code and updating form managers
with only the explicitly set fields, preserving None values for unspecified fields.
"""

import inspect
import logging
import re
from contextlib import contextmanager
from dataclasses import fields, is_dataclass
from typing import Any, Set, get_origin, get_args

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
        pattern = rf'{variable_name}\s*=\s*{class_name}\s*\((.*?)\)\s*$'
        match = re.search(pattern, code, re.DOTALL | re.MULTILINE)

        if not match:
            return set()

        constructor_args = match.group(1)
        field_pattern = r'(\w+)\s*='
        fields_found = set(re.findall(field_pattern, constructor_args))

        logger.debug(f"Explicitly set fields from code: {fields_found}")
        return fields_found

    @staticmethod
    def update_form_from_instance(form_manager, new_instance: Any, explicitly_set_fields: Set[str],
                                  broadcast_callback=None):
        """
        Update a form manager with values from a new instance (dataclass or regular object).

        Only updates fields that were explicitly set in the code editor,
        preserving None values for fields not mentioned.

        Args:
            form_manager: ParameterFormManager instance
            new_instance: New object/dataclass instance with updated values
            explicitly_set_fields: Set of field names explicitly set in code
            broadcast_callback: Optional callback to broadcast changes (e.g., to event bus)
        """
        explicitly_set_fields = set(explicitly_set_fields or [])

        is_instance_dataclass = is_dataclass(new_instance)
        if is_instance_dataclass:
            instance_fields = [field.name for field in fields(new_instance)]
        else:
            instance_fields = list(form_manager.parameters.keys())

        for field_name in instance_fields:

            if field_name not in explicitly_set_fields:
                logger.info("CodeEditorFormUpdater: skipping %s (not explicitly set)", field_name)
                continue

            if field_name not in form_manager.parameters:
                logger.info(
                    "CodeEditorFormUpdater: field %s missing from form_manager %s",
                    field_name,
                    getattr(form_manager, 'field_id', '<unknown>')
                )
                continue

            if is_instance_dataclass:
                new_value = CodeEditorFormUpdater._get_raw_field_value(new_instance, field_name)
            else:
                new_value = getattr(new_instance, field_name, None)

            if is_dataclass(new_value) and not isinstance(new_value, type):
                CodeEditorFormUpdater._update_nested_dataclass(
                    form_manager, field_name, new_value, explicitly_set_fields
                )
            else:
                logger.info("CodeEditorFormUpdater: updating %s to %r", field_name, new_value)
                form_manager.update_parameter(field_name, new_value)

        form_manager._refresh_with_live_context()
        form_manager.context_refreshed.emit(form_manager.object_instance, form_manager.context_obj)

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
            explicitly_set_fields: Set of field names explicitly set in code
        """
        nested_manager = form_manager.nested_managers.get(field_name)
        if not nested_manager:
            form_manager.update_parameter(field_name, new_value)
            return

        form_manager._store_parameter_value(field_name, new_value)
        if hasattr(form_manager, '_user_set_fields'):
            form_manager._user_set_fields.add(field_name)

        for field in fields(new_value):
            if field.name not in explicitly_set_fields:
                continue

            nested_field_value = CodeEditorFormUpdater._get_raw_field_value(new_value, field.name)
            if field.name not in nested_manager.parameters:
                continue

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
            explicitly_set_fields: Set of field names explicitly set in code
        """
        nested_manager = manager.nested_managers.get(field_name)
        if not nested_manager:
            manager.update_parameter(field_name, new_value)
            return

        manager._store_parameter_value(field_name, new_value)
        if hasattr(manager, '_user_set_fields'):
            manager._user_set_fields.add(field_name)

        for field in fields(new_value):
            if field.name not in explicitly_set_fields:
                continue

            nested_field_value = CodeEditorFormUpdater._get_raw_field_value(new_value, field.name)
            if field.name not in nested_manager.parameters:
                continue

            if is_dataclass(nested_field_value) and not isinstance(nested_field_value, type):
                CodeEditorFormUpdater._update_nested_dataclass_in_manager(
                    nested_manager, field.name, nested_field_value, explicitly_set_fields
                )
            else:
                nested_manager.update_parameter(field.name, nested_field_value)

    @staticmethod
    @contextmanager
    def patch_lazy_constructors():
        """
        Context manager that patches lazy dataclass constructors.

        Ensures exec()-created instances only set explicitly provided kwargs,
        allowing unspecified fields to remain None.
        """
        from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
        import openhcs.core.config as config_module

        original_constructors = {}
        lazy_types = []

        for _name, obj in inspect.getmembers(config_module):
            if inspect.isclass(obj) and LazyDefaultPlaceholderService.has_lazy_resolution(obj):
                if not is_dataclass(obj):
                    continue
                lazy_types.append(obj)

        for lazy_type in lazy_types:
            original_constructors[lazy_type] = lazy_type.__init__

            def create_patched_init(original_init, dataclass_type):
                def patched_init(self, **kwargs):
                    for field in fields(dataclass_type):
                        value = kwargs.get(field.name, None)
                        object.__setattr__(self, field.name, value)

                    if hasattr(dataclass_type, '_is_lazy_dataclass'):
                        object.__setattr__(self, '_is_lazy_dataclass', True)

                return patched_init

            lazy_type.__init__ = create_patched_init(original_constructors[lazy_type], lazy_type)

        try:
            yield
        finally:
            for lazy_type, original_init in original_constructors.items():
                lazy_type.__init__ = original_init

    @staticmethod
    def _get_raw_field_value(obj: Any, field_name: str):
        """Fetch field without triggering lazy __getattr__ logic."""
        try:
            return object.__getattribute__(obj, field_name)
        except AttributeError:
            return getattr(obj, field_name, None)

    @staticmethod
    def _is_dataclass_type(field_type: Any) -> bool:
        """Check if a field type represents (or wraps) a dataclass."""
        origin = get_origin(field_type)
        if origin is not None:
            return any(
                CodeEditorFormUpdater._is_dataclass_type(arg)
                for arg in get_args(field_type)
                if arg is not type(None)
            )
        try:
            return is_dataclass(field_type)
        except TypeError:
            return False

    @staticmethod
    def _get_dataclass_field_value(instance: Any, field_obj) -> Any:
        """
        Get a field value from a dataclass, preserving raw None for nested dataclasses
        while allowing primitive fields to resolve normally.
        """
        if CodeEditorFormUpdater._is_dataclass_type(field_obj.type):
            return CodeEditorFormUpdater._get_raw_field_value(instance, field_obj.name)
        return getattr(instance, field_obj.name, None)
