"""
Shared utility for updating forms from code editor changes.

This module provides utilities for parsing edited code and updating form managers
with only the explicitly set fields, preserving None values for unspecified fields.
"""

import logging
from contextlib import contextmanager
from dataclasses import fields, is_dataclass
from typing import Any, get_origin, get_args

logger = logging.getLogger(__name__)


class CodeEditorFormUpdater:
    """Utility for updating forms from code editor changes."""

    # REMOVED: extract_explicitly_set_fields() method
    # No longer needed - raw field values (via object.__getattribute__) are the source of truth
    # Raw None = inherited, Raw concrete = user-set (same pattern as pickle_to_python)

    @staticmethod
    def update_form_from_instance(form_manager, new_instance: Any, broadcast_callback=None):
        """
        Update a form manager with values from a new instance (dataclass or regular object).

        SIMPLIFIED: Updates all fields from the instance. The instance already has raw None
        for unset fields (from patch_lazy_constructors), so the form manager will automatically
        show placeholders for None values and concrete values for user-set fields.

        Args:
            form_manager: ParameterFormManager instance
            new_instance: New object/dataclass instance with updated values
            broadcast_callback: Optional callback to broadcast changes (e.g., to event bus)
        """
        is_instance_dataclass = is_dataclass(new_instance)
        if is_instance_dataclass:
            instance_fields = [field.name for field in fields(new_instance)]
        else:
            instance_fields = list(form_manager.parameters.keys())

        for field_name in instance_fields:
            if field_name not in form_manager.parameters:
                logger.debug(
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
                    form_manager, field_name, new_value
                )
            else:
                logger.debug("CodeEditorFormUpdater: updating %s to %r", field_name, new_value)
                form_manager.update_parameter(field_name, new_value)

        form_manager._refresh_with_live_context()
        form_manager.context_refreshed.emit(form_manager.object_instance, form_manager.context_obj)

        if broadcast_callback:
            broadcast_callback(new_instance)

    @staticmethod
    def _update_nested_dataclass(form_manager, field_name: str, new_value: Any):
        """
        Recursively update a nested dataclass field and all its children.

        SIMPLIFIED: Updates all fields in the nested dataclass. Raw None values
        will show as placeholders, concrete values will show as actual values.

        Args:
            form_manager: ParameterFormManager instance
            field_name: Name of the nested dataclass field
            new_value: New dataclass instance
        """
        nested_manager = form_manager.nested_managers.get(field_name)
        if not nested_manager:
            form_manager.update_parameter(field_name, new_value)
            return

        form_manager._store_parameter_value(field_name, new_value)
        if hasattr(form_manager, '_user_set_fields'):
            form_manager._user_set_fields.add(field_name)

        for field in fields(new_value):
            nested_field_value = CodeEditorFormUpdater._get_raw_field_value(new_value, field.name)
            if field.name not in nested_manager.parameters:
                continue

            if is_dataclass(nested_field_value) and not isinstance(nested_field_value, type):
                CodeEditorFormUpdater._update_nested_dataclass_in_manager(
                    nested_manager, field.name, nested_field_value
                )
            else:
                nested_manager.update_parameter(field.name, nested_field_value)

    @staticmethod
    def _update_nested_dataclass_in_manager(manager, field_name: str, new_value: Any):
        """
        Helper to update nested dataclass within a specific manager.

        SIMPLIFIED: Updates all fields in the nested dataclass. Raw None values
        will show as placeholders, concrete values will show as actual values.

        Args:
            manager: Nested ParameterFormManager instance
            field_name: Name of the nested dataclass field
            new_value: New dataclass instance
        """
        nested_manager = manager.nested_managers.get(field_name)
        if not nested_manager:
            manager.update_parameter(field_name, new_value)
            return

        manager._store_parameter_value(field_name, new_value)
        if hasattr(manager, '_user_set_fields'):
            manager._user_set_fields.add(field_name)

        for field in fields(new_value):
            nested_field_value = CodeEditorFormUpdater._get_raw_field_value(new_value, field.name)
            if field.name not in nested_manager.parameters:
                continue

            if is_dataclass(nested_field_value) and not isinstance(nested_field_value, type):
                CodeEditorFormUpdater._update_nested_dataclass_in_manager(
                    nested_manager, field.name, nested_field_value
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
        from openhcs.introspection import patch_lazy_constructors as _patch_lazy_constructors
        with _patch_lazy_constructors():
            yield

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
