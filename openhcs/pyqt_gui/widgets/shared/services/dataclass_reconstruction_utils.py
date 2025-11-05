"""
Dataclass Reconstruction Utilities

Helper functions for reconstructing nested dataclasses from tuple format.
Extracted from context_layer_builders.py for reuse after tree registry migration.
"""

from typing import Any, Dict
from dataclasses import is_dataclass
import dataclasses


def reconstruct_nested_dataclasses(live_values: dict, base_instance=None) -> dict:
    """
    Reconstruct nested dataclasses from tuple format (type, dict) to instances.

    get_user_modified_values() returns nested dataclasses as (type, dict) tuples
    to preserve only user-modified fields. This function reconstructs them as instances
    by merging the user-modified fields into the base instance's nested dataclasses.

    Args:
        live_values: Dict with values, may contain (type, dict) tuples for nested dataclasses
        base_instance: Base dataclass instance to merge into (for nested dataclass fields)

    Returns:
        Dict with nested dataclasses reconstructed as instances

    Example:
        >>> user_modified = {
        ...     'name': 'test',
        ...     'config': (ConfigClass, {'field1': 'value1'})
        ... }
        >>> reconstructed = reconstruct_nested_dataclasses(user_modified, base)
        >>> # reconstructed['config'] is now a ConfigClass instance
    """
    reconstructed = {}
    for field_name, value in live_values.items():
        if isinstance(value, tuple) and len(value) == 2:
            # Nested dataclass in tuple format: (type, dict)
            dataclass_type, field_dict = value

            # CRITICAL FIX: Preserve None values instead of letting lazy resolution materialize them
            # When user explicitly clears a field (sets to None), we want to save the None,
            # not let the lazy dataclass resolve it against context during reconstruction.
            
            # Separate None and non-None values
            none_fields = {k: v for k, v in field_dict.items() if v is None}
            non_none_fields = {k: v for k, v in field_dict.items() if v is not None}
            
            # If we have a base instance, merge into its nested dataclass
            # ANTI-DUCK-TYPING: Use dataclass introspection instead of hasattr
            if base_instance and is_dataclass(base_instance):
                field_names = {f.name for f in dataclasses.fields(base_instance)}
                if field_name in field_names:
                    base_nested = getattr(base_instance, field_name)
                    if base_nested is not None and is_dataclass(base_nested):
                        # Merge only non-None fields first (let lazy resolution happen for non-None)
                        instance = dataclasses.replace(base_nested, **non_none_fields) if non_none_fields else base_nested
                    else:
                        # No base nested dataclass, create fresh instance with non-None fields
                        instance = dataclass_type(**non_none_fields) if non_none_fields else dataclass_type()
                else:
                    # Field not in base instance, create fresh instance with non-None fields
                    instance = dataclass_type(**non_none_fields) if non_none_fields else dataclass_type()
            else:
                # No base instance, create fresh instance with non-None fields
                instance = dataclass_type(**non_none_fields) if non_none_fields else dataclass_type()
            
            # CRITICAL: Use object.__setattr__ to set None values directly, bypassing lazy resolution
            # This preserves user-cleared fields as None instead of materializing them from context
            for none_field_name in none_fields:
                object.__setattr__(instance, none_field_name, None)
            
            reconstructed[field_name] = instance
        else:
            # Regular value, pass through
            reconstructed[field_name] = value
    return reconstructed
