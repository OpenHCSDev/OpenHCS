"""
Generic dual-axis resolver for lazy configuration inheritance.

This module provides the core inheritance resolution logic as a pure function,
supporting both context hierarchy (X-axis) and sibling inheritance (Y-axis).

The resolver is completely generic and has no application-specific dependencies.
"""

import logging
from typing import Any, Dict, Optional, Tuple
from dataclasses import is_dataclass

logger = logging.getLogger(__name__)

# PERFORMANCE: Cache MRO resolution results
# Key: (obj_type, field_name, context_signature) -> resolved value
# context_signature = tuple of (config_type, id(config_instance)) for stable identity
_mro_resolution_cache: Dict[Tuple, Any] = {}
_CACHE_SENTINEL = object()  # Distinguishes "cached None" from "not cached"


def _make_context_signature(available_configs: Dict[str, Any]) -> Tuple:
    """Create a hashable signature for the context configs.

    Uses config type names as signature. The caller's scope determines which
    ancestor configs are available, so same types = same resolution result.

    NOTE: This assumes that within a single compute cycle, the same config types
    will resolve to the same values. Cache is invalidated when values change.
    """
    return tuple(sorted(available_configs.keys()))


def clear_mro_resolution_cache() -> None:
    """Clear the MRO resolution cache. Call when context fundamentally changes."""
    _mro_resolution_cache.clear()


def invalidate_mro_cache_for_field(changed_type: type, field_name: str) -> None:
    """Invalidate cache entries for a specific field that could be affected by a type change.

    PERFORMANCE: Only clears cache entries where:
    1. The field_name matches
    2. The obj_type has changed_type in its MRO (could inherit from it)

    This is much more targeted than clear_mro_resolution_cache().
    """
    if not _mro_resolution_cache:
        return

    from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
    base_changed = get_base_type_for_lazy(changed_type) or changed_type

    keys_to_remove = []
    for key in _mro_resolution_cache:
        obj_type, cached_field, _ = key
        if cached_field != field_name:
            continue
        # Check if obj_type could inherit from changed_type
        obj_base = get_base_type_for_lazy(obj_type) or obj_type
        if base_changed in obj_base.__mro__:
            keys_to_remove.append(key)

    for key in keys_to_remove:
        del _mro_resolution_cache[key]


def _normalize_to_base(t: type) -> type:
    """Normalize lazy type to its base type for comparison.

    LazyWellFilterConfig -> WellFilterConfig
    WellFilterConfig -> WellFilterConfig
    """
    from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
    return get_base_type_for_lazy(t) or t


def _has_concrete_field_override(config_class, field_name: str) -> bool:
    """
    Check if a class has a concrete field override (not None).

    Used by lazy_factory to find MRO concrete values.
    """
    if hasattr(config_class, field_name):
        class_attr_value = getattr(config_class, field_name)
        return class_attr_value is not None
    return False


def resolve_field_inheritance(
    obj,
    field_name: str,
    available_configs: Dict[str, Any]
) -> Any:
    """
    MRO-based inheritance resolution.

    ALGORITHM:
    For LazyDataclass types:
      1. Check if same-type config exists in context with concrete value
      2. Walk MRO to find parent class configs with concrete value
      3. Fall back to static class defaults if nothing found

    For concrete classes with lazy resolution:
      1. SKIP same-type lookup (if you created ProcessingConfig(group_by=None), you want None)
      2. Walk MRO to find PARENT class configs with concrete value (sibling inheritance)
      3. Return None if nothing found (no static default fallback)

    Args:
        obj: The object requesting field resolution
        field_name: Name of the field to resolve
        available_configs: Dict mapping config type names to config instances

    Returns:
        Resolved field value or None if not found
    """
    obj_type = type(obj)

    # Check if this field needs resolution (instance value is None)
    try:
        instance_value = object.__getattribute__(obj, field_name)
        needs_resolution = instance_value is None
    except AttributeError:
        needs_resolution = True

    # Step 1: Check if exact same type has concrete value in context
    # Do same-type lookup if the field value is None (needs lazy resolution).
    # This works for both LazyDataclass types AND concrete dataclasses with None fields.
    obj_base = _normalize_to_base(obj_type)

    if needs_resolution:
        for config_key, config_instance in available_configs.items():
            # Normalize both sides: LazyWellFilterConfig matches WellFilterConfig
            instance_base = _normalize_to_base(type(config_instance))
            if instance_base == obj_base:
                try:
                    field_value = object.__getattribute__(config_instance, field_name)
                    if field_value is not None:
                        if field_name == 'well_filter':
                            logger.debug(f"🔍 CONCRETE VALUE: {obj_type.__name__}.{field_name} = {field_value}")
                        if field_name == 'num_workers':
                            logger.debug(f"🔍 SAME-TYPE MATCH: {obj_type.__name__}.{field_name} = {field_value!r} (type={type(field_value).__name__}) FROM config_key={config_key}, config_type={type(config_instance).__name__}")
                        return field_value
                except AttributeError:
                    continue

    # Step 2: MRO-based inheritance - traverse MRO from most to least specific
    # Skip the first entry (self type) since we already checked it above (for lazy) or want to skip it (for concrete)
    # This finds PARENT class configs with concrete values (sibling inheritance)
    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter', 'well_filter_mode']:
        logger.debug(f"🔍 MRO-INHERITANCE: Resolving {obj_type.__name__}.{field_name}")
        logger.debug(f"🔍 MRO-INHERITANCE: MRO = {[cls.__name__ for cls in obj_type.__mro__]}")

    for mro_class in obj_type.__mro__[1:]:  # Skip first (self type)
        if not is_dataclass(mro_class):
            continue

        # Look for a config instance of this MRO class type in the available configs
        # Normalize both sides: LazyWellFilterConfig instance matches WellFilterConfig in MRO
        mro_base = _normalize_to_base(mro_class)
        for config_instance in available_configs.values():
            instance_base = _normalize_to_base(type(config_instance))
            if instance_base == mro_base:
                try:
                    value = object.__getattribute__(config_instance, field_name)
                    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter', 'well_filter_mode']:
                        logger.debug(f"🔍 MRO-INHERITANCE: {mro_class.__name__}.{field_name} = {value}")
                    if field_name == 'num_workers':
                        logger.debug(f"🔍 MRO-INHERITANCE: {mro_class.__name__}.{field_name} = {value!r} (type={type(value).__name__})")
                    if value is not None:
                        if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter', 'well_filter_mode']:
                            logger.debug(f"🔍 MRO-INHERITANCE: FOUND {mro_class.__name__}.{field_name}: {value} (returning)")
                        if field_name == 'num_workers':
                            logger.debug(f"🔍 MRO-INHERITANCE: RETURNING {mro_class.__name__}.{field_name} = {value!r}")
                        return value
                except AttributeError:
                    continue

    # No Step 3: If MRO walk finds nothing, return None.
    # "If we wanted static class defaults, it wouldn't have been overridden to None"
    # For LazyDataclass, class defaults are all None anyway (via rebuild_with_none_defaults).
    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
        logger.debug(f"🔍 NO-RESOLUTION: {obj_type.__name__}.{field_name} = None")
    return None
