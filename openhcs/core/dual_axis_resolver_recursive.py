"""
Dual-axis resolver with pure function interface.

This module provides the core inheritance resolution logic as a pure function,
removing complex context discovery and stack introspection.

Phase 2.1 Complete: Cleaned up dual-axis resolver to pure function interface.
"""

import logging
from typing import Any, Dict, Type, Optional
from dataclasses import is_dataclass

logger = logging.getLogger(__name__)


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
        return has_override
    return False


def resolve_field_inheritance(
    obj, 
    field_name: str, 
    available_configs: Dict[str, Any]
) -> Any:
    """
    Pure function for cross-dataclass inheritance resolution.
    
    This replaces the complex RecursiveContextualResolver with explicit parameter passing.
    
    Args:
        obj: The object requesting field resolution
        field_name: Name of the field to resolve
        available_configs: Dict mapping config type names to config instances
                          e.g., {'GlobalPipelineConfig': global_config, 'StepConfig': step_config}
    
    Returns:
        Resolved field value or None if not found
    
    Algorithm:
    1. Check if obj has concrete value for field_name
    2. Check Y-axis inheritance within obj's MRO for concrete values
    3. Check related config types in available_configs for cross-dataclass inheritance
    4. Return class defaults as final fallback
    """
    obj_type = type(obj)
    
    # Step 1: Check concrete value on obj itself
    # Use object.__getattribute__ to avoid recursion with lazy __getattribute__
    try:
        value = object.__getattribute__(obj, field_name)
        if value is not None:
            logger.debug(f"Found concrete value on {obj_type.__name__}.{field_name}: {value}")
            return value
    except AttributeError:
        # Field doesn't exist on the object
        pass

    # DEBUG: Log what we're trying to resolve
    if field_name in ['output_dir_suffix', 'sub_dir']:
        logger.debug(f"🔍 RESOLVING {obj_type.__name__}.{field_name} - checking context and inheritance")
        logger.debug(f"🔍 AVAILABLE CONFIGS: {list(available_configs.keys())}")
    
    # Step 2: Y-axis inheritance within obj's MRO
    blocking_class = _find_blocking_class_in_mro(obj_type, field_name)
    
    for parent_type in obj_type.__mro__[1:]:
        if not is_dataclass(parent_type):
            continue
            
        # Check blocking logic
        if blocking_class and parent_type != blocking_class:
            continue
            
        if blocking_class and parent_type == blocking_class:
            # Check if blocking class has concrete value in available configs
            for config_name, config_instance in available_configs.items():
                if type(config_instance) == parent_type:
                    try:
                        # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                        value = object.__getattribute__(config_instance, field_name)
                        if value is None:
                            # Blocking class has None - inheritance blocked
                            break
                        else:
                            logger.debug(f"Inherited from blocking class {parent_type.__name__}: {value}")
                            return value
                    except AttributeError:
                        # Field doesn't exist on this config type
                        continue
            break

        # Normal inheritance - check for concrete values
        for config_name, config_instance in available_configs.items():
            if type(config_instance) == parent_type:
                try:
                    # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                    value = object.__getattribute__(config_instance, field_name)
                    if field_name in ['output_dir_suffix', 'sub_dir']:
                        logger.debug(f"🔍 Y-AXIS INHERITANCE: {parent_type.__name__}.{field_name} = {value}")
                    if value is not None:
                        if field_name in ['output_dir_suffix', 'sub_dir']:
                            logger.debug(f"🔍 Y-AXIS INHERITANCE: FOUND {parent_type.__name__}.{field_name}: {value} (returning)")
                        logger.debug(f"Inherited from {parent_type.__name__}: {value}")
                        return value
                except AttributeError:
                    # Field doesn't exist on this config type
                    continue
    
    # Step 3: Cross-dataclass inheritance from related config types
    for config_name, config_instance in available_configs.items():
        config_type = type(config_instance)
        if field_name in ['output_dir_suffix', 'sub_dir']:
            logger.debug(f"🔍 CROSS-DATACLASS: Checking {config_type.__name__} for {field_name}")
        if _is_related_config_type(obj_type, config_type):
            try:
                # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                value = object.__getattribute__(config_instance, field_name)
                if field_name in ['output_dir_suffix', 'sub_dir']:
                    logger.debug(f"🔍 CROSS-DATACLASS: {config_type.__name__}.{field_name} = {value} (related config)")
                if value is not None:
                    if field_name in ['output_dir_suffix', 'sub_dir']:
                        logger.debug(f"🔍 CROSS-DATACLASS: FOUND {config_type.__name__}.{field_name}: {value}")
                    logger.debug(f"Cross-dataclass inheritance from {config_type.__name__}: {value}")
                    return value
            except AttributeError:
                # Field doesn't exist on this config type
                if field_name in ['output_dir_suffix', 'sub_dir']:
                    logger.debug(f"🔍 CROSS-DATACLASS: {config_type.__name__} has no field {field_name}")
                continue
        else:
            if field_name in ['output_dir_suffix', 'sub_dir']:
                logger.debug(f"🔍 CROSS-DATACLASS: {config_type.__name__} not related to {obj_type.__name__}")
    
    # Step 4: Class defaults as final fallback
    if blocking_class:
        try:
            # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
            class_default = object.__getattribute__(blocking_class, field_name)
            if class_default is not None:
                logger.debug(f"Using class default from blocking class {blocking_class.__name__}: {class_default}")
                return class_default
        except AttributeError:
            # Field doesn't exist on blocking class
            pass
    
    logger.debug(f"No resolution found for {obj_type.__name__}.{field_name}")
    return None


def _is_related_config_type(obj_type: Type, config_type: Type) -> bool:
    """
    Check if config_type is related to obj_type for cross-dataclass inheritance.

    Related types are those that:
    1. Have inheritance relationships (obj_type inherits from config_type or vice versa)
    2. Share common field names and are part of the same configuration domain
    """


    # Check direct inheritance relationships first
    if issubclass(obj_type, config_type) or issubclass(config_type, obj_type):
        return True

    # Check if they share common dataclass fields
    if is_dataclass(obj_type) and is_dataclass(config_type):
        from dataclasses import fields
        obj_fields = {f.name for f in fields(obj_type)}
        config_fields = {f.name for f in fields(config_type)}
        shared_fields = obj_fields & config_fields
        # If they share more than 2 fields, consider them related
        if len(shared_fields) > 2:
            return True

    return False


# Utility functions for inheritance detection (kept from original resolver)

def _has_concrete_field_override(config_class: Type, field_name: str) -> bool:
    """
    Check if a class has a concrete field override (not None).

    This determines class-level inheritance blocking behavior based on static class definition.
    """
    try:
        # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
        class_attr_value = object.__getattribute__(config_class, field_name)
        has_override = class_attr_value is not None
        logger.debug(f"Class override check {config_class.__name__}.{field_name}: value={class_attr_value}, has_override={has_override}")
        return has_override
    except AttributeError:
        # Field doesn't exist on class
        return False


def _find_blocking_class_in_mro(base_type: Type, field_name: str) -> Optional[Type]:
    """
    Find the first class in MRO that has a concrete field override AND blocks inheritance from parent classes.

    A class blocks inheritance only if:
    1. It has a concrete field override
    2. There are parent classes in the MRO that also have the same field

    This prevents legitimate inheritance sources (like GlobalPipelineConfig) from being treated as blockers.

    Returns:
        The first class in MRO order that blocks inheritance, or None if no blocking class found.
    """
    for i, cls in enumerate(base_type.__mro__):
        if not is_dataclass(cls):
            continue
        if _has_concrete_field_override(cls, field_name):
            # Check if there are parent classes that also have this field
            has_parent_with_field = False
            for parent_cls in base_type.__mro__[i + 1:]:
                if not is_dataclass(parent_cls):
                    continue
                try:
                    # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                    object.__getattribute__(parent_cls, field_name)
                    has_parent_with_field = True
                    break
                except AttributeError:
                    # Field doesn't exist on this parent class
                    continue

            if has_parent_with_field:
                logger.debug(f"Found blocking class {cls.__name__} for {base_type.__name__}.{field_name} (blocks parent inheritance)")
                return cls
            else:
                logger.debug(f"Class {cls.__name__} has concrete override but no parents with field - not blocking")
    return None


# All legacy functions removed - use resolve_field_inheritance() instead
