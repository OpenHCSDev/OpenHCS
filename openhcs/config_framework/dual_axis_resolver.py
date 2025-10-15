"""
Generic dual-axis resolver for lazy configuration inheritance.

This module provides the core inheritance resolution logic as a pure function,
supporting both context hierarchy (X-axis) and sibling inheritance (Y-axis).

The resolver is completely generic and has no application-specific dependencies.
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


# Priority functions removed - MRO-based resolution is sufficient


def resolve_field_inheritance_old(
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

    # Step 1: Check concrete value in merged context for obj's type (HIGHEST PRIORITY)
    # CRITICAL: Context values take absolute precedence over inheritance blocking
    # The config_context() manager merges concrete values into available_configs
    for config_name, config_instance in available_configs.items():
        if type(config_instance) == obj_type:
            try:
                # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                value = object.__getattribute__(config_instance, field_name)
                if value is not None:
                    if field_name == 'well_filter':
                        logger.debug(f"🔍 CONTEXT: Found concrete value in merged context {obj_type.__name__}.{field_name}: {value}")
                    return value
            except AttributeError:
                # Field doesn't exist on this config type
                continue

    # Step 1b: Check concrete value on obj instance itself (fallback)
    # Use object.__getattribute__ to avoid recursion with lazy __getattribute__
    try:
        value = object.__getattribute__(obj, field_name)
        if value is not None:
            if field_name == 'well_filter':
                logger.debug(f"🔍 INSTANCE: Found concrete value on instance {obj_type.__name__}.{field_name}: {value}")
            return value
    except AttributeError:
        # Field doesn't exist on the object
        pass

    # Step 2: FIELD-SPECIFIC INHERITANCE BLOCKING
    # Check if this specific field has a concrete value in the exact same type
    # Only block inheritance if the EXACT same type has a non-None value
    for config_name, config_instance in available_configs.items():
        if type(config_instance) == obj_type:
            try:
                field_value = object.__getattribute__(config_instance, field_name)
                if field_value is not None:
                    # This exact type has a concrete value - use it, don't inherit
                    if field_name == 'well_filter':
                        logger.debug(f"🔍 FIELD-SPECIFIC BLOCKING: {obj_type.__name__}.{field_name} = {field_value} (concrete) - blocking inheritance")
                    return field_value
            except AttributeError:
                continue

    # DEBUG: Log what we're trying to resolve
    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
        logger.debug(f"🔍 RESOLVING {obj_type.__name__}.{field_name} - checking context and inheritance")
        logger.debug(f"🔍 AVAILABLE CONFIGS: {list(available_configs.keys())}")

    # Step 3: Y-axis inheritance within obj's MRO
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
                    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
                        logger.debug(f"🔍 Y-AXIS INHERITANCE: {parent_type.__name__}.{field_name} = {value}")
                    if value is not None:
                        if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
                            logger.debug(f"🔍 Y-AXIS INHERITANCE: FOUND {parent_type.__name__}.{field_name}: {value} (returning)")
                        logger.debug(f"Inherited from {parent_type.__name__}: {value}")
                        return value
                except AttributeError:
                    # Field doesn't exist on this config type
                    continue

    # Step 4: Cross-dataclass inheritance from related config types (MRO-based)
    # NOTE: Inheritance blocking was already applied in Step 2, so this only runs for types without concrete overrides
    # Uses pure MRO-based resolution - no custom priority functions needed
    for config_name, config_instance in available_configs.items():
        config_type = type(config_instance)

        if _is_related_config_type(obj_type, config_type):
            # Skip if this is the same type as the requesting object (avoid self-inheritance)
            if config_type == obj_type:
                if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
                    logger.debug(f"🔍 CROSS-DATACLASS: Skipping self-inheritance from {config_type.__name__}")
                continue

            try:
                # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                value = object.__getattribute__(config_instance, field_name)
                if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
                    logger.debug(f"🔍 CROSS-DATACLASS: {config_type.__name__}.{field_name} = {value} (related config)")
                if value is not None:
                    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
                        logger.debug(f"🔍 CROSS-DATACLASS: FOUND {config_type.__name__}.{field_name}: {value}")
                    logger.debug(f"Cross-dataclass inheritance from {config_type.__name__}: {value}")
                    return value
            except AttributeError:
                # Field doesn't exist on this config type
                if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
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

    CRITICAL FIX: Only allow inheritance from parent classes or sibling classes at the same level,
    NOT from child classes. This prevents WellFilterConfig from inheriting from StepWellFilterConfig.

    Args:
        obj_type: The type requesting field resolution
        config_type: The type being checked for relationship

    Returns:
        True if config_type should be considered for cross-dataclass inheritance
    """
    # CRITICAL: Only allow inheritance from parent classes (obj_type inherits from config_type)
    # This prevents base classes from inheriting from their derived classes
    if issubclass(obj_type, config_type):
        return True

    # Allow sibling inheritance only if they share a common parent but neither inherits from the other
    # This allows StepMaterializationConfig to inherit from both StepWellFilterConfig and PathPlanningConfig
    if not issubclass(config_type, obj_type):  # config_type is NOT a child of obj_type
        # Check if they share a common dataclass ancestor (excluding themselves)
        obj_ancestors = set(cls for cls in obj_type.__mro__[1:] if is_dataclass(cls))  # Skip obj_type itself
        config_ancestors = set(cls for cls in config_type.__mro__[1:] if is_dataclass(cls))  # Skip config_type itself

        shared_ancestors = obj_ancestors & config_ancestors
        if shared_ancestors:
            return True

    return False


def resolve_field_inheritance(
    obj,
    field_name: str,
    available_configs: Dict[str, Any]
) -> Any:
    """
    Simplified MRO-based inheritance resolution.

    ALGORITHM:
    1. Check if obj has concrete value for field_name in context
    2. Traverse obj's MRO from most to least specific
    3. For each MRO class, check if there's a config instance in context with concrete (non-None) value
    4. Return first concrete value found

    Args:
        obj: The object requesting field resolution
        field_name: Name of the field to resolve
        available_configs: Dict mapping config type names to config instances

    Returns:
        Resolved field value or None if not found
    """
    obj_type = type(obj)

    # Step 1: Check if exact same type has concrete value in context
    for config_name, config_instance in available_configs.items():
        if type(config_instance) == obj_type:
            try:
                field_value = object.__getattribute__(config_instance, field_name)
                if field_value is not None:
                    if field_name == 'well_filter':
                        logger.debug(f"🔍 CONCRETE VALUE: {obj_type.__name__}.{field_name} = {field_value}")
                    return field_value
            except AttributeError:
                continue

    # Step 2: MRO-based inheritance - traverse MRO from most to least specific
    # For each class in the MRO, check if there's a config instance in context with concrete value
    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
        logger.debug(f"🔍 MRO-INHERITANCE: Resolving {obj_type.__name__}.{field_name}")
        logger.debug(f"🔍 MRO-INHERITANCE: MRO = {[cls.__name__ for cls in obj_type.__mro__]}")

    for mro_class in obj_type.__mro__:
        if not is_dataclass(mro_class):
            continue

        # Look for a config instance of this MRO class type in the available configs
        for config_name, config_instance in available_configs.items():
            if type(config_instance) == mro_class:
                try:
                    value = object.__getattribute__(config_instance, field_name)
                    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
                        logger.debug(f"🔍 MRO-INHERITANCE: {mro_class.__name__}.{field_name} = {value}")
                    if value is not None:
                        if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
                            logger.debug(f"🔍 MRO-INHERITANCE: FOUND {mro_class.__name__}.{field_name}: {value} (returning)")
                        return value
                except AttributeError:
                    continue

    # Step 3: Class defaults as final fallback
    try:
        class_default = object.__getattribute__(obj_type, field_name)
        if class_default is not None:
            if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
                logger.debug(f"🔍 CLASS-DEFAULT: {obj_type.__name__}.{field_name} = {class_default}")
            return class_default
    except AttributeError:
        pass

    if field_name in ['output_dir_suffix', 'sub_dir', 'well_filter']:
        logger.debug(f"🔍 NO-RESOLUTION: {obj_type.__name__}.{field_name} = None")
    return None


# Utility functions for inheritance detection (kept from original resolver)

def _has_concrete_field_override(config_class: Type, field_name: str) -> bool:
    """
    Check if a class has a concrete field override (not None).

    This determines class-level inheritance blocking behavior based on static class definition.
    Now checks the entire MRO chain to handle inherited fields properly.
    """
    try:
        # Check the entire MRO chain for concrete field values
        for cls in config_class.__mro__:
            if hasattr(cls, field_name):
                # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                class_attr_value = object.__getattribute__(cls, field_name)
                if class_attr_value is not None:
                    has_override = True
                    logger.debug(f"Class override check {config_class.__name__}.{field_name}: found concrete value {class_attr_value} in {cls.__name__}, has_override={has_override}")
                    return has_override

        # No concrete value found in any class in the MRO
        logger.debug(f"Class override check {config_class.__name__}.{field_name}: no concrete value in MRO, has_override=False")
        return False
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
