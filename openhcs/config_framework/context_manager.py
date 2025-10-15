"""
Generic contextvars-based context management system for lazy configuration.

This module provides explicit context scoping using Python's contextvars to enable
hierarchical configuration resolution without explicit parameter passing.

Key features:
1. Explicit context scoping with config_context() manager
2. Config extraction from functions, dataclasses, and objects
3. Config merging for context hierarchy
4. Clean separation between UI windows and contexts

Key components:
- current_temp_global: ContextVar holding current merged global config
- config_context(): Context manager for creating context scopes
- extract_config_overrides(): Extract config values from any object type
- merge_configs(): Merge overrides into base config
"""

import contextvars
import dataclasses
import inspect
import logging
from contextlib import contextmanager
from typing import Any, Dict, Union
from dataclasses import fields, is_dataclass

logger = logging.getLogger(__name__)

# Core contextvar for current merged global config
# This holds the current context state that resolution functions can access
current_temp_global = contextvars.ContextVar('current_temp_global')


def _merge_nested_dataclass(base, override, mask_with_none: bool = False):
    """
    Recursively merge nested dataclass fields.

    For each field in override:
    - If value is None and mask_with_none=False: skip (don't override base)
    - If value is None and mask_with_none=True: override with None (mask base)
    - If value is dataclass: recursively merge with base's value
    - Otherwise: use override value

    Args:
        base: Base dataclass instance
        override: Override dataclass instance
        mask_with_none: If True, None values override base values

    Returns:
        Merged dataclass instance
    """
    if not is_dataclass(base) or not is_dataclass(override):
        return override

    merge_values = {}
    for field_info in fields(override):
        field_name = field_info.name
        override_value = object.__getattribute__(override, field_name)

        if override_value is None:
            if mask_with_none:
                # None overrides base value (masking mode)
                merge_values[field_name] = None
            else:
                # None means "don't override" - keep base value
                continue
        elif is_dataclass(override_value):
            # Recursively merge nested dataclass
            base_value = getattr(base, field_name, None)
            if base_value is not None and is_dataclass(base_value):
                merge_values[field_name] = _merge_nested_dataclass(base_value, override_value, mask_with_none)
            else:
                merge_values[field_name] = override_value
        else:
            # Concrete value - use override
            merge_values[field_name] = override_value

    # Merge with base
    if merge_values:
        return dataclasses.replace(base, **merge_values)
    else:
        return base


@contextmanager
def config_context(obj, mask_with_none: bool = False):
    """
    Create new context scope with obj's matching fields merged into base config.

    This is the universal context manager for all config context needs. It works by:
    1. Finding fields that exist on both obj and the base config type
    2. Using matching field values to create a temporary merged config
    3. Setting that as the current context

    Args:
        obj: Object with config fields (pipeline_config, step, etc.)
        mask_with_none: If True, None values override/mask base config values.
                       If False (default), None values are ignored (normal inheritance).
                       Use True when editing GlobalPipelineConfig to mask thread-local
                       loaded instance with static class defaults.

    Usage:
        with config_context(orchestrator.pipeline_config):  # Pipeline-level context
            # ...
        with config_context(step):  # Step-level context
            # ...
        with config_context(GlobalPipelineConfig(), mask_with_none=True):  # Static defaults
            # ...
    """
    # Get current context as base for nested contexts, or fall back to base global config
    current_context = get_current_temp_global()
    base_config = current_context if current_context is not None else get_base_global_config()

    # Find matching fields between obj and base config type
    overrides = {}
    if obj is not None:
        from openhcs.config_framework.config import get_base_config_type

        base_config_type = get_base_config_type()

        for field_info in fields(base_config_type):
            field_name = field_info.name
            expected_type = field_info.type

            # Check if obj has this field
            try:
                # Use object.__getattribute__ to avoid triggering lazy resolution
                if hasattr(obj, field_name):
                    value = object.__getattribute__(obj, field_name)
                    # CRITICAL: When mask_with_none=True, None values override base config
                    # This allows static defaults to mask loaded instance values
                    if value is not None or mask_with_none:
                        # When masking with None, always include the value (even if None)
                        if mask_with_none:
                            # For nested dataclasses, merge with mask_with_none=True
                            if is_dataclass(value):
                                base_value = getattr(base_config, field_name, None)
                                if base_value is not None and is_dataclass(base_value):
                                    merged_nested = _merge_nested_dataclass(base_value, value, mask_with_none=True)
                                    overrides[field_name] = merged_nested
                                else:
                                    overrides[field_name] = value
                            else:
                                overrides[field_name] = value
                        # Normal mode: only include non-None values
                        elif value is not None:
                            # Check if value is compatible (handles lazy-to-base type mapping)
                            if _is_compatible_config_type(value, expected_type):
                                # Convert lazy configs to base configs for context
                                if hasattr(value, 'to_base_config'):
                                    value = value.to_base_config()

                                # CRITICAL FIX: Recursively merge nested dataclass fields
                                # If this is a dataclass field, merge it with the base config's value
                                # instead of replacing wholesale
                                if is_dataclass(value):
                                    base_value = getattr(base_config, field_name, None)
                                    if base_value is not None and is_dataclass(base_value):
                                        # Merge nested dataclass: base + overrides
                                        # Pass mask_with_none to recursive merge
                                        merged_nested = _merge_nested_dataclass(base_value, value, mask_with_none=False)
                                        overrides[field_name] = merged_nested
                                    else:
                                        # No base value to merge with, use override as-is
                                        overrides[field_name] = value
                                else:
                                    # Non-dataclass field, use override as-is
                                    overrides[field_name] = value
            except AttributeError:
                continue

    # Create merged config if we have overrides
    if overrides:
        try:
            merged_config = dataclasses.replace(base_config, **overrides)
            logger.debug(f"Creating config context with {len(overrides)} field overrides from {type(obj).__name__}")
        except Exception as e:
            logger.warning(f"Failed to merge config overrides from {type(obj).__name__}: {e}")
            merged_config = base_config
    else:
        merged_config = base_config
        logger.debug(f"Creating config context with no overrides from {type(obj).__name__}")

    token = current_temp_global.set(merged_config)
    try:
        yield
    finally:
        current_temp_global.reset(token)


# Removed: extract_config_overrides - no longer needed with field matching approach


# UNUSED: Kept for compatibility but no longer used with field matching approach
def extract_from_function_signature(func) -> Dict[str, Any]:
    """
    Get parameter defaults as config overrides.
    
    This enables functions to provide config context through their parameter defaults.
    Useful for step functions that want to specify their own config values.
    
    Args:
        func: Function to extract parameter defaults from
        
    Returns:
        Dict of parameter_name -> default_value for parameters with defaults
    """
    try:
        sig = inspect.signature(func)
        overrides = {}
        
        for name, param in sig.parameters.items():
            if param.default != inspect.Parameter.empty:
                overrides[name] = param.default
                
        logger.debug(f"Extracted {len(overrides)} overrides from function {func.__name__}")
        return overrides
        
    except (ValueError, TypeError) as e:
        logger.debug(f"Could not extract signature from {func}: {e}")
        return {}


def extract_from_dataclass_fields(obj) -> Dict[str, Any]:
    """
    Get non-None fields as config overrides.
    
    This extracts concrete values from dataclass instances, ignoring None values
    which represent fields that should inherit from context.
    
    Args:
        obj: Dataclass instance to extract field values from
        
    Returns:
        Dict of field_name -> value for non-None fields
    """
    if not is_dataclass(obj):
        return {}
        
    overrides = {}
    
    for field in fields(obj):
        value = getattr(obj, field.name)
        if value is not None:
            overrides[field.name] = value
            
    logger.debug(f"Extracted {len(overrides)} overrides from dataclass {type(obj).__name__}")
    return overrides


def extract_from_object_attributes(obj) -> Dict[str, Any]:
    """
    Extract config attributes from step/pipeline objects.
    
    This handles orchestrators, steps, and other objects that have *_config attributes.
    It flattens the config hierarchy into a single dict of field overrides.
    
    Args:
        obj: Object to extract config attributes from
        
    Returns:
        Dict of field_name -> value for all non-None config fields
    """
    overrides = {}
    
    try:
        for attr_name in dir(obj):
            if attr_name.endswith('_config'):
                attr_value = getattr(obj, attr_name)
                if attr_value is not None and is_dataclass(attr_value):
                    # Extract all non-None fields from this config
                    config_overrides = extract_from_dataclass_fields(attr_value)
                    overrides.update(config_overrides)
                    
        logger.debug(f"Extracted {len(overrides)} overrides from object {type(obj).__name__}")
        
    except Exception as e:
        logger.debug(f"Error extracting from object {obj}: {e}")
        
    return overrides


def merge_configs(base, overrides: Dict[str, Any]):
    """
    Merge overrides into base config, creating new immutable instance.
    
    This creates a new config instance with override values merged in,
    preserving immutability of the original base config.
    
    Args:
        base: Base config instance (base config type)
        overrides: Dict of field_name -> value to override
        
    Returns:
        New config instance with overrides applied
    """
    if not base or not overrides:
        return base
        
    try:
        # Filter out None values - they should not override existing values
        filtered_overrides = {k: v for k, v in overrides.items() if v is not None}
        
        if not filtered_overrides:
            return base
            
        # Use dataclasses.replace to create new instance with overrides
        merged = dataclasses.replace(base, **filtered_overrides)
        
        logger.debug(f"Merged {len(filtered_overrides)} overrides into {type(base).__name__}")
        return merged
        
    except Exception as e:
        logger.warning(f"Failed to merge configs: {e}")
        return base


def get_base_global_config():
    """
    Get the base global config (fallback when no context set).

    This provides the global config that was set up with ensure_global_config_context(),
    or a default if none was set. Used as the base for merging operations.

    Returns:
        Current global config instance or default instance of base config type
    """
    try:
        from openhcs.config_framework.config import get_base_config_type
        from openhcs.config_framework.global_config import get_current_global_config

        base_config_type = get_base_config_type()

        # First try to get the global config that was set up
        current_global = get_current_global_config(base_config_type)
        if current_global is not None:
            return current_global

        # Fallback to default if none was set
        return base_config_type()
    except ImportError:
        logger.warning("Could not get base config type")
        return None


def get_current_temp_global():
    """
    Get current context or None.
    
    This is the primary interface for resolution functions to access
    the current context. Returns None if no context is active.
    
    Returns:
        Current merged global config or None
    """
    return current_temp_global.get(None)


def set_current_temp_global(config):
    """
    Set current context (for testing/debugging).
    
    This is primarily for testing purposes. Normal code should use
    config_context() manager instead.
    
    Args:
        config: Global config instance to set as current context
        
    Returns:
        Token for resetting the context
    """
    return current_temp_global.set(config)


def clear_current_temp_global():
    """
    Clear current context (for testing/debugging).
    
    This removes any active context, causing resolution to fall back
    to default behavior.
    """
    try:
        current_temp_global.set(None)
    except LookupError:
        pass  # No context was set


# Utility functions for debugging and introspection

def get_context_info() -> Dict[str, Any]:
    """
    Get information about current context for debugging.
    
    Returns:
        Dict with context information including type, field count, etc.
    """
    current = get_current_temp_global()
    if current is None:
        return {"active": False}
        
    return {
        "active": True,
        "type": type(current).__name__,
        "field_count": len(fields(current)) if is_dataclass(current) else 0,
        "non_none_fields": sum(1 for f in fields(current) 
                              if getattr(current, f.name) is not None) if is_dataclass(current) else 0
    }


def extract_all_configs_from_context() -> Dict[str, Any]:
    """
    Extract all *_config attributes from current context.

    This is used by the resolution system to get all available configs
    for cross-dataclass inheritance resolution.

    Returns:
        Dict of config_name -> config_instance for all *_config attributes
    """
    current = get_current_temp_global()
    if current is None:
        return {}

    return extract_all_configs(current)


def extract_all_configs(context_obj) -> Dict[str, Any]:
    """
    Extract all config instances from a context object using type-driven approach.

    This function leverages dataclass field type annotations to efficiently extract
    config instances, avoiding string matching and runtime attribute scanning.

    Args:
        context_obj: Object to extract configs from (orchestrator, merged config, etc.)

    Returns:
        Dict mapping config type names to config instances
    """
    if context_obj is None:
        return {}

    configs = {}

    # Include the context object itself if it's a dataclass
    if is_dataclass(context_obj):
        configs[type(context_obj).__name__] = context_obj

    # Type-driven extraction: Use dataclass field annotations to find config fields
    if is_dataclass(type(context_obj)):
        for field_info in fields(type(context_obj)):
            field_type = field_info.type
            field_name = field_info.name

            # Handle Optional[ConfigType] annotations
            actual_type = _unwrap_optional_type(field_type)

            # Only process fields that are dataclass types (config objects)
            if is_dataclass(actual_type):
                try:
                    field_value = getattr(context_obj, field_name)
                    if field_value is not None:
                        # Use the actual instance type, not the annotation type
                        # This handles cases where field is annotated as base class but contains subclass
                        instance_type = type(field_value)
                        configs[instance_type.__name__] = field_value

                        logger.debug(f"Extracted config {instance_type.__name__} from field {field_name}")

                except AttributeError:
                    # Field doesn't exist on instance (shouldn't happen with dataclasses)
                    logger.debug(f"Field {field_name} not found on {type(context_obj).__name__}")
                    continue

    # For non-dataclass objects (orchestrators, etc.), extract dataclass attributes
    else:
        _extract_from_object_attributes_typed(context_obj, configs)

    logger.debug(f"Extracted {len(configs)} configs: {list(configs.keys())}")
    return configs


def _unwrap_optional_type(field_type):
    """
    Unwrap Optional[T] and Union[T, None] types to get the actual type T.

    This handles type annotations like Optional[ConfigType] -> ConfigType
    """
    # Handle typing.Optional and typing.Union
    if hasattr(field_type, '__origin__'):
        if field_type.__origin__ is Union:
            # Get non-None types from Union
            non_none_types = [arg for arg in field_type.__args__ if arg is not type(None)]
            if len(non_none_types) == 1:
                return non_none_types[0]

    return field_type


def _extract_from_object_attributes_typed(obj, configs: Dict[str, Any]) -> None:
    """
    Type-safe extraction from object attributes for non-dataclass objects.

    This is used for orchestrators and other objects that aren't dataclasses
    but have config attributes. Uses type checking instead of string matching.
    """
    try:
        # Get all attributes that are dataclass instances
        for attr_name in dir(obj):
            if attr_name.startswith('_'):
                continue

            try:
                attr_value = getattr(obj, attr_name)
                if attr_value is not None and is_dataclass(attr_value):
                    configs[type(attr_value).__name__] = attr_value
                    logger.debug(f"Extracted config {type(attr_value).__name__} from attribute {attr_name}")

            except (AttributeError, TypeError):
                # Skip attributes that can't be accessed or aren't relevant
                continue

    except Exception as e:
        logger.debug(f"Error in typed attribute extraction: {e}")


def _is_compatible_config_type(value, expected_type) -> bool:
    """
    Check if value is compatible with expected_type, handling lazy-to-base type mapping.

    This handles cases where:
    - value is LazyStepMaterializationConfig, expected_type is StepMaterializationConfig
    - value is a subclass of the expected type
    - value is exactly the expected type
    """
    value_type = type(value)

    # Direct type match
    if value_type == expected_type:
        return True

    # Check if value_type is a subclass of expected_type
    try:
        if issubclass(value_type, expected_type):
            return True
    except TypeError:
        # expected_type might not be a class (e.g., Union, Optional)
        pass

    # Check lazy-to-base type mapping
    if hasattr(value, 'to_base_config'):
        # This is a lazy config - check if its base type matches expected_type
        from openhcs.config_framework.lazy_factory import _lazy_type_registry
        base_type = _lazy_type_registry.get(value_type)
        if base_type == expected_type:
            return True
        # Also check if base type is subclass of expected type
        if base_type and issubclass(base_type, expected_type):
            return True

    return False
