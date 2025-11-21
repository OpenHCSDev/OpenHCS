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
from abc import ABC, abstractmethod
from contextlib import contextmanager
from typing import Any, Dict, Union, Tuple, Optional
from dataclasses import fields, is_dataclass

logger = logging.getLogger(__name__)

# Core contextvar for current merged global config
# This holds the current context state that resolution functions can access
current_temp_global = contextvars.ContextVar('current_temp_global')

# Cached extracted configs for the current context
# This avoids re-extracting configs on every attribute access
current_extracted_configs: contextvars.ContextVar[Dict[str, Any]] = contextvars.ContextVar('current_extracted_configs', default={})

# Stack of original (unmerged) context objects
# This preserves lazy type information that gets lost during merging
current_context_stack: contextvars.ContextVar[list] = contextvars.ContextVar('current_context_stack', default=[])

# Scope information for the current context
# Maps config type names to their scope IDs (None for global, string for scoped)
current_config_scopes: contextvars.ContextVar[Dict[str, Optional[str]]] = contextvars.ContextVar('current_config_scopes', default={})

# Current scope ID for resolution context
current_scope_id: contextvars.ContextVar[Optional[str]] = contextvars.ContextVar('current_scope_id', default=None)


class ScopedObject(ABC):
    """
    Abstract base class for objects that can provide scope information.

    This is a generic interface that allows the config framework to remain
    domain-agnostic while supporting hierarchical scope identification.

    Implementations should build their scope identifier from a context provider
    (e.g., orchestrator, session, request, etc.) that contains the necessary
    contextual information.
    """

    @abstractmethod
    def build_scope_id(self, context_provider) -> Optional[str]:
        """
        Build scope identifier from context provider.

        Args:
            context_provider: Domain-specific context provider (e.g., orchestrator)
                            that contains information needed to build the scope.

        Returns:
            Scope identifier string, or None for global scope.

        Examples:
            - Global config: return None
            - Plate-level config: return str(context_provider.plate_path)
            - Step-level config: return f"{context_provider.plate_path}::{self.token}"
        """
        pass


class ScopeProvider:
    """
    Minimal context provider for UI code that only has scope strings.

    This allows UI code to create scoped contexts when it doesn't have
    access to the full orchestrator, but only has the scope string
    (e.g., from live_context_scopes).

    Example:
        scope_string = "/path/to/plate"
        provider = ScopeProvider(scope_string)
        with config_context(pipeline_config, context_provider=provider):
            # ...
    """
    def __init__(self, scope_string: str):
        from pathlib import Path
        # Extract plate_path from scope string (format: "plate_path::step_token" or just "plate_path")
        # CRITICAL: scope_string might be hierarchical like "/path/to/plate::step_0"
        # We need to extract just the plate_path part (before the first ::)
        if '::' in scope_string:
            plate_path_str = scope_string.split('::')[0]
        else:
            plate_path_str = scope_string
        self.plate_path = Path(plate_path_str)


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
def config_context(obj, *, context_provider=None, mask_with_none: bool = False, config_scopes: Optional[Dict[str, Optional[str]]] = None):
    """
    Create new context scope with obj's matching fields merged into base config.

    This is the universal context manager for all config context needs. It works by:
    1. Finding fields that exist on both obj and the base config type
    2. Using matching field values to create a temporary merged config
    3. Setting that as the current context

    Args:
        obj: Object with config fields (pipeline_config, step, etc.)
        context_provider: Optional context provider (e.g., orchestrator or ScopeProvider) for deriving scope_id.
                         If obj implements ScopedObject, scope_id will be auto-derived by calling
                         obj.build_scope_id(context_provider). Not needed for global configs.
        mask_with_none: If True, None values override/mask base config values.
                       If False (default), None values are ignored (normal inheritance).
                       Use True when editing GlobalPipelineConfig to mask thread-local
                       loaded instance with static class defaults.
        config_scopes: Optional dict mapping config type names to their scope IDs

    Usage:
        # Auto-derive scope from orchestrator:
        with config_context(orchestrator.pipeline_config, context_provider=orchestrator):
            with config_context(step, context_provider=orchestrator):
                # ...

        # UI code with scope string:
        provider = ScopeProvider("/path/to/plate")
        with config_context(pipeline_config, context_provider=provider):
            # ...

        # Global scope (no context_provider needed):
        with config_context(GlobalPipelineConfig(), mask_with_none=True):
            # ...
    """
    # Auto-derive scope_id from context_provider
    if context_provider is not None and isinstance(obj, ScopedObject):
        scope_id = obj.build_scope_id(context_provider)
        logger.info(f"🔍 CONFIG_CONTEXT SCOPE: ScopedObject.build_scope_id() -> {scope_id} for {type(obj).__name__}")
    elif context_provider is not None and isinstance(context_provider, ScopeProvider):
        # CRITICAL FIX: For UI code that passes ScopeProvider with a scope string,
        # use the scope string directly even if obj is not a ScopedObject
        # This enables placeholder resolution for LazyPipelineConfig and other lazy configs
        # that need scope information but don't implement ScopedObject
        scope_id = str(context_provider.plate_path)
        logger.info(f"🔍 CONFIG_CONTEXT SCOPE: ScopeProvider.plate_path -> {scope_id} for {type(obj).__name__}")
    else:
        scope_id = None
        logger.info(f"🔍 CONFIG_CONTEXT SCOPE: None (no provider or not Scoped/Provider) for {type(obj).__name__}, provider={type(context_provider).__name__ if context_provider else None}")

    # Get current context as base for nested contexts, or fall back to base global config
    current_context = get_current_temp_global()
    base_config = current_context if current_context is not None else get_base_global_config()

    # CRITICAL: Extract configs from ORIGINAL object FIRST (before to_base_config() conversion)
    # This preserves lazy type information that gets lost during merging
    # Use bypass_lazy_resolution=True to get raw values without triggering resolution
    # This is important for unsaved changes detection
    original_extracted = {}
    if obj is not None:
        original_extracted = extract_all_configs(obj, bypass_lazy_resolution=True)
        if 'LazyWellFilterConfig' in original_extracted or 'WellFilterConfig' in original_extracted:
            logger.debug(f"🔍 CONTEXT MANAGER: original_extracted from {type(obj).__name__} has LazyWellFilterConfig={('LazyWellFilterConfig' in original_extracted)}, WellFilterConfig={('WellFilterConfig' in original_extracted)}")
        logger.debug(f"🔍 CONTEXT MANAGER: original_extracted from {type(obj).__name__} = {set(original_extracted.keys())}")

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

    # Extract configs from merged config
    extracted = extract_all_configs(merged_config)
    logger.info(f"🔍 CONTEXT MANAGER: extracted from merged = {set(extracted.keys())}")
    logger.info(f"🔍 CONTEXT MANAGER: extracted types = {[(k, type(v).__name__) for k, v in extracted.items()]}")

    # CRITICAL: Original configs ALWAYS override merged configs to preserve lazy types
    # This ensures LazyWellFilterConfig from PipelineConfig takes precedence over
    # WellFilterConfig from the merged GlobalPipelineConfig
    for config_name, config_instance in original_extracted.items():
        extracted[config_name] = config_instance

    logger.info(f"🔍 CONTEXT MANAGER: After original override, extracted = {set(extracted.keys())}")
    logger.info(f"🔍 CONTEXT MANAGER: After original override, types = {[(k, type(v).__name__) for k, v in extracted.items()]}")

    # CRITICAL: Merge with parent context's extracted configs instead of replacing
    # When contexts are nested (GlobalPipelineConfig → PipelineConfig), we need to preserve
    # configs from outer contexts while allowing inner contexts to override
    parent_extracted = current_extracted_configs.get()
    # Track which configs were extracted from the CURRENT context object itself (original_extracted)
    # NOT from the merged base - this is critical for scope assignment
    # CRITICAL: Normalize config names by removing "Lazy" prefix for scope tracking
    # LazyWellFilterConfig and WellFilterConfig should be treated as the same config type
    current_context_configs = set()
    for config_name in original_extracted.keys():
        # Normalize: LazyWellFilterConfig -> WellFilterConfig
        normalized_name = config_name.replace('Lazy', '') if config_name.startswith('Lazy') else config_name
        current_context_configs.add(normalized_name)
    logger.debug(f"🔍 CONTEXT MANAGER: Built current_context_configs from original_extracted.keys() = {current_context_configs}")
    if parent_extracted:
        # Start with parent's configs
        merged_extracted = dict(parent_extracted)
        # Override with current context's configs (inner context takes precedence)
        merged_extracted.update(extracted)
        extracted = merged_extracted

    # Push original object onto context stack
    current_stack = current_context_stack.get()
    new_stack = current_stack + [obj] if obj is not None else current_stack

    # Update scope information if provided
    if config_scopes is not None:
        # Merge with parent scopes
        parent_scopes = current_config_scopes.get()
        logger.info(f"🔍 SCOPE MERGE: Entering {type(obj).__name__}, parent_scopes has {len(parent_scopes)} entries")
        logger.info(f"🔍 SCOPE MERGE: config_scopes parameter has {len(config_scopes)} entries")
        if 'StreamingDefaults' in parent_scopes:
            logger.info(f"🔍 SCOPE MERGE: parent_scopes['StreamingDefaults'] = {parent_scopes.get('StreamingDefaults')}")
        if 'StreamingDefaults' in config_scopes:
            logger.info(f"🔍 SCOPE MERGE: config_scopes['StreamingDefaults'] = {config_scopes.get('StreamingDefaults')}")

        merged_scopes = dict(parent_scopes) if parent_scopes else {}

        # CRITICAL: Selectively update scopes - don't overwrite more specific scopes with None
        # If parent has StreamingDefaults: plate_path and config_scopes has StreamingDefaults: None,
        # keep the plate_path (more specific)
        for config_name, new_scope in config_scopes.items():
            existing_scope = merged_scopes.get(config_name)
            if existing_scope is None and new_scope is not None:
                # Existing is None, new is specific - overwrite
                merged_scopes[config_name] = new_scope
            elif existing_scope is not None and new_scope is None:
                # Existing is specific, new is None - DON'T overwrite, keep existing
                if config_name == 'StreamingDefaults':
                    logger.info(f"🔍 SCOPE MERGE: PRESERVING {config_name} scope {existing_scope} (not overwriting with None)")
            else:
                # Both None or both specific - use new scope
                merged_scopes[config_name] = new_scope

        if 'StreamingDefaults' in merged_scopes:
            logger.info(f"🔍 SCOPE MERGE: After merge, merged_scopes['StreamingDefaults'] = {merged_scopes.get('StreamingDefaults')}")

        # CRITICAL: Propagate scope to all extracted nested configs
        # If PipelineConfig has scope_id=plate_path, then all its nested configs
        # (LazyWellFilterConfig, LazyZarrConfig, etc.) should also have scope_id=plate_path
        # This ensures the resolver can prioritize based on scope specificity
        #
        # IMPORTANT: Only apply scope to configs that were NEWLY extracted from this context,
        # not configs that already exist in parent scopes (which should keep their parent scope)
        #
        # CRITICAL: We ALWAYS set scopes for nested configs, even when scope_id=None
        # This is because GlobalPipelineConfig has scope_id=None, and we need to track
        # that its nested configs (WellFilterConfig, etc.) also have scope=None
        # Apply scope to ONLY newly extracted configs from this context
        # Use current_context_configs to identify configs that were extracted from the current
        # context object (before merging with parent), not inherited from parent contexts
        logger.debug(f"🔍 CONTEXT MANAGER: current_context_configs = {current_context_configs}")
        logger.debug(f"🔍 CONTEXT MANAGER: parent_scopes = {parent_scopes}")
        logger.debug(f"🔍 CONTEXT MANAGER: About to loop over current_context_configs, len={len(current_context_configs)}")
        for config_name in current_context_configs:
            # CRITICAL: Configs extracted from the CURRENT context object should get the current scope_id
            # UNLESS a more specific scope already exists in merged_scopes
            #
            # Example 1: PipelineConfig (scope=plate_path) extracts LazyWellFilterConfig
            # Even though WellFilterConfig exists in parent with scope=None,
            # LazyWellFilterConfig should get scope=plate_path (not None)
            #
            # Example 2: GlobalPipelineConfig (scope=None) extracts StreamingDefaults
            # If StreamingDefaults already has scope=plate_path from PipelineConfig's nested managers,
            # DON'T overwrite with None - keep the more specific plate scope
            existing_scope = merged_scopes.get(config_name)

            if config_name == 'StreamingDefaults':
                logger.info(f"🔍 SCOPE LOOP: Processing {config_name}, existing_scope={existing_scope}, scope_id={scope_id}")

            if existing_scope is None and scope_id is not None:
                # Existing scope is None (global), new scope is specific (plate/step) - overwrite
                merged_scopes[config_name] = scope_id
                logger.info(f"🔍 SCOPE ASSIGN: {config_name} -> {scope_id} (was None)")
            elif existing_scope is not None and scope_id is None:
                # Existing scope is specific, new scope is None - DON'T overwrite
                logger.info(f"🔍 SCOPE PRESERVE: {config_name} keeping {existing_scope} (not overwriting with None)")
            else:
                # Both None or both specific - use current scope_id
                merged_scopes[config_name] = scope_id
                logger.info(f"🔍 SCOPE ASSIGN: {config_name} -> {scope_id}")

        logger.debug(f"🔍 CONTEXT MANAGER: Setting scopes: {merged_scopes}, scope_id: {scope_id}")
    else:
        merged_scopes = current_config_scopes.get()

    # Set context, extracted configs, context stack, and scope information atomically
    logger.info(
        f"🔍 CONTEXT MANAGER: SET SCOPES FINAL for {type(obj).__name__}: "
        f"{len(merged_scopes)} entries, scope_id={scope_id}"
    )
    if 'StreamingDefaults' in merged_scopes:
        logger.info(f"🔍 CONTEXT MANAGER: merged_scopes['StreamingDefaults'] = {merged_scopes.get('StreamingDefaults')}")
    logger.debug(f"🔍 CONTEXT MANAGER: About to set current_config_scopes.set(merged_scopes) where merged_scopes = {merged_scopes}")
    token = current_temp_global.set(merged_config)
    extracted_token = current_extracted_configs.set(extracted)
    stack_token = current_context_stack.set(new_stack)
    scopes_token = current_config_scopes.set(merged_scopes)
    scope_id_token = current_scope_id.set(scope_id) if scope_id is not None else None
    try:
        yield
    finally:
        current_temp_global.reset(token)
        current_extracted_configs.reset(extracted_token)
        current_context_stack.reset(stack_token)
        current_config_scopes.reset(scopes_token)
        if scope_id_token is not None:
            current_scope_id.reset(scope_id_token)


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


# Cache for extract_all_configs to avoid repeated extraction
# Content-based cache: (type_name, frozen_field_values) -> extracted_configs
_extract_configs_cache: Dict[Tuple, Dict[str, Any]] = {}

def _make_cache_key_for_dataclass(obj) -> Tuple:
    """Create content-based cache key for frozen dataclass.

    CRITICAL: The cache key must include the ACTUAL TYPE of nested dataclasses,
    not just their content. This is because LazyWellFilterConfig and WellFilterConfig
    can have the same field values but are different types, and extract_all_configs()
    needs to return different results for them.
    """
    if not is_dataclass(obj):
        return (id(obj),)  # Fallback to identity for non-dataclasses

    # Build tuple of (type_name, field_values)
    # CRITICAL: Use the ACTUAL type, not just __name__, to distinguish Lazy vs BASE
    type_key = type(obj)  # Use the actual type object, not just the name
    field_values = []
    for field_info in fields(obj):
        try:
            value = object.__getattribute__(obj, field_info.name)
            # Recursively handle nested dataclasses
            if is_dataclass(value):
                # CRITICAL: Include the TYPE of the nested dataclass in the cache key
                # This ensures LazyWellFilterConfig and WellFilterConfig have different keys
                value = (type(value), _make_cache_key_for_dataclass(value))
            elif isinstance(value, (list, tuple)):
                # Convert lists to tuples for hashability
                value = tuple(
                    (type(item), _make_cache_key_for_dataclass(item)) if is_dataclass(item) else item
                    for item in value
                )
            elif isinstance(value, dict):
                # Convert dicts to sorted tuples
                value = tuple(sorted(value.items()))
            field_values.append((field_info.name, value))
        except AttributeError:
            field_values.append((field_info.name, None))

    return (type_key, tuple(field_values))

def extract_all_configs(context_obj, bypass_lazy_resolution: bool = False) -> Dict[str, Any]:
    """
    Extract all config instances from a context object using type-driven approach.

    This function leverages dataclass field type annotations to efficiently extract
    config instances, avoiding string matching and runtime attribute scanning.

    PERFORMANCE: Results are cached by CONTENT (not identity) to handle frozen dataclasses
    that are recreated with dataclasses.replace().

    Args:
        context_obj: Object to extract configs from (orchestrator, merged config, etc.)
        bypass_lazy_resolution: If True, use object.__getattribute__() to get raw values
                               without triggering lazy resolution. This preserves the
                               original lazy config values before context merging.

    Returns:
        Dict mapping config type names to config instances
    """
    if context_obj is None:
        return {}

    # Build content-based cache key (include bypass flag in key)
    cache_key = (_make_cache_key_for_dataclass(context_obj), bypass_lazy_resolution)

    # Check cache first
    if cache_key in _extract_configs_cache:
        logger.debug(f"🔍 CACHE HIT: extract_all_configs for {type(context_obj).__name__} (bypass={bypass_lazy_resolution})")
        # CRITICAL: Return a COPY of the cached dict to prevent mutations from affecting the cache
        return dict(_extract_configs_cache[cache_key])

    logger.debug(f"🔍 CACHE MISS: extract_all_configs for {type(context_obj).__name__} (bypass={bypass_lazy_resolution}), cache size={len(_extract_configs_cache)}")
    configs = {}

    # Include the context object itself if it's a dataclass
    if is_dataclass(context_obj):
        configs[type(context_obj).__name__] = context_obj
        logger.info(f"🔍 EXTRACT: Added self {type(context_obj).__name__} to configs")

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
                    # CRITICAL: ALWAYS use object.__getattribute__() to get RAW nested configs
                    # We want to extract the actual config instances stored in this object,
                    # not resolved values from parent contexts
                    # The bypass_lazy_resolution flag controls whether we convert Lazy to BASE,
                    # not whether we use getattr vs object.__getattribute__
                    field_value = object.__getattribute__(context_obj, field_name)

                    if field_value is not None:
                        # Use the actual instance type, not the annotation type
                        # This handles cases where field is annotated as base class but contains subclass
                        instance_type = type(field_value)

                        # Log extraction of WellFilterConfig for debugging
                        if 'WellFilterConfig' in instance_type.__name__:
                            logger.debug(f"🔍 EXTRACT: Extracting {instance_type.__name__} from {type(context_obj).__name__}.{field_name} (bypass={bypass_lazy_resolution})")
                            logger.debug(f"🔍 EXTRACT: Instance ID: {id(field_value)}")
                            if hasattr(field_value, 'well_filter'):
                                try:
                                    raw_wf = object.__getattribute__(field_value, 'well_filter')
                                    logger.debug(f"🔍 EXTRACT: {instance_type.__name__}.well_filter RAW={raw_wf}")
                                except AttributeError:
                                    logger.debug(f"🔍 EXTRACT: {instance_type.__name__}.well_filter RAW=<no attribute>")

                        if 'WellFilterConfig' in instance_type.__name__ or 'PipelineConfig' in instance_type.__name__:
                            logger.info(f"🔍 EXTRACT: field_name={field_name}, instance_type={instance_type.__name__}, context_obj={type(context_obj).__name__}, bypass={bypass_lazy_resolution}, value={field_value}")
                        configs[instance_type.__name__] = field_value

                        logger.info(f"🔍 EXTRACT: Extracted config {instance_type.__name__} from field {field_name} on {type(context_obj).__name__} (bypass={bypass_lazy_resolution})")

                except AttributeError:
                    # Field doesn't exist on instance (shouldn't happen with dataclasses)
                    logger.debug(f"Field {field_name} not found on {type(context_obj).__name__}")
                    continue

    # For non-dataclass objects (orchestrators, etc.), extract dataclass attributes
    else:
        _extract_from_object_attributes_typed(context_obj, configs)

    logger.info(f"🔍 EXTRACT: Extracted {len(configs)} configs from {type(context_obj).__name__}: {list(configs.keys())}")
    logger.info(f"🔍 EXTRACT: Config types: {[(k, type(v).__name__) for k, v in configs.items()]}")

    # Store in cache before returning (using content-based key)
    _extract_configs_cache[cache_key] = configs

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
                    logger.debug(f"Extracted config {type(attr_value).__name__} from attribute {attr_name} on {type(obj).__name__}")

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
