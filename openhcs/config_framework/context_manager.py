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

# Context type stack - tracks the types of objects pushed via config_context()
# This enables generic hierarchy inference without hardcoding specific types
# The stack is a tuple of types, ordered from outermost to innermost context
context_type_stack = contextvars.ContextVar('context_type_stack', default=())

# Dispatch cycle cache - caches expensive computations within a single field change dispatch
# This avoids redundant computation when refreshing multiple siblings
_dispatch_cycle_cache: contextvars.ContextVar[dict | None] = contextvars.ContextVar(
    '_dispatch_cycle_cache', default=None
)


@contextmanager
def dispatch_cycle():
    """Context manager for a dispatch cycle. Enables caching of computed values.

    Usage in field_change_dispatcher.py:
        with dispatch_cycle():
            # sibling refreshes can share cached GLOBAL layer
            for sibling in siblings:
                refresh_placeholder(sibling, field_name)

    The cache is automatically cleared when the context manager exits.
    """
    cache: dict = {}
    token = _dispatch_cycle_cache.set(cache)
    try:
        yield cache
    finally:
        _dispatch_cycle_cache.reset(token)


def get_dispatch_cache() -> dict | None:
    """Get the current dispatch cycle cache, or None if not in a cycle."""
    return _dispatch_cycle_cache.get()


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

    # Track the type in the context type stack
    current_types = context_type_stack.get()
    new_types = current_types + (type(obj),) if obj is not None else current_types

    merged_token = current_temp_global.set(merged_config)
    type_token = context_type_stack.set(new_types)
    try:
        yield
    finally:
        current_temp_global.reset(merged_token)
        context_type_stack.reset(type_token)


def get_context_type_stack():
    """
    Get the current stack of context types (outermost to innermost).

    This enables generic hierarchy inference without hardcoding specific types.
    The stack represents the order in which config_context() calls were nested.

    Returns:
        Tuple of types representing the context hierarchy.
        Empty tuple if no context is active.

    Example:
        with config_context(global_config):      # stack = (GlobalPipelineConfig,)
            with config_context(pipeline_config):  # stack = (GlobalPipelineConfig, PipelineConfig)
                with config_context(step):         # stack = (GlobalPipelineConfig, PipelineConfig, Step)
                    types = get_context_type_stack()
                    # types == (GlobalPipelineConfig, PipelineConfig, Step)
    """
    return context_type_stack.get()


def _normalize_type(t):
    """Normalize a type by getting its base type if it's a lazy variant.

    This function is defined here to avoid circular imports with lazy_factory.
    The actual get_base_type_for_lazy is imported lazily when needed.
    """
    try:
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
        return get_base_type_for_lazy(t) or t
    except ImportError:
        return t


def _is_global_type(t):
    """Check if a type is a global config type.

    This function is defined here to avoid circular imports with lazy_factory.
    """
    try:
        from openhcs.config_framework.lazy_factory import is_global_config_type
        return is_global_config_type(t)
    except ImportError:
        return False


# Hierarchy registry - built from active form managers
# Maps: child_type -> parent_type (normalized base types)
# This is populated by ParameterFormManager when it registers
_known_hierarchy: dict = {}


def get_root_from_scope_key(scope_key: str) -> str:
    """Extract root (plate path) from scope_key for visibility checks.

    scope_key format:
    - Pipeline-level: just plate path (e.g., "/path/to/plate")
    - Step-level: plate_path::step_token (e.g., "/path/to/plate::step_a")
    - Global: empty string

    Returns the portion before "::" (or the whole string if no "::" present).
    """
    if not scope_key:
        return ""
    return scope_key.split("::")[0]


def is_scope_affected(target_scope_id: str | None, editing_scope_id: str | None) -> bool:
    """Check if target scope is affected by edit at editing scope.

    Uses scope_id hierarchy - no type introspection needed:
    - None/"" (global) → affects all
    - "plate_path" (pipeline) → affects same plate + all its steps
    - "plate_path::token" (step) → affects only that step

    Args:
        target_scope_id: The scope being checked for affectedness (None = global)
        editing_scope_id: The scope where the edit occurred (None = global)

    Returns:
        True if target should refresh when editing_scope changes
    """
    # Normalize None to empty string
    target = target_scope_id or ""
    editing = editing_scope_id or ""

    # Global edit affects all
    if not editing:
        return True

    # Different plate roots = not affected
    target_root = get_root_from_scope_key(target)
    editing_root = get_root_from_scope_key(editing)
    if target_root != editing_root:
        return False

    # Same root: parent affects children, not vice versa
    # editing="plate" affects target="plate::step" ✓
    # editing="plate::step" affects target="plate" ✗
    return target == editing or target.startswith(editing + "::")


def _normalize_type_for_hierarchy(t):
    """Normalize a type for hierarchy registry, but preserve lazy-global distinction.

    Normalization maps lazy types to their base types (e.g., LazyPathPlanningConfig → PathPlanningConfig).
    However, PipelineConfig → GlobalPipelineConfig is a special case: they represent DISTINCT
    hierarchy levels (pipeline overrides vs global defaults), so we must NOT collapse them.

    Rule: If normalization would produce a global type from a non-global type, keep the original.
    """
    normalized = _normalize_type(t)
    # Don't collapse lazy-to-global - they're distinct hierarchy levels
    if _is_global_type(normalized) and not _is_global_type(t):
        return t
    return normalized


def register_hierarchy_relationship(context_obj_type, object_instance_type):
    """Register that context_obj_type is the parent of object_instance_type in the hierarchy.

    Called by ParameterFormManager when a root manager registers.
    This builds up the known hierarchy from actual usage patterns.

    Args:
        context_obj_type: The parent/context type (e.g., PipelineConfig for Step editor)
        object_instance_type: The child type being edited (e.g., Step)

    Note:
        Types are normalized to base types (e.g., LazyPathPlanningConfig → PathPlanningConfig),
        but lazy-to-global normalization is prevented to preserve distinct hierarchy levels
        (PipelineConfig stays as PipelineConfig, not collapsed to GlobalPipelineConfig).
    """
    if context_obj_type is None or object_instance_type is None:
        return

    parent_base = _normalize_type_for_hierarchy(context_obj_type)
    child_base = _normalize_type_for_hierarchy(object_instance_type)

    if parent_base != child_base:
        _known_hierarchy[child_base] = parent_base
        logger.debug(f"Registered hierarchy: {parent_base.__name__} -> {child_base.__name__}")


def unregister_hierarchy_relationship(object_instance_type):
    """Remove a type from the hierarchy registry when its editor closes.

    Args:
        object_instance_type: The type to remove from the registry
    """
    child_base = _normalize_type_for_hierarchy(object_instance_type)
    if child_base in _known_hierarchy:
        del _known_hierarchy[child_base]
        logger.debug(f"Unregistered hierarchy for: {child_base.__name__}")


def get_ancestors_from_hierarchy(target_type):
    """Get all ancestor types for target_type by walking up the known hierarchy.

    Returns ancestors in order from outermost to innermost (excluding target_type itself).

    Args:
        target_type: The type to find ancestors for

    Returns:
        List of ancestor types in hierarchy order (grandparent, parent, ...)
    """
    target_base = _normalize_type_for_hierarchy(target_type)
    ancestors = []

    # Walk up the hierarchy
    current = target_base
    visited = set()
    while current in _known_hierarchy:
        if current in visited:
            # Cycle detected - stop
            break
        visited.add(current)
        parent = _known_hierarchy[current]
        ancestors.append(parent)
        current = parent

    # Reverse so outermost is first
    ancestors.reverse()
    return ancestors


def get_normalized_stack():
    """
    Get the context type stack with normalized (base) types, excluding global configs.

    Returns:
        List of base types in hierarchy order (outermost to innermost),
        with global config types filtered out.
    """
    canonical_stack = get_context_type_stack()
    normalized = []
    for t in canonical_stack:
        base_t = _normalize_type(t)
        if not _is_global_type(base_t):
            normalized.append(base_t)
    return normalized


def get_types_before_in_stack(target_type):
    """
    Get all non-global types that come before target_type in the hierarchy.

    First tries the active context_type_stack (for resolution during config_context),
    then falls back to the known hierarchy registry (for cross-window updates).

    Args:
        target_type: The type to find ancestors for (will be normalized)

    Returns:
        List of base types that come before target_type in the hierarchy.
        Empty list if no ancestors found.
    """
    # First try active context stack
    normalized_stack = get_normalized_stack()
    if normalized_stack:
        target_base = _normalize_type(target_type)

        # Find target's position
        target_index = -1
        for i, base_t in enumerate(normalized_stack):
            if base_t == target_base:
                target_index = i
                break

        if target_index > 0:
            return normalized_stack[:target_index]

    # Fall back to known hierarchy registry
    return get_ancestors_from_hierarchy(target_type)


def is_ancestor_in_context(ancestor_type, descendant_type):
    """
    Check if ancestor_type comes before descendant_type in the context hierarchy.

    This determines whether changes to ancestor_type should affect descendant_type.

    Args:
        ancestor_type: The potential ancestor type
        descendant_type: The potential descendant type

    Returns:
        True if ancestor_type is an ancestor of descendant_type,
        False otherwise.
    """
    from openhcs.config_framework.lazy_factory import get_base_type_for_lazy

    # Check 1: Is ancestor_type the lazy base of descendant_type?
    # This handles GlobalPipelineConfig → PipelineConfig relationship
    # PipelineConfig is a lazy version of GlobalPipelineConfig
    descendant_base = get_base_type_for_lazy(descendant_type)
    if descendant_base is not None and descendant_base == ancestor_type:
        return True

    # Check 2: Normalize for comparison (handles nested lazy configs like LazyPathPlanningConfig)
    ancestor_base = _normalize_type(ancestor_type)
    descendant_normalized = _normalize_type(descendant_type)

    # Check 3: Active context stack (uses normalized types)
    normalized_stack = get_normalized_stack()
    if normalized_stack:
        ancestor_index = -1
        descendant_index = -1
        for i, base_t in enumerate(normalized_stack):
            if base_t == ancestor_base:
                ancestor_index = i
            if base_t == descendant_normalized:
                descendant_index = i

        if ancestor_index >= 0 and descendant_index >= 0:
            return ancestor_index < descendant_index

    # Check 4: Known hierarchy registry (uses actual types, not normalized)
    ancestors = get_ancestors_from_hierarchy(descendant_type)
    # Check if ancestor_type OR its normalized form is in the ancestor list
    return ancestor_type in ancestors or ancestor_base in [_normalize_type(a) for a in ancestors]


def is_same_type_in_context(type_a, type_b):
    """
    Check if two types are the same when normalized.

    Handles lazy vs base type equivalence.

    Args:
        type_a: First type to compare
        type_b: Second type to compare

    Returns:
        True if both types normalize to the same base type.
    """
    return _normalize_type(type_a) == _normalize_type(type_b)


# ============================================================================
# Context Stack Building (for UI placeholder resolution)
# ============================================================================


def _inject_context_layer(
    stack,
    t: type | None,
    values: dict | None,
    stored: object | None,
) -> None:
    """
    Inject a context layer into the stack.

    Handles dataclass instantiation with SimpleNamespace fallback.
    For types that can't be reconstructed (e.g., FunctionStep needs 'func' arg),
    injects stored object + SimpleNamespace so type tracking works and live values win.

    Args:
        stack: ExitStack to inject into
        t: Type to instantiate (None = use SimpleNamespace)
        values: Dict of values to use (None = use stored only)
        stored: Stored object to fall back to (None = no fallback)
    """
    from types import SimpleNamespace

    if values is None:
        if stored is not None:
            stack.enter_context(config_context(stored))
        return

    # Have values - try to instantiate as dataclass, fall back to SimpleNamespace
    if t is not None and is_dataclass(t):
        try:
            stack.enter_context(config_context(t(**values)))
            return
        except Exception:
            # Dataclass ctor failed (e.g., missing required args not in form)
            # Inject stored (for type tracking) + SimpleNamespace (for values)
            if stored is not None:
                stack.enter_context(config_context(stored))
            stack.enter_context(config_context(SimpleNamespace(**values)))
            return

    # Non-dataclass or no type - use SimpleNamespace
    stack.enter_context(config_context(SimpleNamespace(**values)))


def build_context_stack(
    context_obj: object | None,
    object_instance: object,
    live_values: dict[type, dict] | None = None,
):
    """
    Build a complete context stack for placeholder resolution.

    This is the framework-agnostic function for building context stacks. It can
    be called from any UI framework (PyQt6, Textual, etc.) and returns an ExitStack
    with the proper layer order.

    Layer order (innermost to outermost when entered):
    1. Global context layer (live from editor OR thread-local)
    2. Intermediate layers from live_values (via get_types_before_in_stack())
    3. Parent context from context_obj
    4. Overlay from current form values (included in live_values)

    Args:
        context_obj: Parent context object (e.g., PipelineConfig for Step editor), or None for root
        object_instance: The object being edited (type used to infer global editing mode)
        live_values: Dict mapping types to their current field values.
                     Merges cross-window live context + current form overlay.
                     Caller is responsible for merging these before calling.

    Returns:
        ExitStack with all context layers entered. Caller must manage the stack lifecycle.
    """
    from contextlib import ExitStack
    from openhcs.config_framework.lazy_factory import GlobalConfigBase

    stack = ExitStack()
    obj_type = type(object_instance)

    # Infer global editing mode from object_instance type
    is_global_config_editing = isinstance(object_instance, GlobalConfigBase)
    global_config_type = obj_type if is_global_config_editing else None

    ctx_type_name = type(context_obj).__name__ if context_obj else "None"
    obj_type_name = obj_type.__name__
    live_val_types = [t.__name__ for t in live_values.keys()] if live_values else []
    logger.info(f"🔧 build_context_stack: ctx={ctx_type_name}, obj={obj_type_name}, live_values={live_val_types[:5]}{'...' if len(live_val_types) > 5 else ''}")

    # 1. Global context layer
    global_layer = _get_global_context_layer(live_values, is_global_config_editing, global_config_type)
    if global_layer is not None:
        stack.enter_context(config_context(global_layer, mask_with_none=is_global_config_editing))

    # 2-3. Unified parent chain (ancestors + immediate parent)
    if context_obj is not None:
        context_type = type(context_obj)
        ancestor_types = get_types_before_in_stack(context_type) if live_values else []
        parent_chain = ancestor_types + [context_type]

        for t in parent_chain:
            if _is_global_type(t):
                continue
            layer_values = _find_live_values_for_type(t, live_values) if live_values else None
            stored = context_obj if t == context_type else None
            _inject_context_layer(stack, t, layer_values, stored)

    # 4. Overlay from current form values (included in live_values under obj_type)
    overlay = _find_live_values_for_type(obj_type, live_values) if live_values else None
    if overlay is not None:
        _inject_context_layer(stack, obj_type, overlay, None)

    return stack


def _get_global_context_layer(
    live_context: dict | None,
    is_global_config_editing: bool,
    global_config_type: type | None,
) -> object | None:
    """
    Get the global context layer for the stack.

    Priority:
    1. If editing global config, use static defaults (mask_with_none will mask thread-local)
    2. If live_context has a global config, use that (from another open editor)
    3. Fall back to thread-local global config

    PERFORMANCE OPTIMIZATION: Within a dispatch cycle, the GLOBAL layer is cached
    since it's the same for all sibling refreshes.

    Args:
        live_context: Dict mapping types to their live values
        is_global_config_editing: True if editing a global config
        global_config_type: The global config type

    Returns:
        Global config instance to use, or None if not available
    """
    cache = get_dispatch_cache()
    cache_key = ('global_layer', is_global_config_editing, global_config_type)
    if cache is not None and cache_key in cache:
        logger.info(f"  🚀 GLOBAL layer CACHE HIT")
        return cache[cache_key]

    layer = None

    # 1) Global config editing → fresh instance (mask thread-local when entering)
    if is_global_config_editing and global_config_type is not None:
        try:
            layer = global_config_type()
        except Exception:
            layer = None

    # 2) Live global from other window
    if layer is None:
        layer = _find_live_global(live_context)

    # 3) Fallback to thread-local base
    if layer is None:
        layer = get_base_global_config()

    if cache is not None:
        cache[cache_key] = layer
        logger.info(f"  📦 GLOBAL layer cached")

    return layer


def _find_live_global(live_context: dict | None) -> object | None:
    """Find and instantiate a global config from live_context if present."""
    if not live_context:
        return None

    from openhcs.config_framework.lazy_factory import is_global_config_type

    for config_type, config_values in live_context.items():
        if is_global_config_type(config_type):
            try:
                return config_type(**config_values)
            except Exception:
                continue
    return None





def _find_live_values_for_type(target_type: type, live_context: dict) -> dict | None:
    """
    Find live values for a target type in live_context.

    Handles type normalization (lazy vs base types) AND inheritance.
    For sibling inheritance, a StepWellFilterConfig's values should be
    usable when resolving WellFilterConfig's placeholders.

    IMPORTANT: Prefers subclass matches over exact matches.
    This ensures StepWellFilterConfig values (with concrete value) are used
    for WellFilterConfig resolution, not WellFilterConfig values (with None).

    Args:
        target_type: The type to find values for
        live_context: Dict mapping types to their live values

    Returns:
        Dict of field values, or None if not found
    """
    target_base = _normalize_type(target_type)
    logger.info(f"_find_live_values_for_type: target={target_type.__name__} -> base={target_base.__name__}")
    logger.info(f"_find_live_values_for_type: live_context has {len(live_context)} types")

    # Pass 0: exact type match without normalization (prefer most specific)
    for config_type, config_values in live_context.items():
        if config_type == target_type:
            logger.info(f"_find_live_values_for_type: ✅ exact type match for {config_type.__name__}")
            return config_values

    # First pass: look for subclass match (more specific wins) after normalization
    # e.g., StepWellFilterConfig values for WellFilterConfig resolution
    for config_type, config_values in live_context.items():
        config_base = _normalize_type(config_type)
        try:
            if config_base != target_base and issubclass(config_base, target_base):
                logger.info(f"_find_live_values_for_type: ✅ using {config_base.__name__} values for {target_base.__name__} (subclass)")
                return config_values
        except TypeError:
            pass  # Not a class

    # Second pass: exact type match (after normalization)
    for config_type, config_values in live_context.items():
        config_base = _normalize_type(config_type)
        if config_base == target_base:
            logger.info(f"_find_live_values_for_type: ✅ exact match for {target_base.__name__}")
            return config_values

    logger.warning(f"_find_live_values_for_type: ❌ no match for {target_base.__name__}")
    return None


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
                        # CRITICAL: Use base type for lazy configs so MRO matching works
                        # LazyWellFilterConfig should be stored as WellFilterConfig
                        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
                        instance_type = type(field_value)
                        base_type = get_base_type_for_lazy(instance_type) or instance_type
                        configs[base_type.__name__] = field_value

                        logger.debug(f"Extracted config {base_type.__name__} from field {field_name}")

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
                    # CRITICAL: Use base type for lazy configs so MRO matching works
                    from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
                    instance_type = type(attr_value)
                    base_type = get_base_type_for_lazy(instance_type) or instance_type
                    configs[base_type.__name__] = attr_value
                    logger.debug(f"Extracted config {base_type.__name__} from attribute {attr_name}")

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
