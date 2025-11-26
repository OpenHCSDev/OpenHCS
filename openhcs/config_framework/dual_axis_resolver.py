"""
Generic dual-axis resolver for lazy configuration inheritance.

This module provides the core inheritance resolution logic as a pure function,
supporting both context hierarchy (X-axis) and sibling inheritance (Y-axis).

The resolver is completely generic and has no application-specific dependencies.
"""

import logging
from enum import Enum
from typing import Any, Dict, Type, Optional, Callable
from dataclasses import is_dataclass

logger = logging.getLogger(__name__)


class ScopeFilterMode(Enum):
    """Scope filtering strategies for different use cases.

    Each mode encapsulates a predicate function that determines whether a manager
    with a given scope_id should be included given a filter_scope.

    Polymorphic dispatch via enum value → predicate mapping eliminates if/else branching.
    Callers use factory methods to get the appropriate mode for their use case.

    Use Cases:
        INCLUDE_ALL: No filtering - include all managers (global + all scoped)
                     Used for window close snapshots where pipeline editor needs
                     to see step editor values to detect unsaved changes.

        BIDIRECTIONAL: Include managers in the same hierarchy (parent, child, or same)
                       Used for value collection where we want all related values.

        STRICT_HIERARCHY: Only include managers at same level or LESS specific
                          Used for scopes_dict building to prevent scope contamination.
    """
    INCLUDE_ALL = "include_all"
    BIDIRECTIONAL = "bidirectional"
    STRICT_HIERARCHY = "strict_hierarchy"

    @classmethod
    def for_value_collection(cls, scope_filter) -> 'ScopeFilterMode':
        """Get mode for value collection. None filter → INCLUDE_ALL, otherwise BIDIRECTIONAL."""
        return (cls.INCLUDE_ALL, cls.BIDIRECTIONAL)[scope_filter is not None]

    @classmethod
    def for_scopes_dict(cls) -> 'ScopeFilterMode':
        """Get mode for scopes dict building. Always STRICT_HIERARCHY."""
        return cls.STRICT_HIERARCHY

    def should_include(self, manager_scope: Optional[str], filter_scope) -> bool:
        """Polymorphic dispatch - check if manager should be included.

        Handles filter_scope normalization (Path → str) internally.
        """
        # Normalize Path → str, pass str/None through unchanged
        filter_str = {True: filter_scope, False: str(filter_scope)}.get(
            filter_scope is None or isinstance(filter_scope, str), str(filter_scope)
        )
        return _SCOPE_FILTER_PREDICATES[self.value](manager_scope, filter_str)


# Predicate dispatch table - module level to avoid enum member issues
_SCOPE_FILTER_PREDICATES: Dict[str, Callable[[Optional[str], Optional[str]], bool]] = {}


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

    # COMPREHENSIVE LOGGING: Log resolution for ALL fields in PipelineConfig-related configs
    should_log = (
        'WellFilterConfig' in obj_type.__name__ or
        'StepWellFilterConfig' in obj_type.__name__ or
        'PipelineConfig' in obj_type.__name__ or
        field_name in ['well_filter', 'well_filter_mode', 'num_workers']
    )

    if should_log:
        logger.info(f"🔍 RESOLVER START: {obj_type.__name__}.{field_name}")
        logger.info(f"🔍 RESOLVER: available_configs has {len(available_configs)} items: {list(available_configs.keys())}")
        logger.info(f"🔍 RESOLVER: obj MRO = {[cls.__name__ for cls in obj_type.__mro__ if is_dataclass(cls)]}")

    # Step 1: Check concrete value in merged context for obj's type (HIGHEST PRIORITY)
    # CRITICAL: Context values take absolute precedence over inheritance blocking
    # The config_context() manager merges concrete values into available_configs
    for config_name, config_instance in available_configs.items():
        if type(config_instance) == obj_type:
            if should_log:
                logger.info(f"🔍 STEP 1: Found exact type match: {config_name} (type={type(config_instance).__name__})")
            try:
                # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                value = object.__getattribute__(config_instance, field_name)
                if should_log:
                    logger.info(f"🔍 STEP 1: {config_name}.{field_name} = {value}")
                if value is not None:
                    if should_log:
                        logger.info(f"🔍 STEP 1: RETURNING {value} from {config_name} (concrete value in context)")
                    return value
                else:
                    if should_log:
                        logger.info(f"🔍 STEP 1: {config_name}.{field_name} = None (not concrete)")
            except AttributeError:
                # Field doesn't exist on this config type
                if should_log:
                    logger.info(f"🔍 STEP 1: {config_name} has no field {field_name}")
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
            if should_log:
                logger.info(f"🔍 STEP 2: Found exact type match: {config_name} (type={type(config_instance).__name__})")
            try:
                field_value = object.__getattribute__(config_instance, field_name)
                if should_log:
                    logger.info(f"🔍 STEP 2: {config_name}.{field_name} = {field_value}")
                if field_value is not None:
                    # This exact type has a concrete value - use it, don't inherit
                    if should_log:
                        logger.info(f"🔍 FIELD-SPECIFIC BLOCKING: {obj_type.__name__}.{field_name} = {field_value} (concrete) - blocking inheritance")
                    return field_value
            except AttributeError:
                if should_log:
                    logger.info(f"🔍 STEP 2: {config_name} has no field {field_name}")
                continue

    # DEBUG: Log what we're trying to resolve
    if should_log:
        logger.info(f"🔍 RESOLVING {obj_type.__name__}.{field_name} - checking context and inheritance")
        logger.info(f"🔍 AVAILABLE CONFIGS: {list(available_configs.keys())}")
        logger.info(f"🔍 AVAILABLE CONFIG TYPES: {[type(v).__name__ for v in available_configs.values()]}")
        logger.info(f"🔍 MRO: {[cls.__name__ for cls in obj_type.__mro__ if is_dataclass(cls)]}")

    # Step 3: Y-axis inheritance within obj's MRO
    blocking_class = _find_blocking_class_in_mro(obj_type, field_name)

    if should_log:
        logger.info(f"🔍 Y-AXIS: Blocking class = {blocking_class.__name__ if blocking_class else 'None'}")

    for parent_type in obj_type.__mro__[1:]:
        if not is_dataclass(parent_type):
            continue

        if should_log:
            logger.info(f"🔍 Y-AXIS: Checking parent {parent_type.__name__}")

        # Check blocking logic
        if blocking_class and parent_type != blocking_class:
            if should_log:
                logger.info(f"🔍 Y-AXIS: Skipping {parent_type.__name__} (not blocking class)")
            continue

        if blocking_class and parent_type == blocking_class:
            # Check if blocking class has concrete value in available configs
            for config_name, config_instance in available_configs.items():
                if type(config_instance) == parent_type:
                    try:
                        # Use object.__getattribute__ to avoid triggering lazy __getattribute__ recursion
                        value = object.__getattribute__(config_instance, field_name)
                        if should_log:
                            logger.info(f"🔍 Y-AXIS: Blocking class {parent_type.__name__} has value {value}")
                        if value is None:
                            # Blocking class has None - inheritance blocked
                            if should_log:
                                logger.info(f"🔍 Y-AXIS: Blocking class has None - inheritance blocked")
                            break
                        else:
                            if should_log:
                                logger.info(f"🔍 Y-AXIS: RETURNING {value} from blocking class {parent_type.__name__}")
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
                    if should_log:
                        logger.info(f"🔍 Y-AXIS INHERITANCE: {parent_type.__name__}.{field_name} = {value}")
                    if value is not None:
                        if should_log:
                            logger.info(f"🔍 Y-AXIS INHERITANCE: RETURNING {value} from {parent_type.__name__}")
                        return value
                except AttributeError:
                    # Field doesn't exist on this config type
                    if should_log:
                        logger.info(f"🔍 Y-AXIS: {parent_type.__name__} has no field {field_name}")
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


def get_scope_specificity(scope_id: Optional[str]) -> int:
    """Calculate scope specificity for priority ordering.

    More specific scopes have higher values:
    - None (global): 0
    - "plate_path": 1
    - "plate_path::step": 2
    - "plate_path::step::nested": 3

    Args:
        scope_id: Scope identifier (None for global, string for scoped)

    Returns:
        Specificity level (higher = more specific)
    """
    if scope_id is None:
        return 0
    return scope_id.count('::') + 1


def is_scope_visible(manager_scope: Optional[str], filter_scope: Optional[str]) -> bool:
    """Check if manager_scope is visible/related to filter_scope.

    Returns True if the scopes are in the same hierarchy (same plate).
    This is used for finding managers that might be relevant to a scope.

    GENERIC SCOPE RULE: Works for any N-level hierarchy.

    Examples:
        >>> is_scope_visible(None, "plate")              # global visible to all
        True
        >>> is_scope_visible("plate", "plate")           # exact match
        True
        >>> is_scope_visible("plate", "plate::step")     # manager is parent of filter
        True
        >>> is_scope_visible("plate::step", "plate")     # manager is child of filter (same hierarchy)
        True
        >>> is_scope_visible("plate1::step", "plate2")   # different hierarchy
        False

    Args:
        manager_scope: Scope ID of the manager being checked
        filter_scope: Scope ID of the perspective we're checking from

    Returns:
        True if scopes are in the same hierarchy
    """
    # Global scope (None) is visible to everyone
    if manager_scope is None:
        return True

    # If filter is global (None), only global managers are visible
    if filter_scope is None:
        return False

    # Exact match
    if manager_scope == filter_scope:
        return True

    # Manager is parent of filter (less specific)
    # e.g., manager="plate", filter="plate::step" → manager is parent
    if filter_scope.startswith(f"{manager_scope}::"):
        return True

    # Manager is child of filter (more specific, but same hierarchy)
    # e.g., manager="plate::step", filter="plate" → same plate hierarchy
    if manager_scope.startswith(f"{filter_scope}::"):
        return True

    # Different hierarchies
    return False


def is_scope_at_or_above(manager_scope: Optional[str], filter_scope: Optional[str]) -> bool:
    """Check if manager_scope is at the same level or LESS SPECIFIC than filter_scope.

    Used for placeholder resolution to prevent scope contamination.
    Managers MORE SPECIFIC than filter are NOT visible.

    GENERIC SCOPE RULE: Works for any N-level hierarchy.

    Examples:
        >>> is_scope_at_or_above(None, "plate")           # global visible to all
        True
        >>> is_scope_at_or_above("plate", "plate")        # exact match
        True
        >>> is_scope_at_or_above("plate", "plate::step")  # manager is parent of filter
        True
        >>> is_scope_at_or_above("plate::step", "plate")  # manager is child of filter
        False

    Args:
        manager_scope: Scope ID of the manager being checked
        filter_scope: Scope ID of the perspective we're checking from

    Returns:
        True if manager_scope is at same level or less specific than filter_scope
    """
    # Global scope (None) is visible to everyone
    if manager_scope is None:
        return True

    # If filter is global (None), only global managers are visible
    if filter_scope is None:
        return False

    # Exact match - same scope level
    if manager_scope == filter_scope:
        return True

    # Manager is LESS SPECIFIC than filter (filter is a child of manager)
    # e.g., manager="plate", filter="plate::step" → manager is parent, visible
    if filter_scope.startswith(f"{manager_scope}::"):
        return True

    # Manager is MORE SPECIFIC than filter - NOT visible for placeholder resolution
    # e.g., manager="plate::step", filter="plate" → manager is child, NOT visible
    return False


# Initialize predicate dispatch table now that functions are defined
_SCOPE_FILTER_PREDICATES.update({
    "include_all": lambda _m, _f: True,
    "bidirectional": is_scope_visible,
    "strict_hierarchy": is_scope_at_or_above,
})


def get_parent_scope(scope_id: Optional[str]) -> Optional[str]:
    """Get the parent scope of a given scope.

    GENERIC SCOPE RULE: Works for any N-level hierarchy.

    Examples:
        >>> get_parent_scope("/path/to/plate::step_0::nested")
        '/path/to/plate::step_0'
        >>> get_parent_scope("/path/to/plate::step_0")
        '/path/to/plate'
        >>> get_parent_scope("/path/to/plate")
        None
        >>> get_parent_scope(None)
        None

    Args:
        scope_id: Child scope identifier

    Returns:
        Parent scope identifier, or None if already at global scope
    """
    if scope_id is None:
        return None

    if '::' in scope_id:
        # Remove last segment: "/a/b::c::d" → "/a/b::c"
        return scope_id.rsplit('::', 1)[0]
    else:
        # No more segments, parent is global scope
        return None


def iter_scope_hierarchy(scope_id: Optional[str]):
    """Iterate through scope hierarchy from most specific to global.

    GENERIC SCOPE RULE: Works for any N-level hierarchy.

    Examples:
        >>> list(iter_scope_hierarchy("/path/to/plate::step_0::nested"))
        ['/path/to/plate::step_0::nested', '/path/to/plate::step_0', '/path/to/plate', None]
        >>> list(iter_scope_hierarchy("/path/to/plate"))
        ['/path/to/plate', None]
        >>> list(iter_scope_hierarchy(None))
        [None]

    Args:
        scope_id: Starting scope identifier

    Yields:
        Scope identifiers from most specific to global (None)
    """
    current = scope_id
    while True:
        yield current
        if current is None:
            break
        current = get_parent_scope(current)


def resolve_field_inheritance(
    obj,
    field_name: str,
    available_configs: Dict[str, Any],
    current_scope_id: Optional[str] = None,
    config_scopes: Optional[Dict[str, Optional[str]]] = None
) -> Any:
    """
    Simplified MRO-based inheritance resolution with scope-aware priority.

    ALGORITHM:
    1. Check if obj has concrete value for field_name in context
    2. Traverse obj's MRO from most to least specific
    3. For each MRO class, check if there's a config instance in context with concrete (non-None) value
    4. When multiple configs match, prioritize by scope specificity (plate > global)
    5. Return first concrete value found

    Args:
        obj: The object requesting field resolution
        field_name: Name of the field to resolve
        available_configs: Dict mapping config type names to config instances
        current_scope_id: Scope ID of the context requesting resolution (e.g., "/plate" or "/plate::step")
        config_scopes: Optional dict mapping config type names to their scope IDs

    Returns:
        Resolved field value or None if not found
    """
    obj_type = type(obj)

    if field_name in ['well_filter_mode', 'output_dir_suffix', 'num_workers']:
        logger.info(f"🔍 RESOLVER: {obj_type.__name__}.{field_name}")
        logger.info(f"🔍 RESOLVER: MRO = {[cls.__name__ for cls in obj_type.__mro__ if is_dataclass(cls)]}")
        logger.info(f"🔍 RESOLVER: available_configs keys = {list(available_configs.keys())}")
        logger.info(f"🔍 RESOLVER: current_scope_id = {current_scope_id}")
        logger.info(f"🔍 RESOLVER: config_scopes = {config_scopes}")

    # Step 1: Check if exact same type has concrete value in context
    for config_name, config_instance in available_configs.items():
        if type(config_instance) == obj_type:
            try:
                # CRITICAL: Always use object.__getattribute__() to avoid infinite recursion
                # Lazy configs store their raw values as instance attributes
                field_value = object.__getattribute__(config_instance, field_name)
                if field_name in ['well_filter_mode', 'output_dir_suffix', 'num_workers']:
                    logger.info(f"🔍 STEP 1: {config_name}.{field_name} = {field_value} (type match: {type(config_instance).__name__})")
                if field_value is not None:
                    if field_name in ['well_filter_mode', 'output_dir_suffix', 'num_workers']:
                        logger.info(f"🔍 STEP 1: RETURNING {field_value} from {config_name}")
                    return field_value
            except AttributeError:
                continue

    # Step 2: MRO-based inheritance - traverse MRO from most to least specific
    # For each class in the MRO, check if there's a config instance in context with concrete value
    for mro_class in obj_type.__mro__:
        if field_name in ['well_filter_mode', 'output_dir_suffix', 'num_workers']:
            logger.info(f"🔍 STEP 2: Checking MRO class {mro_class.__name__}")
        if not is_dataclass(mro_class):
            continue

        # Look for a config instance of this MRO class type in the available configs
        # CRITICAL: Prioritize lazy types over base types when both are present
        # This ensures PipelineConfig's LazyWellFilterConfig takes precedence over GlobalPipelineConfig's WellFilterConfig

        # First pass: Look for exact type match OR lazy type match
        # Collect ALL matches with their scope specificity for priority sorting
        lazy_matches = []  # List of (config_name, config_instance, scope_specificity)
        base_matches = []

        # CRITICAL: Calculate current resolution scope specificity for filtering
        # Configs can only see values from their own scope or LESS specific scopes
        # Example: GlobalPipelineConfig (specificity=0) should NOT see PipelineConfig (specificity=1) values
        current_specificity = get_scope_specificity(current_scope_id)

        for config_name, config_instance in available_configs.items():
            instance_type = type(config_instance)

            # Get scope specificity for this config
            # Normalize config name for scope lookup (LazyWellFilterConfig -> WellFilterConfig)
            normalized_name = config_name.replace('Lazy', '') if config_name.startswith('Lazy') else config_name
            if config_scopes:
                # Prefer normalized base name, but fall back to the exact name when scopes
                # were stored using lazy class names (e.g., LazyWellFilterConfig)
                config_scope = config_scopes.get(normalized_name)
                if config_scope is None:
                    config_scope = config_scopes.get(config_name)
            else:
                config_scope = None
            scope_specificity = get_scope_specificity(config_scope)

            # CRITICAL FIX: Skip configs from MORE SPECIFIC scopes than current resolution scope
            # This prevents scope contamination where PipelineConfig values leak into GlobalPipelineConfig
            # Scope hierarchy: Global (0) < Plate (1) < Step (2)
            # A config can only see its own scope level or less specific (lower number)
            if scope_specificity > current_specificity:
                if field_name in ['well_filter', 'well_filter_mode', 'output_dir_suffix', 'num_workers', 'enabled', 'persistent', 'host', 'port']:
                    logger.info(f"🔍 SCOPE FILTER: Skipping {config_name} (scope_specificity={scope_specificity} > current_specificity={current_specificity}) for field {field_name}")
                continue

            # Check exact type match
            if instance_type == mro_class:
                # Separate lazy and base types
                if instance_type.__name__.startswith('Lazy'):
                    if field_name == 'well_filter_mode' and mro_class.__name__ == 'WellFilterConfig':
                        logger.info(f"🔍 MATCHING: Exact match - {config_name} is lazy (scope={config_scope}, specificity={scope_specificity})")
                    lazy_matches.append((config_name, config_instance, scope_specificity))
                else:
                    if field_name == 'well_filter_mode' and mro_class.__name__ == 'WellFilterConfig':
                        logger.info(f"🔍 MATCHING: Exact match - {config_name} is base (scope={config_scope}, specificity={scope_specificity})")
                    base_matches.append((config_name, config_instance, scope_specificity))
            # Check if instance is base type of lazy MRO class (e.g., StepWellFilterConfig matches LazyStepWellFilterConfig)
            elif mro_class.__name__.startswith('Lazy') and instance_type.__name__ == mro_class.__name__[4:]:
                if field_name == 'well_filter_mode' and mro_class.__name__ == 'WellFilterConfig':
                    logger.info(f"🔍 MATCHING: Base type of lazy MRO - {config_name} (scope={config_scope}, specificity={scope_specificity})")
                base_matches.append((config_name, config_instance, scope_specificity))
            # Check if instance is lazy type of non-lazy MRO class (e.g., LazyStepWellFilterConfig matches StepWellFilterConfig)
            elif instance_type.__name__.startswith('Lazy') and mro_class.__name__ == instance_type.__name__[4:]:
                if field_name == 'well_filter_mode' and mro_class.__name__ == 'WellFilterConfig':
                    logger.info(f"🔍 MATCHING: Lazy type of non-lazy MRO - {config_name} (scope={config_scope}, specificity={scope_specificity})")
                lazy_matches.append((config_name, config_instance, scope_specificity))

        # Sort matches by scope specificity (highest first = most specific scope)
        lazy_matches.sort(key=lambda x: x[2], reverse=True)
        base_matches.sort(key=lambda x: x[2], reverse=True)

        if field_name in ['well_filter_mode', 'num_workers'] and mro_class.__name__ in ['WellFilterConfig', 'LazyWellFilterConfig', 'GlobalPipelineConfig', 'PipelineConfig']:
            logger.info(f"🔍 SORTED MATCHES for {mro_class.__name__}:")
            logger.info(f"🔍   Lazy matches (sorted by specificity): {[(name, spec) for name, _, spec in lazy_matches]}")
            logger.info(f"🔍   Base matches (sorted by specificity): {[(name, spec) for name, _, spec in base_matches]}")

        # Get the highest-priority matches
        lazy_match = lazy_matches[0][1] if lazy_matches else None
        base_match = base_matches[0][1] if base_matches else None

        # Prioritization logic:
        # CRITICAL: Always check BOTH lazy and base instances, prioritizing non-None values
        # This ensures we get class defaults from base instances even when MRO contains lazy types
        #
        # Example: LazyStepMaterializationConfig.output_dir_suffix
        # - MRO contains LazyPathPlanningConfig (lazy type)
        # - available_configs has LazyPathPlanningConfig (value=None) AND PathPlanningConfig (value="_openhcs")
        # - We should use PathPlanningConfig's "_openhcs" class default, not LazyPathPlanningConfig's None
        #
        # Strategy: Try lazy first (for context values), then base (for class defaults)
        matched_instance = None
        if lazy_match is not None:
            try:
                value = object.__getattribute__(lazy_match, field_name)
                if field_name == 'num_workers':
                    logger.info(f"🔍 STEP 2: Checking lazy_match {type(lazy_match).__name__}.{field_name} = {value}")
                if value is not None:
                    matched_instance = lazy_match
            except AttributeError:
                pass

        if matched_instance is None and base_match is not None:
            matched_instance = base_match

        if field_name in ['well_filter_mode', 'output_dir_suffix', 'num_workers']:
            if matched_instance is not None:
                logger.info(f"🔍 STEP 2: Found match for {mro_class.__name__}: {type(matched_instance).__name__}")
            else:
                logger.info(f"🔍 STEP 2: No match for {mro_class.__name__}")

        if matched_instance is not None:
            try:
                # CRITICAL: Always use object.__getattribute__() to avoid infinite recursion
                # Lazy configs store their raw values as instance attributes
                value = object.__getattribute__(matched_instance, field_name)
                if field_name in ['well_filter_mode', 'output_dir_suffix', 'num_workers']:
                    logger.info(f"🔍 STEP 2: {type(matched_instance).__name__}.{field_name} = {value}")
                if value is not None:
                    if field_name in ['well_filter_mode', 'output_dir_suffix', 'num_workers']:
                        logger.info(f"✅ RETURNING {value} from {type(matched_instance).__name__}")
                    return value
            except AttributeError:
                if field_name in ['well_filter_mode', 'output_dir_suffix', 'num_workers']:
                    logger.info(f"🔍 STEP 2: {type(matched_instance).__name__} has no field {field_name}")
                continue

    # Step 3: Class defaults as final fallback
    try:
        class_default = object.__getattribute__(obj_type, field_name)
        if field_name == 'num_workers':
            logger.info(f"🔍 STEP 3 FALLBACK: {obj_type.__name__}.{field_name} = {class_default} (from class default)")
        if class_default is not None:
            if field_name == 'num_workers':
                logger.info(f"❌ RETURNING CLASS DEFAULT {class_default}")
            return class_default
    except AttributeError:
        pass

    if field_name == 'num_workers':
        logger.info(f"❌ RETURNING None (no value found)")
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
