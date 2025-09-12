"""
Recursive implementation of dual-axis lazy resolution system.

This implements the proper recursive algorithm:
1. Check current instance for concrete value at THIS context level
2. Try Y-axis inheritance at THIS context level
3. If no resolution, recurse to PARENT context level
4. Continue until thread-local storage (which has concrete values)

Context hierarchy: specific → parent → global
Each level gets full dual-axis treatment before recursing to parent level.
"""

import inspect
import logging
from typing import Any, Optional, Type, List
from dataclasses import fields, is_dataclass

# Import existing components
from openhcs.core.lazy_config import get_base_type_for_lazy, LazyMethodBindings, _lazy_type_registry
from openhcs.core.field_path_detection import FieldPathDetector, FieldPathNavigator
from openhcs.core.composition_detection import discover_composition_hierarchy_from_instance
from openhcs.core.context.global_config import get_current_global_config

logger = logging.getLogger(__name__)


def _get_global_config_type_for_target(target_type: Type) -> Optional[Type]:
    """
    Get the global config type for a target type using the decorator factory relationships.

    This leverages the existing lazy type registry to find the global config type
    that was established when the target type was decorated.
    """
    # Find the lazy version of the target type (reverse lookup)
    for lazy_type, base_type in _lazy_type_registry.items():
        if base_type == target_type:
            # Create a temporary instance to access the stored global config type
            try:
                temp_instance = lazy_type()
                return getattr(temp_instance, '_global_config_type', None)
            except Exception:
                continue
    return None


class RecursiveContextualResolver:
    """
    Recursive dual-axis resolver that properly traverses context hierarchy.

    Algorithm:
    1. Check concrete value at current context level
    2. Try Y-axis inheritance at current context level
    3. If no resolution, recurse to parent context level
    4. Continue until thread-local storage

    Each context level gets full dual-axis treatment independently.
    """

    def __init__(self):
        self._resolution_cache = {}

    def resolve_field(self, lazy_instance, field_name: str) -> Any:
        """
        Resolve field using recursive dual-axis logic.

        Discovers context hierarchy and recursively resolves through levels.
        """
        # Get the base type for this lazy instance
        base_type = get_base_type_for_lazy(type(lazy_instance))
        if not base_type:
            return None

        if field_name == 'well_filter' and ('NapariStreamingConfig' in type(lazy_instance).__name__ or 'StepMaterializationConfig' in type(lazy_instance).__name__):
            print(f"🔍 RESOLVER DEBUG: Resolving {type(lazy_instance).__name__}.{field_name}, base_type = {base_type.__name__}")

        # CRITICAL: Check for static class field overrides first
        # If the base class has a concrete field override (different from parent classes),
        # use that instead of hierarchical inheritance
        static_override_value = self._check_static_override(base_type, field_name)
        if static_override_value is not None:
            if field_name == 'well_filter' and ('NapariStreamingConfig' in type(lazy_instance).__name__ or 'StepMaterializationConfig' in type(lazy_instance).__name__):
                print(f"🔍 RESOLVER DEBUG: Using static override = {static_override_value}")
            return static_override_value

        # Discover context hierarchy
        context_hierarchy = self._discover_context_hierarchy(base_type)
        if not context_hierarchy:
            logger.debug(f"No context hierarchy found for {base_type.__name__}.{field_name}")
            if field_name == 'well_filter' and ('NapariStreamingConfig' in type(lazy_instance).__name__ or 'StepMaterializationConfig' in type(lazy_instance).__name__):
                print(f"🔍 RESOLVER DEBUG: No context hierarchy found!")
            return None

        if field_name == 'well_filter' and ('NapariStreamingConfig' in type(lazy_instance).__name__ or 'StepMaterializationConfig' in type(lazy_instance).__name__):
            print(f"🔍 RESOLVER DEBUG: Found context hierarchy = {[type(ctx).__name__ for ctx in context_hierarchy]}")

        # Check cache first
        cache_key = (id(lazy_instance), field_name, tuple(id(ctx) for ctx in context_hierarchy))
        if cache_key in self._resolution_cache:
            return self._resolution_cache[cache_key]

        # Recursive resolution through context hierarchy
        if field_name == 'well_filter' and 'StepMaterializationConfig' in type(lazy_instance).__name__:
            print(f"🔍 RESOLVER DEBUG: Starting recursive resolution with hierarchy = {[type(ctx).__name__ for ctx in context_hierarchy]}")

        result = self._resolve_field_recursive(base_type, field_name, context_hierarchy)

        if field_name == 'well_filter' and ('NapariStreamingConfig' in type(lazy_instance).__name__ or 'StepMaterializationConfig' in type(lazy_instance).__name__):
            print(f"🔍 RESOLVER DEBUG: Resolved result = {result}")

        # Cache the result
        self._resolution_cache[cache_key] = result
        return result
    
    def _resolve_field_recursive(self, target_type: Type, field_name: str, context_hierarchy: List[Any]) -> Any:
        """
        Recursive dual-axis resolution through context hierarchy.

        Correct Algorithm (per context level):
        1. Check current field concrete at THIS level → if yes, return
        2. Check if field exists in parent context with concrete → if yes, return
        3. Exhaust Y-axis at THIS level → try inheritance within current context
        4. If Y-axis can't resolve at THIS level → go to parent context and repeat from step 1

        Args:
            target_type: The type to resolve for
            field_name: The field name to resolve
            context_hierarchy: List of contexts from most specific to least specific
        """
        if not context_hierarchy:
            logger.debug(f"No more context levels for {target_type.__name__}.{field_name}")

            # Final fallback: check for class defaults from blocking classes
            blocking_class = self._find_blocking_class_in_mro(target_type, field_name)
            if blocking_class:
                class_default = getattr(blocking_class, field_name, None)
                if class_default is not None:
                    logger.debug(f"Using class default from blocking class {blocking_class.__name__}: {class_default}")
                    return class_default

            return None

        current_context = context_hierarchy[0]  # Most specific level
        parent_context_hierarchy = context_hierarchy[1:]  # Parent contexts

        if field_name == 'well_filter' and target_type.__name__ == 'StepMaterializationConfig':
            print(f"🔍 RECURSIVE DEBUG: Resolving {target_type.__name__}.{field_name} at context level: {type(current_context).__name__}")

        logger.debug(f"Resolving {target_type.__name__}.{field_name} at context level: {type(current_context).__name__}")

        # STEP 1: Check concrete value at THIS context level
        concrete_value = self._get_concrete_value_at_level(current_context, target_type, field_name)
        if concrete_value is not None:
            if field_name == 'well_filter' and target_type.__name__ == 'StepMaterializationConfig':
                print(f"🔍 RECURSIVE DEBUG: Found concrete value at {type(current_context).__name__}: {concrete_value}")
            logger.debug(f"Found concrete value at {type(current_context).__name__}: {concrete_value}")
            return concrete_value

        # STEP 2: Check if field exists in parent context with concrete value
        if parent_context_hierarchy:
            parent_context = parent_context_hierarchy[0]
            parent_concrete_value = self._get_concrete_value_at_level(parent_context, target_type, field_name)
            if field_name == 'well_filter' and target_type.__name__ == 'StepMaterializationConfig':
                print(f"🔍 RECURSIVE DEBUG: Parent context {type(parent_context).__name__} returned: {parent_concrete_value}")
            if parent_concrete_value is not None:
                if field_name == 'well_filter' and target_type.__name__ == 'StepMaterializationConfig':
                    print(f"🔍 RECURSIVE DEBUG: Found concrete value in parent context {type(parent_context).__name__}: {parent_concrete_value}")
                logger.debug(f"Found concrete value in parent context {type(parent_context).__name__}: {parent_concrete_value}")
                return parent_concrete_value

        # STEP 3: Exhaust Y-axis at THIS context level only
        # Find the first blocking class in MRO (if any)
        blocking_class = self._find_blocking_class_in_mro(target_type, field_name)
        logger.debug(f"Blocking class for {target_type.__name__}.{field_name}: {blocking_class.__name__ if blocking_class else 'None'}")

        for parent_type in target_type.__mro__[1:]:
            if not is_dataclass(parent_type):
                continue

            logger.debug(f"Checking MRO class {parent_type.__name__} for {field_name}")

            # If we've reached the blocking class, check if it has a concrete value
            if blocking_class and parent_type == blocking_class:
                # First check context for instance value
                parent_value = self._get_concrete_value_at_level(current_context, parent_type, field_name)
                logger.debug(f"Blocking class {parent_type.__name__} context value: {parent_value}")

                # If context has None, the blocking class acts as a flag - inheritance blocked, must use context hierarchy
                if parent_value is None:
                    logger.debug(f"Blocking class {parent_type.__name__} has None in context - inheritance blocked, must use context hierarchy")
                    break  # Inheritance blocked - must go to context hierarchy
                else:
                    logger.debug(f"Inherited concrete value from blocking class {parent_type.__name__}: {parent_value}")
                    return parent_value

            # If we haven't reached the blocking class yet, skip (can't inherit from classes before the blocker)
            elif blocking_class and parent_type != blocking_class:
                logger.debug(f"Skipping {parent_type.__name__} - haven't reached blocking class {blocking_class.__name__} yet")
                continue

            # No blocking class, normal inheritance
            else:
                parent_value = self._get_concrete_value_at_level(current_context, parent_type, field_name)
                logger.debug(f"No blocking class - {parent_type.__name__} has value: {parent_value}")
                if parent_value is not None:
                    logger.debug(f"Inherited from {parent_type.__name__} at {type(current_context).__name__}: {parent_value}")
                    return parent_value

        # STEP 4: Y-axis can't resolve at this level - recurse to parent context
        logger.debug(f"No resolution at {type(current_context).__name__}, recursing to parent context")
        return self._resolve_field_recursive(target_type, field_name, parent_context_hierarchy)
    
    def _discover_context_hierarchy(self, target_type: Type) -> List[Any]:
        """
        Discover the full context hierarchy from most specific to least specific.

        Returns: [specific_context, parent_context, global_context]
        """
        hierarchy = []

        # Use existing context discovery to find the most specific context
        most_specific_context = ContextDiscovery.discover_context(target_type)
        if most_specific_context:
            hierarchy.append(most_specific_context)

            # Try to find parent contexts
            parent_context = self._find_parent_context(most_specific_context, target_type)
            while parent_context and parent_context not in hierarchy:
                hierarchy.append(parent_context)
                parent_context = self._find_parent_context(parent_context, target_type)

        # Always include thread-local as final fallback
        thread_local_context = self._get_thread_local_context(target_type)
        if thread_local_context and thread_local_context not in hierarchy:
            hierarchy.append(thread_local_context)

        logger.debug(f"Context hierarchy: {[type(ctx).__name__ for ctx in hierarchy]}")
        return hierarchy

    def _find_parent_context(self, current_context: Any, target_type: Type) -> Optional[Any]:
        """
        Find the parent context by discovering the next context in the call stack.

        For step contexts, the parent should be the orchestrator context.
        """
        import inspect

        # If current context is a step, look for orchestrator in call stack
        if 'Step' in type(current_context).__name__:
            frame = inspect.currentframe()
            try:
                current_frame = frame
                while current_frame:
                    current_frame = current_frame.f_back
                    if not current_frame:
                        break

                    # Check 'self' parameter for orchestrator
                    if 'self' in current_frame.f_locals:
                        potential_context = current_frame.f_locals['self']
                        if 'Orchestrator' in type(potential_context).__name__:
                            if ContextDiscovery._is_context_provider(potential_context, target_type):
                                return potential_context

                    # Check other variables for orchestrator
                    for var_name, var_value in current_frame.f_locals.items():
                        if var_name != 'self' and 'Orchestrator' in type(var_value).__name__:
                            if ContextDiscovery._is_context_provider(var_value, target_type):
                                return var_value
            finally:
                del frame

        # Fallback to thread-local context
        thread_local = self._get_thread_local_context(target_type)
        if thread_local and thread_local != current_context:
            return thread_local

        return None

    def _get_thread_local_context(self, target_type: Type) -> Optional[Any]:
        """Get thread-local global config context for the target type."""
        try:
            global_config_type = _get_global_config_type_for_target(target_type)
            if global_config_type:
                return get_current_global_config(global_config_type)
            return None
        except Exception:
            return None



    def _get_concrete_value_at_level(self, context: Any, target_type: Type, field_name: str) -> Any:
        """
        Get concrete (non-None) value for target_type.field_name at this specific context level.

        This is level-specific - only looks within the given context, no recursion.
        Enhanced with inheritance search and global config fallback like non-recursive resolver.
        """


        context_type = type(context)

        # Try exact type first, then parent types in MRO order for inheritance
        types_to_search = [target_type]
        if hasattr(target_type, '__mro__'):
            # Add parent dataclass types from MRO (skip object)
            for parent_type in target_type.__mro__[1:]:
                if is_dataclass(parent_type):
                    types_to_search.append(parent_type)

        logger.debug(f"Searching context {context_type.__name__} for {target_type.__name__} and parents: {[t.__name__ for t in types_to_search]}")

        # Search for each type in priority order (exact type first, then parents)
        for search_type in types_to_search:
            # CRITICAL FIX: Handle direct type match (context type == target type)
            if context_type == search_type:
                logger.debug(f"Direct type match - context {context_type.__name__} == target {search_type.__name__}")
                # Direct field access from context instance
                try:
                    value = self._get_raw_field_value(context, field_name)
                    if value is not None:
                        logger.debug(f"Found direct value for {field_name}: {value}")
                        return value
                except AttributeError:
                    logger.debug(f"Field {field_name} not found in direct context")
                    pass
                # Continue to field path detection as fallback

            # Find instances of search_type within this context
            if is_dataclass(context_type):
                # FieldPathDetector now handles lazy type detection internally
                field_paths = FieldPathDetector.find_all_field_paths_unified(context_type, search_type)
                logger.debug(f"Context is dataclass {context_type.__name__}, found {len(field_paths)} paths for {search_type.__name__}")
            else:
                # Use instance-based discovery for regular objects
                hierarchy = discover_composition_hierarchy_from_instance(context)
                field_paths = hierarchy.get(search_type, [])

                # Manual lazy detection still needed for instance-based discovery
                if not field_paths:
                    field_paths = next((paths for hierarchy_type, paths in hierarchy.items()
                                      if get_base_type_for_lazy(hierarchy_type) == search_type), [])
                    if field_paths:
                        logger.debug(f"Found lazy type for base type {search_type.__name__} at paths: {field_paths}")



            logger.debug(f"Found {len(field_paths)} paths for {search_type.__name__}: {field_paths}")

            # Navigate to instances and check for concrete values
            for path in field_paths:
                instance = FieldPathNavigator.navigate_to_instance(context, path)
                if instance:
                    try:
                        value = self._get_raw_field_value(instance, field_name)
                        if value is not None:
                            logger.debug(f"Found value at {path}.{field_name} from {search_type.__name__}: {value}")
                            return value
                    except AttributeError:
                        # Field doesn't exist on this instance, continue to next path
                        continue

        # Fallback: Check global config if no value found in current context
        global_config_value = self._check_global_config_fallback(target_type, field_name)
        if global_config_value is not None:
            return global_config_value

        return None

    def _has_concrete_field_override(self, config_class: Type, field_name: str) -> bool:
        """
        Check if a class has a concrete field override (not None).

        This determines class-level inheritance blocking behavior based on static class definition.
        Note: Context-level blocking is handled separately in _resolve_field_impl.
        """
        if not hasattr(config_class, field_name):
            return False

        class_attr_value = getattr(config_class, field_name)
        has_override = class_attr_value is not None

        logger.debug(f"Class override check {config_class.__name__}.{field_name}: value={class_attr_value}, has_override={has_override}")
        return has_override

    def _find_blocking_class_in_mro(self, base_type: Type, field_name: str) -> Optional[Type]:
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
            if self._has_concrete_field_override(cls, field_name):
                # Check if there are parent classes that also have this field
                has_parent_with_field = False
                for parent_cls in base_type.__mro__[i + 1:]:
                    if not is_dataclass(parent_cls):
                        continue
                    if hasattr(parent_cls, field_name):
                        has_parent_with_field = True
                        break

                if has_parent_with_field:
                    logger.debug(f"Found blocking class {cls.__name__} for {base_type.__name__}.{field_name} (blocks parent inheritance)")
                    return cls
                else:
                    logger.debug(f"Class {cls.__name__} has concrete override but no parents with field - not blocking")
        return None
    
    def _check_global_config_fallback(self, target_type: Type, field_name: str) -> Any:
        """
        Check global config as fallback when current context doesn't have the value.

        Generic implementation that leverages the existing decorator factory system
        to auto-detect the appropriate global config type and resolve field values.
        """
        try:
            # Auto-detect global config type using existing decorator system
            global_config_type = _get_global_config_type_for_target(target_type)
            if not global_config_type:
                return None

            # Get global config instance from thread-local context
            global_config = get_current_global_config(global_config_type)
            if not global_config:
                return None

            # Use the same field path detection logic as the main resolver
            field_paths = FieldPathDetector.find_all_field_paths_unified(global_config_type, target_type)

            # Navigate to each instance in global config and check for field value
            for path in field_paths:
                instance = FieldPathNavigator.navigate_to_instance(global_config, path)
                if instance and hasattr(instance, field_name):
                    value = self._get_raw_field_value(instance, field_name)
                    if value is not None:
                        return value

            return None
        except Exception:
            return None

    def _check_static_override(self, base_type: Type, field_name: str) -> Any:
        """
        Check if the base class has a static field override that should take precedence
        over hierarchical inheritance.

        Returns the static override value if found, None otherwise.
        """
        import dataclasses

        if not is_dataclass(base_type):
            return None

        # Get parent types from MRO
        parent_types = [cls for cls in base_type.__mro__[1:] if is_dataclass(cls)]
        if not parent_types:
            return None

        # Unified field default extraction pattern
        def get_field_default(dataclass_type: Type, field_name: str) -> Any:
            return next((field.default if field.default != dataclasses.MISSING else None
                        for field in dataclasses.fields(dataclass_type) if field.name == field_name), None)

        # Get base class field default
        base_field_value = get_field_default(base_type, field_name)
        if base_field_value is None:
            return None

        # Get parent class field defaults using same pattern
        parent_field_values = {get_field_default(parent_type, field_name) for parent_type in parent_types}

        # If base class has a different default than all parents, it's an override
        if base_field_value not in parent_field_values:
            return base_field_value

        return None

    def _get_raw_field_value(self, instance: Any, field_name: str) -> Any:
        """
        Get raw field value bypassing lazy resolution to prevent infinite recursion.
        """
        try:
            return object.__getattribute__(instance, field_name)
        except AttributeError:
            return None


class ContextDiscovery:
    """
    Automatic context discovery through stack introspection and type analysis.
    
    Finds context objects by walking the call stack and identifying objects
    that provide the expected type-driven hierarchy structure.
    """
    
    @staticmethod
    def discover_context(target_type: type = None) -> Optional[Any]:
        """
        Walk call stack to find objects that can provide resolution context.

        For PipelineConfig editing: Prioritizes thread-local GlobalPipelineConfig over orchestrators
        For step-level configs: Prioritizes orchestrators over thread-local to ensure proper inheritance
        """
        if target_type and target_type.__name__ == 'StepWellFilterConfig':
            print(f"🔍 CONTEXT_DISCOVERY DEBUG: Starting discovery for {target_type.__name__}")

        frame = inspect.currentframe()

        # CRITICAL FIX: For step-level configs, use correct inheritance order: step → pipeline/orchestrator → global
        # ProcessingContext is NOT part of config inheritance - it's just an execution context
        orchestrator_context = None
        step_context = None

        # Use pure stack introspection - but collect all context providers first
        try:
            frame_count = 0
            current_frame = frame
            while current_frame:
                current_frame = current_frame.f_back
                if not current_frame:
                    break
                frame_count += 1

                # Check for any injected context (generic pattern)
                injected_context = ContextDiscovery._find_injected_context(current_frame, target_type)
                if injected_context:
                    logger.debug(f"Found injected context provider: {type(injected_context).__name__}")
                    return injected_context

                # Check 'self' parameter first (method calls are most likely to be context providers)
                if 'self' in current_frame.f_locals:
                    potential_context = current_frame.f_locals['self']
                    if ContextDiscovery._is_context_provider(potential_context, target_type):
                        context_type = type(potential_context).__name__
                        if 'Orchestrator' in context_type:
                            orchestrator_context = potential_context
                        elif 'FunctionStep' in context_type or 'Step' in context_type:
                            step_context = potential_context
                        else:
                            # Other context types (not ProcessingContext) - return immediately
                            logger.debug(f"Found context provider: self ({context_type}) - using stack proximity")
                            return potential_context

                # Check all other objects in current frame
                for var_name, var_value in current_frame.f_locals.items():
                    if var_name != 'self':
                        # Check if object can provide context for the target type
                        if ContextDiscovery._is_context_provider(var_value, target_type):
                            context_type = type(var_value).__name__
                            if 'Orchestrator' in context_type:
                                orchestrator_context = var_value
                            elif 'FunctionStep' in context_type or 'Step' in context_type:
                                step_context = var_value
                            else:
                                # Other context types (not ProcessingContext) - return immediately
                                logger.debug(f"Found context provider: {var_name} ({context_type}) - using stack proximity")
                                return var_value

        finally:
            del frame

        # PRIORITY ORDER: step → pipeline/orchestrator → global
        # Return contexts in the correct inheritance order
        if step_context:
            logger.debug(f"Using step context: {type(step_context).__name__}")
            return step_context
        elif orchestrator_context:
            logger.debug(f"Using orchestrator context: {type(orchestrator_context).__name__}")
            return orchestrator_context

        # Thread-local is a context provider, not a fallback
        if target_type:
            global_config_type = _get_global_config_type_for_target(target_type)
            if global_config_type:
                thread_local_global_config = get_current_global_config(global_config_type)
                if thread_local_global_config:
                    logger.debug(f"Using thread-local {global_config_type.__name__} as context provider")
                    return thread_local_global_config

        return None
    
    @staticmethod
    def _find_injected_context(frame: Any, target_type: type = None) -> Optional[Any]:
        """
        Find any injected context in frame locals using generic pattern.

        Looks for variables with naming pattern: __*_context__
        This allows flexible context injection without hardcoding specific names.
        """
        for var_name, var_value in frame.f_locals.items():
            # Generic pattern: __*_context__ (e.g., __step_context__, __pipeline_context__, etc.)
            if var_name.startswith('__') and var_name.endswith('_context__'):
                if ContextDiscovery._is_context_provider(var_value, target_type):
                    logger.debug(f"Found injected context: {var_name} = {type(var_value).__name__}")
                    return var_value
        return None

    @staticmethod
    def _is_context_provider(obj: Any, target_type: type = None) -> bool:
        """
        Check if object can provide resolution context for the target type.

        Considers objects that have dataclass instances relevant to the target type through:
        1. Inheritance hierarchy (parent types)
        2. Composition relationships (step attributes)
        3. Direct type matches (for step attributes)
        """
        if obj is None or not hasattr(obj, '__dict__'):
            return False



        # Look for dataclass instance attributes that could provide context for target_type
        for attr_name in dir(obj):
            if attr_name.startswith('_'):
                continue

            try:
                # Use object.__getattribute__ to bypass lazy resolution and prevent infinite recursion
                attr_value = object.__getattribute__(obj, attr_name)

                # Check if this attribute is a dataclass instance
                if (is_dataclass(attr_value) and
                    not inspect.isclass(attr_value) and
                    attr_value is not None):

                    attr_type = type(attr_value)
                    if target_type and target_type.__name__ == 'StepWellFilterConfig':
                        print(f"🔍 ATTR_DEBUG: Checking {type(obj).__name__}.{attr_name}: {attr_type.__name__} for target {target_type.__name__}")

                    # If no target_type specified, accept any dataclass (backward compatibility)
                    if target_type is None:
                        logger.debug(f"Found dataclass attribute {attr_name}: {attr_type.__name__} in {type(obj).__name__}")
                        return True

                    # INHERITANCE RESOLUTION: Check for parent types in MRO
                    # For inheritance resolution, we need the parent type, not the same type
                    # E.g., for PipelineConfig resolution, we need GlobalPipelineConfig
                    if hasattr(target_type, '__mro__'):
                        # Look for parent types in the MRO (excluding the target type itself)
                        parent_types = target_type.__mro__[1:]  # Skip the target type itself
                        if attr_type in parent_types:
                            logger.debug(f"Found parent context provider: {attr_name}: {attr_type.__name__} for target {target_type.__name__}")
                            return True

                    # COMPOSITION RESOLUTION: Check for direct type matches (step attributes)
                    # For step attributes like step_materialization_config: StepMaterializationConfig
                    if attr_type == target_type:
                        logger.debug(f"Found direct context provider: {attr_name}: {attr_type.__name__} for target {target_type.__name__}")
                        return True

                    # LAZY DATACLASS RESOLUTION: Check for lazy versions of target type
                    # For step attributes like step_materialization_config: LazyStepMaterializationConfig
                    base_type = get_base_type_for_lazy(attr_type)
                    if base_type == target_type:
                        print(f"🔍 LAZY_PROVIDER DEBUG: Found lazy context provider: {attr_name}: {attr_type.__name__} (base: {base_type.__name__}) for target {target_type.__name__}")
                        logger.debug(f"Found lazy context provider: {attr_name}: {attr_type.__name__} (base: {base_type.__name__}) for target {target_type.__name__}")
                        return True

            except (AttributeError, Exception):
                continue

        # NESTED COMPOSITION RESOLUTION: Check for target type in nested hierarchy
        # For orchestrator → pipeline_config → napari_streaming_config: LazyNapariStreamingConfig
        if target_type is not None:
            try:
                hierarchy = discover_composition_hierarchy_from_instance(obj)

                # Check if target_type or its lazy version exists in the hierarchy
                if target_type in hierarchy:
                    logger.debug(f"Found nested context provider for {target_type.__name__} at paths: {hierarchy[target_type]}")
                    return True

                # Check for lazy versions using registry
                for hierarchy_type in hierarchy.keys():
                    base_type = get_base_type_for_lazy(hierarchy_type)
                    if base_type == target_type:
                        logger.debug(f"Found nested lazy context provider: {hierarchy_type.__name__} (base: {base_type.__name__}) for target {target_type.__name__} at paths: {hierarchy[hierarchy_type]}")
                        return True

            except (AttributeError, Exception):
                pass

        return False


# Global resolver instance for reuse
_recursive_resolver = None


def get_recursive_resolver() -> RecursiveContextualResolver:
    """Get or create the global recursive resolver."""
    global _recursive_resolver

    if _recursive_resolver is None:
        _recursive_resolver = RecursiveContextualResolver()
        # Auto-initialize the system when first resolver is created
        update_lazy_dataclass_factory()

    return _recursive_resolver


def create_enhanced_lazy_getattribute():
    """
    Create enhanced __getattribute__ method for lazy dataclasses.

    This uses the recursive dual-axis resolver for proper context hierarchy traversal.
    """

    def __getattribute__(self, name: str) -> Any:
        """
        Enhanced lazy field resolution with recursive dual-axis resolution.

        Resolution order:
        1. Instance value (if not None/empty)
        2. Recursive dual-axis resolution through context hierarchy
        3. Fallback to None
        """
        # Get raw instance value first
        try:
            value = object.__getattribute__(self, name)
        except AttributeError:
            value = None

        # If we have a value or it's not a dataclass field, return as-is
        if value is not None or not self._is_dataclass_field(name):
            return value

        # Use recursive resolver
        resolver = get_recursive_resolver()
        resolved_value = resolver.resolve_field(self, name)

        logger.debug(f"Resolved {type(self).__name__}.{name} = {resolved_value}")
        return resolved_value

    return __getattribute__


def _is_dataclass_field(self, name: str) -> bool:
    """Check if name is a dataclass field."""
    if not is_dataclass(self):
        return False
    return name in {f.name for f in fields(self)}


# Updated LazyMethodBindings for integration with existing system
class RecursiveLazyMethodBindings:
    """Recursive method bindings that use dual-axis resolution."""

    @staticmethod
    def create_getattribute() -> callable:
        """Create enhanced __getattribute__ method."""
        enhanced_getattr = create_enhanced_lazy_getattribute()

        # Attach helper method
        def attached_getattr(self, name):
            # Add helper method to instance if not present
            if not hasattr(self, '_is_dataclass_field'):
                object.__setattr__(self, '_is_dataclass_field', lambda n: _is_dataclass_field(self, n))

            return enhanced_getattr(self, name)

        return attached_getattr

    @staticmethod
    def create_resolver(resolution_config) -> callable:
        """Create field resolver method - now uses recursive dual-axis resolution."""
        def _resolve_field_value(self, field_name: str) -> Any:
            # Use the recursive resolution system
            resolver = get_recursive_resolver()
            return resolver.resolve_field(self, field_name)

        return _resolve_field_value





# Integration function to update existing lazy dataclass factory
def update_lazy_dataclass_factory():
    """
    Update the existing LazyDataclassFactory to use recursive resolution.

    This patches the existing system to use recursive dual-axis resolution.
    """
    # Replace the method bindings with recursive versions
    LazyMethodBindings.create_getattribute = RecursiveLazyMethodBindings.create_getattribute
    LazyMethodBindings.create_resolver = RecursiveLazyMethodBindings.create_resolver

    logger.info("Updated LazyDataclassFactory to use recursive dual-axis resolution")


