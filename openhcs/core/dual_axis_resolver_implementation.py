"""
Full implementation of dual-axis lazy resolution system.

This replaces thread-local context management with automatic context discovery
and implements the dual-axis inheritance logic with proper blocking behavior.

Inheritance blocking occurs at two levels:
1. Context-level: Concrete values in context hierarchy block inheritance
2. Class-level: Non-None class attributes block inheritance

Resolution follows X-axis (context hierarchy) then Y-axis (class inheritance MRO).
"""

import inspect
import logging
from typing import Any, Optional, Type, List
from dataclasses import fields, is_dataclass

# Import existing components
from openhcs.core.lazy_config import get_base_type_for_lazy
from openhcs.core.field_path_detection import FieldPathDetector, FieldPathNavigator

logger = logging.getLogger(__name__)


class ContextualResolver:
    """
    Dual-axis resolver that discovers context automatically and applies
    inheritance blocking rules with context-first priority.

    Resolution priority:
    1. Context values always take precedence over class defaults
    2. Context values block inheritance (no further MRO traversal)
    3. Class defaults only used when no context is available at any level

    Inheritance blocking occurs when:
    1. Context-level: Any concrete (non-None) value found in context hierarchy
    2. Class-level: Non-None class attribute (only when no higher context available)

    Resolution follows X-axis (context hierarchy) then Y-axis (class inheritance MRO),
    but always exhausts context options before falling back to class defaults.
    """
    
    def __init__(self, context_instance):
        self.context = context_instance
        self._resolution_cache = {}
    
    def resolve_field(self, lazy_instance, field_name: str) -> Any:
        """
        Resolve field using dual-axis logic:
        - X-axis: Context hierarchy (step → orchestrator → global)
        - Y-axis: Class inheritance (MRO with blocking)
        """


        # Check cache first
        cache_key = (id(lazy_instance), field_name, id(self.context))
        if cache_key in self._resolution_cache:
            return self._resolution_cache[cache_key]
        
        # Get the base type for this lazy instance
        base_type = get_base_type_for_lazy(type(lazy_instance))
        if not base_type:
            return None
        
        result = self._resolve_field_impl(base_type, field_name)
        
        # Cache the result
        self._resolution_cache[cache_key] = result
        return result
    
    def _resolve_field_impl(self, base_type: Type, field_name: str) -> Any:
        """
        Core resolution implementation with proper dual-axis inheritance blocking.

        Inheritance is blocked by:
        1. Context-level concrete values (user-set values in any context level)
        2. Class-level concrete overrides (non-None class attributes) - but only when no context available

        Resolution order:
        1. Check context for THIS type - if found, blocks inheritance
        2. Walk MRO checking each parent for context values and blocking
        3. Only return class defaults if no context is available at any level
        """

        # STEP 1: Check context for THIS type first
        # Any concrete value in context blocks inheritance immediately
        context_value = self._resolve_from_context_hierarchy(base_type, field_name)
        if context_value is not None:
            logger.debug(f"Resolved {base_type.__name__}.{field_name} from context (blocks inheritance): {context_value}")
            return context_value

        # STEP 2: Walk MRO for parent types with proper blocking logic
        # Always prioritize context values over class defaults
        for parent_type in base_type.__mro__[1:]:
            if not is_dataclass(parent_type):
                continue

            # Check parent context first - concrete values block inheritance
            parent_context_value = self._resolve_from_context_hierarchy(parent_type, field_name)
            if parent_context_value is not None:
                logger.debug(f"Resolved {base_type.__name__}.{field_name} from parent {parent_type.__name__} context (blocks inheritance): {parent_context_value}")
                return parent_context_value

            # Check if parent class blocks inheritance
            if self._has_concrete_field_override(parent_type, field_name):
                # Parent class blocks inheritance - but only return class default if no more context to check
                # Continue checking for context in remaining parents first
                remaining_parents = base_type.__mro__[base_type.__mro__.index(parent_type) + 1:]

                # Check if any remaining parents have context values
                for remaining_parent in remaining_parents:
                    if not is_dataclass(remaining_parent):
                        continue
                    remaining_context = self._resolve_from_context_hierarchy(remaining_parent, field_name)
                    if remaining_context is not None:
                        logger.debug(f"Resolved {base_type.__name__}.{field_name} from higher parent {remaining_parent.__name__} context (overrides class block): {remaining_context}")
                        return remaining_context

                # No context found in remaining parents - class default can be used
                parent_default = getattr(parent_type, field_name, None)
                logger.debug(f"Using parent class default for {base_type.__name__}.{field_name} from {parent_type.__name__} (no higher context available): {parent_default}")
                return parent_default

            # Parent allows inheritance - continue to next parent (context already checked above)
            logger.debug(f"Parent {parent_type.__name__} allows inheritance for {field_name}, continuing MRO")

        # STEP 3: No context found anywhere - check if THIS class has a default
        if self._has_concrete_field_override(base_type, field_name):
            class_default = getattr(base_type, field_name, None)
            logger.debug(f"Using class default for {base_type.__name__}.{field_name} (no context available): {class_default}")
            return class_default

        logger.debug(f"No resolution found for {base_type.__name__}.{field_name}")
        return None
    
    def _resolve_from_context_hierarchy(self, target_type: Type, field_name: str) -> Any:
        """
        X-axis resolution: Find instances of target_type OR its parent types in context hierarchy.

        Uses FieldPathDetector to find all possible locations of target_type and its MRO parents
        in the current context, then navigates to those instances.

        This enables proper inheritance: StepMaterializationConfig can inherit from
        StepWellFilterConfig instances found in the orchestrator's pipeline config.
        """
        if not self.context:
            return None

        context_type = type(self.context)

        # Try exact type first, then parent types in MRO order
        types_to_search = [target_type]
        if hasattr(target_type, '__mro__'):
            # Add parent dataclass types from MRO (skip object)
            for parent_type in target_type.__mro__[1:]:
                if is_dataclass(parent_type):
                    types_to_search.append(parent_type)

        logger.debug(f"Searching context for {target_type.__name__} and parents: {[t.__name__ for t in types_to_search]}")

        # Search for each type in priority order (exact type first, then parents)
        for search_type in types_to_search:
            if is_dataclass(context_type):
                # Use type-based discovery for dataclasses
                field_paths = FieldPathDetector.find_all_field_paths_unified(context_type, search_type)
            else:
                # Use instance-based discovery for regular objects
                from openhcs.core.composition_detection import discover_composition_hierarchy_from_instance
                hierarchy = discover_composition_hierarchy_from_instance(self.context)

                # Try both the exact type and any lazy version of the type
                field_paths = hierarchy.get(search_type, [])

                # If no paths found for base type, try to find lazy version
                if not field_paths:
                    lazy_type_name = f"Lazy{search_type.__name__}"
                    for hierarchy_type, paths in hierarchy.items():
                        if hierarchy_type.__name__ == lazy_type_name:
                            field_paths = paths
                            break

            logger.debug(f"Found {len(field_paths)} paths for {search_type.__name__}: {field_paths}")

            # Navigate to each instance and check for field value
            for path in field_paths:
                instance = FieldPathNavigator.navigate_to_instance(self.context, path)
                if instance:
                    # Use object.__getattribute__ to bypass lazy resolution and prevent infinite recursion
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

    def _check_global_config_fallback(self, target_type: Type, field_name: str) -> Any:
        """
        Check global config as fallback when current context doesn't have the value.

        Generic implementation that leverages the existing decorator factory system
        to auto-detect the appropriate global config type and resolve field values.
        """
        try:
            # Auto-detect global config type using existing decorator system
            global_config_type = self._detect_global_config_type(target_type)
            if not global_config_type:
                return None

            # Get global config instance from thread-local context
            from openhcs.core.context.global_config import get_current_global_config
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

    def _detect_global_config_type(self, target_type: Type) -> Optional[Type]:
        """
        Auto-detect the global config type using the existing decorator factory registry.

        Leverages the lazy config system's existing tracking of config type relationships
        to find the global config that contains the target type.
        """
        try:
            # Use the existing field path detection to find which global config contains this type
            # Check common global config types from the same module
            target_module = target_type.__module__

            # Import the module to access global config classes
            import importlib
            module = importlib.import_module(target_module)

            # Look for global config classes (classes with "Global" prefix)
            for attr_name in dir(module):
                if attr_name.startswith('Global') and attr_name.endswith('Config'):
                    attr_value = getattr(module, attr_name)
                    if isinstance(attr_value, type) and hasattr(attr_value, '__dataclass_fields__'):
                        # Use the existing field path detection logic
                        field_paths = FieldPathDetector.find_all_field_paths_unified(attr_value, target_type)
                        if field_paths:
                            return attr_value

            return None

        except Exception:
            return None

    def _try_lazy_path_resolution(self, path: str):
        """
        Try to resolve a field path using lazy config's nested config creation.

        This bypasses the dual-axis resolver to avoid infinite recursion while
        still triggering the lazy config's automatic nested config creation.
        """
        try:
            # For paths like 'pipeline_config.step_well_filter_config', we need to:
            # 1. Get pipeline_config from context (should work)
            # 2. Get step_well_filter_config from pipeline_config using lazy resolution

            parts = path.split('.')
            if len(parts) != 2 or parts[0] != 'pipeline_config':
                return None

            # Get the pipeline_config from context
            pipeline_config = object.__getattribute__(self.context, 'pipeline_config')
            if pipeline_config is None:
                return None

            # Get the nested config field name
            nested_field = parts[1]

            # Check if the pipeline_config has this field and it's a dataclass type
            from dataclasses import fields, is_dataclass
            pipeline_fields = fields(pipeline_config.__class__)
            field_obj = next((f for f in pipeline_fields if f.name == nested_field), None)

            if field_obj and is_dataclass(field_obj.type):
                # Create an instance of the nested config type
                # This should be the lazy type that will resolve through dual-axis
                return field_obj.type()

            return None
        except (AttributeError, Exception):
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
    def discover_context() -> Optional[Any]:
        """
        Walk call stack to find objects that can provide resolution context.

        Prioritizes orchestrators over other context providers to ensure proper
        step-level config inheritance from orchestrator pipeline configs.
        """
        frame = inspect.currentframe()

        # First pass: Look for orchestrators (highest priority)
        orchestrator_context = None
        try:
            frame_count = 0
            current_frame = frame
            while current_frame:
                current_frame = current_frame.f_back
                if not current_frame:
                    break
                frame_count += 1

                # Check for orchestrator objects first (highest priority)
                for var_name, var_value in current_frame.f_locals.items():
                    if hasattr(var_value, 'pipeline_config') and hasattr(var_value, 'plate_path'):
                        logger.debug(f"Found orchestrator {var_name} ({type(var_value).__name__}) in frame {frame_count}")
                        if ContextDiscovery._is_context_provider(var_value):
                            logger.debug(f"Using orchestrator as primary context provider")
                            return var_value

        finally:
            pass

        # Second pass: Look for other context providers if no orchestrator found
        try:
            frame_count = 0
            current_frame = frame
            while current_frame:
                current_frame = current_frame.f_back
                if not current_frame:
                    break
                frame_count += 1

                # Check 'self' parameter first (method calls are most likely to be context providers)
                if 'self' in current_frame.f_locals:
                    potential_context = current_frame.f_locals['self']
                    if ContextDiscovery._is_context_provider(potential_context):
                        logger.debug(f"Found context provider: self ({type(potential_context).__name__}) - using stack proximity")
                        return potential_context

                # Check all other objects in current frame only if 'self' didn't provide context
                for var_name, var_value in current_frame.f_locals.items():
                    if var_name != 'self' and ContextDiscovery._is_context_provider(var_value):
                        logger.debug(f"Found context provider: {var_name} ({type(var_value).__name__}) - using stack proximity")
                        return var_value

        finally:
            del frame

        logger.debug("No context provider found in call stack")
        return None
    
    @staticmethod
    def _is_context_provider(obj: Any) -> bool:
        """
        Check if object can provide resolution context using type introspection.

        Identifies context providers by looking for dataclass instances as attributes,
        which indicates this object participates in the type-driven hierarchy.
        """
        if obj is None or not hasattr(obj, '__dict__'):
            return False

        # Look for dataclass instance attributes (not classes themselves)
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
                    logger.debug(f"Found dataclass attribute {attr_name}: {type(attr_value).__name__}")
                    return True

            except (AttributeError, Exception):
                continue

        return False




# Global resolver instance for reuse
_resolver_cache = {}


def get_resolver_for_context(context_instance) -> ContextualResolver:
    """Get or create resolver for the given context instance."""
    context_id = id(context_instance)
    
    if context_id not in _resolver_cache:
        _resolver_cache[context_id] = ContextualResolver(context_instance)
    
    return _resolver_cache[context_id]


def create_enhanced_lazy_getattribute():
    """
    Create enhanced __getattribute__ method for lazy dataclasses.
    
    This replaces the thread-local dependent resolution with automatic
    context discovery and dual-axis resolution.
    """
    
    def __getattribute__(self, name: str) -> Any:
        """
        Enhanced lazy field resolution with automatic context discovery.
        
        Resolution order:
        1. Instance value (if not None/empty)
        2. Dual-axis resolution through discovered context
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
        
        # Auto-discover context from call stack
        context = ContextDiscovery.discover_context()
        if not context:
            logger.debug(f"No context found for {type(self).__name__}.{name}")
            return None
        
        # Get resolver and resolve field
        resolver = get_resolver_for_context(context)
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
class EnhancedLazyMethodBindings:
    """Enhanced method bindings that use dual-axis resolution."""
    
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
        """Create field resolver method - now uses dual-axis resolution."""
        def _resolve_field_value(self, field_name: str) -> Any:
            # Use the enhanced resolution system
            context = ContextDiscovery.discover_context()
            if not context:
                return None
            
            resolver = get_resolver_for_context(context)
            return resolver.resolve_field(self, field_name)
        
        return _resolve_field_value


# Updated placeholder service integration
class EnhancedPlaceholderService:
    """Enhanced placeholder service using dual-axis resolution."""
    
    @staticmethod
    def get_lazy_resolved_placeholder(
        dataclass_type: Type,
        field_name: str,
        app_config: Optional[Any] = None,
        placeholder_prefix: str = "Inherits"
    ) -> Optional[str]:
        """
        Get placeholder text using enhanced resolution system.
        
        No thread-local manipulation needed - uses context discovery.
        """
        from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
        
        if not LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type):
            return None
        
        # Create temporary instance
        temp_instance = dataclass_type()
        
        # If app_config provided, use it directly
        if app_config:
            resolver = get_resolver_for_context(app_config)
            resolved_value = resolver.resolve_field(temp_instance, field_name)
        else:
            # Let it auto-discover from call stack
            resolved_value = getattr(temp_instance, field_name)
        
        # Format placeholder text
        if resolved_value is None:
            return None
        
        if hasattr(resolved_value, 'value') and hasattr(resolved_value, 'name'):  # Enum
            value_text = f"{resolved_value.name}"
        else:
            value_text = str(resolved_value)
        
        return f"{placeholder_prefix}: {value_text}"


# Integration function to update existing lazy dataclass factory
def update_lazy_dataclass_factory():
    """
    Update the existing LazyDataclassFactory to use enhanced resolution.
    
    This patches the existing system to use dual-axis resolution instead
    of thread-local dependent resolution.
    """
    from openhcs.core.lazy_config import LazyMethodBindings
    
    # Replace the method bindings with enhanced versions
    LazyMethodBindings.create_getattribute = EnhancedLazyMethodBindings.create_getattribute
    LazyMethodBindings.create_resolver = EnhancedLazyMethodBindings.create_resolver
    
    logger.info("Updated LazyDataclassFactory to use dual-axis resolution")


# Simplified parameter form integration
class DualAxisParameterForm:
    """
    Simplified parameter form that leverages dual-axis resolution.
    
    This replaces the complex 180+ line context building with simple
    lazy resolution that automatically discovers context.
    """
    
    def __init__(self, config_type: Type):
        self.config_type = config_type
        self.current_values = {}
        self.widgets = {}
    
    def get_placeholder(self, field_name: str) -> Optional[str]:
        """Get placeholder using automatic resolution - no context building needed."""
        # Create temp instance with current form values
        temp_instance = self._create_temp_instance()
        
        # Enhanced resolution happens automatically in __getattribute__
        resolved_value = getattr(temp_instance, field_name)
        
        if resolved_value is None:
            return None
        
        return f"Inherits: {resolved_value}"
    
    def set_field(self, field_name: str, value: Any) -> None:
        """Set field value."""
        self.current_values[field_name] = value
    
    def reset_field(self, field_name: str) -> None:
        """Reset field to show inheritance."""
        self.current_values[field_name] = None
        # Next placeholder request will auto-resolve through context
    
    def _create_temp_instance(self):
        """Create temporary instance with current form values."""
        # Only include non-None values
        filtered_values = {k: v for k, v in self.current_values.items() if v is not None}
        
        try:
            return self.config_type(**filtered_values)
        except Exception:
            # Fallback to empty instance
            return self.config_type()


# Testing and validation utilities
class ResolutionValidator:
    """Utilities for testing and validating dual-axis resolution."""
    
    @staticmethod
    def trace_resolution(lazy_instance, field_name: str) -> dict:
        """
        Trace the resolution path for debugging.
        
        Returns detailed information about how a field was resolved.
        """
        context = ContextDiscovery.discover_context()
        if not context:
            return {"error": "No context found"}
        
        resolver = get_resolver_for_context(context)
        base_type = get_base_type_for_lazy(type(lazy_instance))
        
        trace = {
            "lazy_type": type(lazy_instance).__name__,
            "base_type": base_type.__name__ if base_type else None,
            "field_name": field_name,
            "context_type": type(context).__name__,
            "has_concrete_override": resolver._has_concrete_field_override(base_type, field_name) if base_type else False,
            "field_paths": [],
            "mro_checked": [],
            "final_value": None
        }
        
        if base_type:
            # Trace field paths
            field_paths = FieldPathDetector.find_all_field_paths_unified(type(context), base_type)
            trace["field_paths"] = field_paths
            
            # Trace MRO
            for parent_type in base_type.__mro__:
                if is_dataclass(parent_type):
                    trace["mro_checked"].append({
                        "type": parent_type.__name__,
                        "has_override": resolver._has_concrete_field_override(parent_type, field_name)
                    })
            
            # Get final resolution - DISABLED to prevent infinite loop
            # trace["final_value"] = resolver.resolve_field(lazy_instance, field_name)
            trace["final_value"] = "DISABLED_TO_PREVENT_INFINITE_LOOP"
        
        return trace


# Initialization function
def initialize_dual_axis_resolution():
    """
    Initialize the dual-axis resolution system.
    
    This should be called during application startup to replace
    thread-local resolution with the enhanced system.
    """
    # Update the lazy dataclass factory
    update_lazy_dataclass_factory()
    
    # Clear any existing resolver caches
    global _resolver_cache
    _resolver_cache.clear()
    
    logger.info("Dual-axis resolution system initialized")


if __name__ == "__main__":
    # Example usage
    initialize_dual_axis_resolution()
    
    # The system is now ready to use with existing lazy dataclasses
    # No changes needed to user code - lazy configs automatically use dual-axis resolution