"""Generic lazy dataclass factory using flexible resolution."""

# Standard library imports
import inspect
import logging
import re
import threading
import sys
from contextlib import contextmanager
from dataclasses import dataclass, fields, is_dataclass, make_dataclass, MISSING, field
from typing import Any, Callable, Dict, List, Optional, Tuple, Type, TypeVar, Union

# OpenHCS imports
from openhcs.core.context.global_config import (
    get_current_global_config,
    set_current_global_config,
)
from openhcs.core.field_path_detection import FieldPathDetector


# Type registry for lazy dataclass to base class mapping
_lazy_type_registry: Dict[Type, Type] = {}


def register_lazy_type_mapping(lazy_type: Type, base_type: Type) -> None:
    """Register mapping between lazy dataclass type and its base type."""
    _lazy_type_registry[lazy_type] = base_type


def get_base_type_for_lazy(lazy_type: Type) -> Optional[Type]:
    """Get the base type for a lazy dataclass type."""
    return _lazy_type_registry.get(lazy_type)

# Optional imports (handled gracefully)
try:
    from PyQt6.QtWidgets import QApplication
    HAS_PYQT = True
except ImportError:
    QApplication = None
    HAS_PYQT = False

logger = logging.getLogger(__name__)


# Constants for lazy configuration system - simplified from class to module-level
MATERIALIZATION_DEFAULTS_PATH = "materialization_defaults"
RESOLVE_FIELD_VALUE_METHOD = "_resolve_field_value"
GET_ATTRIBUTE_METHOD = "__getattribute__"
TO_BASE_CONFIG_METHOD = "to_base_config"
WITH_DEFAULTS_METHOD = "with_defaults"
WITH_OVERRIDES_METHOD = "with_overrides"
LAZY_FIELD_DEBUG_TEMPLATE = "LAZY FIELD CREATION: {field_name} - original={original_type}, has_default={has_default}, final={final_type}"
THREAD_LOCAL_FIELD_DEBUG_TEMPLATE = "THREAD-LOCAL LAZY FIELD: {field_name} - original={original_type}, has_default={has_default}, final={final_type}"
LAZY_CLASS_NAME_PREFIX = "Lazy"

# Core helper functions to eliminate duplication
_get_current_config = lambda config_type: get_current_global_config(config_type)

# Primary value resolution pattern - used throughout module for "try sources, return first non-None"
def _resolve_value_from_sources(field_name: str, *source_funcs):
    """Try multiple source functions, return first non-None value."""
    for source_func in source_funcs:
        try:
            value = source_func(field_name)
            if value is not None:
                return value
        except (AttributeError, Exception):
            continue
    return None

# Common lambda factory patterns - eliminates duplicate lambda creation
def _create_field_value_extractor(obj_provider):
    """Create lambda for extracting field values from object provider."""
    return lambda field_name: _get_raw_field_value(obj_provider(), field_name) if obj_provider() else None

def _create_static_field_extractor(obj):
    """Create lambda for extracting field values from static object."""
    return lambda field_name: _get_raw_field_value(obj, field_name)

# Removed single-use _create_resolution_config method - inlined at call site


class FieldPathNavigator:
    """Utility for navigating dot-separated field paths in object hierarchies."""

    @staticmethod
    def navigate_to_instance(current_global_config: Any, field_path: Optional[str] = None) -> Optional[Any]:
        """
        Navigate to instance using explicit field path.

        Args:
            current_global_config: Thread-local storage object or global config instance
            field_path: Dot-separated path to navigate (None = root)

        Returns:
            Instance at the specified field path, or None if not found
        """
        # Handle both thread-local storage objects and direct config instances
        if hasattr(current_global_config, "value"):
            if not current_global_config.value:
                return None
            instance = current_global_config.value
        else:
            # Direct config instance
            instance = current_global_config

        if field_path is None:
            # Root instance - return the global config directly
            return instance

        # Navigate dot-separated path
        for field in field_path.split('.'):
            if instance is None:
                return None
            # Use object.__getattribute__ to avoid triggering lazy resolution during navigation
            try:
                instance = object.__getattribute__(instance, field)
            except AttributeError:
                return None

        return instance


@dataclass(frozen=True)
class ResolutionConfig:
    """Declarative configuration for recursive lazy resolution."""
    instance_provider: Callable[[], Any]
    fallback_chain: List[Callable[[str], Any]]

    def resolve_field(self, field_name: str) -> Any:
        """Resolve field through primary instance and fallback chain."""
        primary_source = _create_field_value_extractor(self.instance_provider)
        return _resolve_value_from_sources(field_name, primary_source, *self.fallback_chain)


# Functional fallback strategies
def _get_raw_field_value(obj: Any, field_name: str) -> Any:
    """
    Get raw field value bypassing lazy property getters to prevent infinite recursion.

    Uses object.__getattribute__() to access stored values directly without triggering
    lazy resolution, which would create circular dependencies in the resolution chain.

    Args:
        obj: Object to get field from
        field_name: Name of field to access

    Returns:
        Raw field value or None if field doesn't exist

    Raises:
        AttributeError: If field doesn't exist (fail-loud behavior)
    """
    try:
        return object.__getattribute__(obj, field_name)
    except AttributeError:
        return None


@dataclass(frozen=True)
class LazyMethodBindings:
    """Declarative method bindings for lazy dataclasses."""

    @staticmethod
    def create_resolver(resolution_config: ResolutionConfig) -> Callable[[Any, str], Any]:
        """Create field resolver method."""
        return lambda self, field_name: resolution_config.resolve_field(field_name)

    @staticmethod
    def create_getattribute() -> Callable[[Any, str], Any]:
        """Create lazy __getattribute__ method."""
        def __getattribute__(self: Any, name: str) -> Any:
            # First try to get the attribute normally
            try:
                value = object.__getattribute__(self, name)
                if value is None and name in {f.name for f in fields(self.__class__)}:
                    # CRITICAL FIX: Use object.__getattribute__ to get _resolve_field_value method
                    # to avoid potential recursion if _resolve_field_value accesses other attributes
                    resolve_method = object.__getattribute__(self, '_resolve_field_value')
                    return resolve_method(name)
                return value
            except AttributeError:
                # If attribute doesn't exist on lazy class, try to get it from base class
                # This handles methods like get_streaming_kwargs
                try:
                    # CRITICAL FIX: Use object.__getattribute__ to avoid recursion
                    base_class = object.__getattribute__(self, '_base_class')
                    if hasattr(base_class, name):
                        # Create a temporary instance of the base class with current values
                        base_instance = self.to_base_config()
                        return getattr(base_instance, name)
                except AttributeError:
                    # _base_class doesn't exist, continue to raise original AttributeError
                    pass
                raise
        return __getattribute__

    @staticmethod
    def create_to_base_config(base_class: Type) -> Callable[[Any], Any]:
        """Create base config converter method."""
        return lambda self: base_class(**{
            f.name: getattr(self, f.name) for f in fields(self)
        })

    @staticmethod
    def create_class_methods() -> Dict[str, Any]:
        """Create class-level utility methods."""
        return {
            WITH_DEFAULTS_METHOD: classmethod(lambda cls: cls()),
            WITH_OVERRIDES_METHOD: classmethod(lambda cls, **kwargs: cls(**kwargs))
        }


class LazyDataclassFactory:
    """Generic factory for creating lazy dataclasses with flexible resolution."""





    @staticmethod
    def _introspect_dataclass_fields(base_class: Type, debug_template: str, global_config_type: Type = None, parent_field_path: str = None, parent_instance_provider: Optional[Callable[[], Any]] = None) -> List[Tuple[str, Type, None]]:
        """
        Introspect dataclass fields for lazy loading.

        Converts nested dataclass fields to lazy equivalents and makes fields Optional
        if they lack defaults. Complex logic handles type unwrapping and lazy nesting.
        """
        base_fields = fields(base_class)
        lazy_field_definitions = []

        for field in base_fields:
            # Check if field already has Optional type
            origin = getattr(field.type, '__origin__', None)
            is_already_optional = (origin is Union and
                                 type(None) in getattr(field.type, '__args__', ()))

            # Check if field has default value or factory
            has_default = (field.default is not MISSING or
                         field.default_factory is not MISSING)

            # Check if field type is a dataclass that should be made lazy
            field_type = field.type
            if is_dataclass(field.type) and global_config_type is not None:
                # Create lazy version with automatic inheritance detection and context propagation - inline single-use method
                full_field_path = f"{parent_field_path}.{field.name}" if parent_field_path else field.name
                lazy_nested_type = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
                    base_class=field.type,
                    global_config_type=global_config_type,
                    field_path=full_field_path,
                    lazy_class_name=f"Lazy{field.type.__name__}",
                    context_provider=lambda: parent_instance_provider() if parent_instance_provider else _get_current_config(global_config_type)
                )
                field_type = lazy_nested_type
                logger.debug(f"Created lazy class for {field.name}: {field.type} -> {lazy_nested_type}")

            # Complex type logic: make Optional if no default, preserve existing Optional types
            if is_already_optional or not has_default:
                final_field_type = Union[field_type, type(None)] if not is_already_optional else field_type
            else:
                final_field_type = field_type

            # CRITICAL FIX: Create default factory for Optional dataclass fields
            # This eliminates the need for field introspection and ensures UI always has instances to render
            default_value = None
            if (is_already_optional or not has_default) and is_dataclass(field.type):
                # For Optional dataclass fields, create default factory that creates lazy instances
                # This ensures the UI always has nested lazy instances to render recursively
                from dataclasses import field as dataclass_field
                # CRITICAL: field_type is already the lazy type, so use it directly
                default_value = dataclass_field(default_factory=field_type)

            lazy_field_definitions.append((field.name, final_field_type, default_value))

            # Debug logging with provided template (reduced to DEBUG level to reduce log pollution)
            logger.debug(debug_template.format(
                field_name=field.name,
                original_type=field.type,
                has_default=has_default,
                final_type=final_field_type
            ))

        return lazy_field_definitions

    @staticmethod
    def _create_lazy_dataclass_unified(
        base_class: Type,
        instance_provider: Callable[[], Any],
        lazy_class_name: str,
        debug_template: str,
        use_recursive_resolution: bool = False,
        fallback_chain: Optional[List[Callable[[str], Any]]] = None,
        global_config_type: Type = None,
        parent_field_path: str = None,
        parent_instance_provider: Optional[Callable[[], Any]] = None
    ) -> Type:
        """
        Create lazy dataclass with declarative configuration.

        Core factory method that creates lazy dataclass with introspected fields,
        binds resolution methods, and registers type mappings. Complex orchestration
        of field analysis, method binding, and class creation.
        """
        if not is_dataclass(base_class):
            raise ValueError(f"{base_class} must be a dataclass")

        # Inlined resolution config creation (was single-use method)
        static_fallback = _create_static_field_extractor(base_class())
        safe_fallback = _create_field_value_extractor(instance_provider)
        final_fallback_chain = (fallback_chain or [static_fallback]) if use_recursive_resolution else [safe_fallback, static_fallback]
        resolution_config = ResolutionConfig(instance_provider=instance_provider, fallback_chain=final_fallback_chain)

        # Create lazy dataclass with introspected fields, inheriting from base class
        lazy_class = make_dataclass(
            lazy_class_name,
            LazyDataclassFactory._introspect_dataclass_fields(
                base_class, debug_template, global_config_type, parent_field_path, parent_instance_provider
            ),
            bases=(base_class,),
            frozen=True
        )

        # Bind methods declaratively - inline single-use method
        method_bindings = {
            RESOLVE_FIELD_VALUE_METHOD: LazyMethodBindings.create_resolver(resolution_config),
            GET_ATTRIBUTE_METHOD: LazyMethodBindings.create_getattribute(),
            TO_BASE_CONFIG_METHOD: LazyMethodBindings.create_to_base_config(base_class),
            **LazyMethodBindings.create_class_methods()
        }
        for method_name, method_impl in method_bindings.items():
            setattr(lazy_class, method_name, method_impl)

        # Automatically register the lazy dataclass with the type registry
        register_lazy_type_mapping(lazy_class, base_class)

        return lazy_class

    @staticmethod
    def create_lazy_dataclass(
        defaults_source: Union[Type, Any],
        lazy_class_name: str,
        use_recursive_resolution: bool = False,
        fallback_chain: Optional[List[Callable[[str], Any]]] = None
    ) -> Type:
        """Create lazy dataclass with functional configuration."""
        base_class = defaults_source if isinstance(defaults_source, type) else type(defaults_source)
        instance_provider = (lambda: defaults_source()) if isinstance(defaults_source, type) else (lambda: defaults_source)

        return LazyDataclassFactory._create_lazy_dataclass_unified(
            base_class, instance_provider, lazy_class_name,
            LAZY_FIELD_DEBUG_TEMPLATE, use_recursive_resolution, fallback_chain
        )



    @staticmethod
    def make_lazy_with_field_level_auto_hierarchy(
        base_class: Type,
        global_config_type: Type,
        field_path: str = None,
        lazy_class_name: str = None,
        context_provider: Optional[Callable[[], Any]] = None
    ) -> Type:
        """
        Create lazy dataclass with automatically discovered field-level hierarchy resolution.

        Preserves sophisticated field-level inheritance while using automatic type introspection
        to discover hierarchy relationships, eliminating the need for manual configuration.
        Now supports context-aware resolution for sibling inheritance within instances.

        Args:
            base_class: The dataclass type to make lazy
            global_config_type: The global config type for thread-local resolution
            field_path: Optional field path for the current instance
            lazy_class_name: Optional name for the generated lazy class
            context_provider: Optional function that provides the resolution context.
                             If None, uses global config. If provided, uses the returned instance.

        Returns:
            Generated lazy dataclass with field-level auto-hierarchy resolution
        """
        # Generate class name if not provided
        lazy_class_name = lazy_class_name or f"Lazy{base_class.__name__}"

        # Create field-level hierarchy provider with context support
        field_level_provider = _create_field_level_hierarchy_provider(
            base_class=base_class,
            global_config_type=global_config_type,
            current_field_path=field_path,
            context_provider=context_provider
        )

        # Use field-level provider with optional static defaults fallback
        # Static fallbacks should only be used in specific contexts (tests, serialization, etc.)
        # In normal app operation, thread-local storage should always be available
        def context_aware_static_fallback(field_name: str) -> Any:
            """Static fallback that warns when used in contexts where thread-local storage should exist."""
            # Check if we're in a context where thread-local storage should exist
            current_context = _get_current_config(global_config_type)

            if current_context is None and HAS_PYQT:
                # Check if we're in a PyQt app context where this shouldn't happen
                app_instance = QApplication.instance()
                if app_instance and hasattr(app_instance, 'global_config'):
                    logger.warning(
                        f"🚨 ARCHITECTURE WARNING: Static fallback used for {base_class.__name__}.{field_name} "
                        f"in PyQt app context where thread-local storage should be available. "
                        f"This indicates a context management bug."
                    )

            # Use static default
            return _get_raw_field_value(base_class(), field_name)

        fallback_chain = [context_aware_static_fallback]

        return LazyDataclassFactory._create_lazy_dataclass_unified(
            base_class=base_class,
            instance_provider=field_level_provider,
            lazy_class_name=lazy_class_name,
            debug_template=f"Field-level auto-hierarchy resolution for {base_class.__name__}",
            use_recursive_resolution=False,
            fallback_chain=fallback_chain,
            global_config_type=global_config_type,
            parent_field_path=field_path,
            parent_instance_provider=lambda: context_provider() if context_provider else None
        )

    # Deprecated methods removed - use make_lazy_with_field_level_auto_hierarchy() for all use cases


def _create_field_level_hierarchy_provider(base_class: Type, global_config_type: Type, current_field_path: str = None, context_provider: Optional[Callable[[], Any]] = None):
    """
    Create field-level hierarchy provider with simplified logic.

    Complex function that auto-discovers inheritance relationships, builds hierarchy paths,
    and creates a provider that resolves each field through multiple config sources.
    Handles PyQt app context detection and inheritance-aware validation.
    """
    # Auto-discover unified hierarchy paths (inheritance + composition)
    all_field_paths = FieldPathDetector.find_all_field_paths_unified(global_config_type, base_class)
    parent_types = FieldPathDetector.find_all_relationships(base_class)
    sibling_paths = [path for parent_type in parent_types for path in FieldPathDetector.find_all_field_paths_unified(global_config_type, parent_type)]

    # Determine field classifications - FIXED: Use ALL parent types, not just the first one
    if parent_types:
        # Collect fields from ALL parent types (inheritance + composition)
        parent_fields = frozenset()
        for parent_type in parent_types:
            parent_fields |= frozenset(f.name for f in fields(parent_type))
        child_fields = frozenset(f.name for f in fields(base_class))
        # CRITICAL FIX: For composition, we want ALL parent fields to be resolvable, not just intersection
        inherited_fields, own_fields = parent_fields, child_fields

        # Debug removed - parent field collection working correctly
    else:
        inherited_fields, own_fields = frozenset(), frozenset(f.name for f in fields(base_class))

    def field_level_provider():
        """Provider with simplified field-level inheritance logic."""
        current_config = context_provider() if context_provider else _get_current_config(global_config_type)

        # Get actual global config from app
        actual_global_config = None
        is_pipeline_context = True
        if HAS_PYQT and (app_instance := QApplication.instance()) and hasattr(app_instance, 'global_config'):
            actual_global_config = app_instance.global_config
            is_pipeline_context = current_config is not actual_global_config

        # Build hierarchy paths
        hierarchy_paths = []
        if current_field_path:
            hierarchy_paths.append(('current', current_field_path))
        hierarchy_paths.extend(('current', path) for path in sibling_paths)
        if is_pipeline_context:
            if current_field_path:
                hierarchy_paths.append(('global', current_field_path))
            hierarchy_paths.extend(('global', path) for path in sibling_paths)
        else:
            hierarchy_paths.extend(('current', path) for path in all_field_paths if path != current_field_path)

        # CRITICAL FIX: Include ALL GlobalPipelineConfig fields for top-level field resolution
        global_config_fields = {f.name for f in fields(global_config_type)} if global_config_type else set()
        all_resolvable_fields = inherited_fields | own_fields | global_config_fields

        # Debug removed - field categorization working correctly

        # Create config instance with resolved fields
        config_instance = type('FieldLevelInheritanceConfig', (), {})()

        # Debug removed - field processing working correctly

        for field_name in all_resolvable_fields:
            is_inherited = field_name in inherited_fields

            # CRITICAL: Thread-local context must have highest priority for placeholder resolution
            sources = []

            # ALWAYS include direct access to global config for top-level fields
            is_global_config_field = global_config_type and field_name in {f.name for f in fields(global_config_type)}

            # Debug removed - conditions working correctly

            if is_global_config_field:
                if current_config:
                    sources.append(_create_static_field_extractor(current_config))
                if actual_global_config and actual_global_config != current_config:
                    sources.append(_create_static_field_extractor(actual_global_config))

            # Add hierarchy-based sources for inherited/composed fields
            if hierarchy_paths and not is_global_config_field:
                for context_type, path in hierarchy_paths:
                    config = current_config if context_type == 'current' else actual_global_config
                    if config and (instance := FieldPathNavigator.navigate_to_instance(config, path)):
                        # Debug removed - instance finding working correctly
                        # SIMPLIFIED: Use the same static field extractor that works in debug
                        sources.append(_create_static_field_extractor(instance))
            elif not hierarchy_paths and not is_global_config_field:
                # Fallback for non-global fields when no hierarchy paths
                if current_config:
                    sources.append(_create_static_field_extractor(current_config))
                if actual_global_config and actual_global_config != current_config:
                    sources.append(_create_static_field_extractor(actual_global_config))

            resolved_value = _resolve_value_from_sources(field_name, *sources)
            setattr(config_instance, field_name, resolved_value)

        return config_instance

    return field_level_provider


# Generic utility functions for clean thread-local storage management
def ensure_global_config_context(global_config_type: Type, global_config_instance: Any) -> None:
    """Ensure proper thread-local storage setup for any global config type."""
    set_current_global_config(global_config_type, global_config_instance)




def resolve_lazy_configurations_for_serialization(data: Any) -> Any:
    """Recursively resolve lazy dataclass instances to concrete values for serialization."""
    # Resolve the object itself if it's a lazy dataclass
    resolved_data = (data.to_base_config()
                    if get_base_type_for_lazy(type(data)) is not None
                    else data)

    # Recursively process nested structures based on type
    if is_dataclass(resolved_data) and not isinstance(resolved_data, type):
        # Process dataclass fields recursively - inline field processing pattern
        resolved_fields = {f.name: resolve_lazy_configurations_for_serialization(getattr(resolved_data, f.name)) for f in fields(resolved_data)}
        return type(resolved_data)(**resolved_fields)

    elif isinstance(resolved_data, dict):
        # Process dictionary values recursively
        return {
            key: resolve_lazy_configurations_for_serialization(value)
            for key, value in resolved_data.items()
        }

    elif isinstance(resolved_data, (list, tuple)):
        # Process sequence elements recursively
        resolved_items = [resolve_lazy_configurations_for_serialization(item) for item in resolved_data]
        return type(resolved_data)(resolved_items)

    else:
        # Primitive type or unknown structure - return as-is
        return resolved_data


# Generic dataclass editing with configurable value preservation
T = TypeVar('T')


def create_dataclass_for_editing(dataclass_type: Type[T], source_config: Any, preserve_values: bool = False, context_provider: Optional[Callable[[Any], None]] = None) -> T:
    """Create dataclass for editing with configurable value preservation."""
    if not is_dataclass(dataclass_type):
        raise ValueError(f"{dataclass_type} must be a dataclass")

    # Set up context if provider is given (e.g., thread-local storage)
    if context_provider:
        context_provider(source_config)

    # Initialize field values based on editing mode - inline field processing pattern
    field_values = {f.name: getattr(source_config, f.name) if preserve_values else None for f in fields(dataclass_type)}

    return dataclass_type(**field_values)


def create_config_for_editing(
    global_config_type: Type,
    global_config_instance: Any,
    preserve_values: bool = False,
    placeholder_prefix: str = "Default"
) -> Any:
    """Create editable config for any global dataclass type."""
    return create_dataclass_for_editing(
        global_config_type,
        global_config_instance,
        preserve_values=preserve_values,
        context_provider=lambda config: ensure_global_config_context(global_config_type, config)
    )


def rebuild_lazy_config_with_new_global_reference(
    existing_lazy_config: Any,
    new_global_config: Any,
    global_config_type: Optional[Type] = None
) -> Any:
    """
    Rebuild lazy config to reference new global config while preserving field states.

    This function preserves the exact field state of the existing lazy config:
    - Fields that are None (using lazy resolution) remain None
    - Fields that have been explicitly set retain their concrete values
    - Nested dataclass fields are recursively rebuilt to reference new global config
    - The underlying global config reference is updated for None field resolution

    Args:
        existing_lazy_config: Current lazy config instance
        new_global_config: New global config to reference for lazy resolution
        global_config_type: Type of the global config (defaults to type of new_global_config)

    Returns:
        New lazy config instance with preserved field states and updated global reference
    """
    if existing_lazy_config is None:
        return None

    # Determine global config type
    if global_config_type is None:
        global_config_type = type(new_global_config)

    # Set new global config in thread-local storage
    ensure_global_config_context(global_config_type, new_global_config)

    # Extract current field values without triggering lazy resolution - inline field processing pattern
    def process_field_value(field_obj):
        raw_value = object.__getattribute__(existing_lazy_config, field_obj.name)
        if raw_value is not None and hasattr(raw_value, '__dataclass_fields__'):
            try:
                return rebuild_lazy_config_with_new_global_reference(raw_value, new_global_config, global_config_type)
            except Exception:
                return raw_value
        return raw_value

    current_field_values = {f.name: process_field_value(f) for f in fields(existing_lazy_config)}

    return type(existing_lazy_config)(**current_field_values)


# Declarative Global Config Field Injection System
# Moved inline imports to top-level

# Naming configuration
GLOBAL_CONFIG_PREFIX = "Global"
LAZY_CONFIG_PREFIX = "Lazy"

# Registry to accumulate all decorations before injection
_pending_injections = {}



def create_global_default_decorator(target_config_class: Type):
    """
    Create a decorator factory for a specific global config class.

    The decorator accumulates all decorations, then injects all fields at once
    when the module finishes loading. Also creates lazy versions of all decorated configs.
    """
    target_class_name = target_config_class.__name__
    if target_class_name not in _pending_injections:
        _pending_injections[target_class_name] = {
            'target_class': target_config_class,
            'configs_to_inject': []
        }

    def global_default_decorator(cls=None, *, optional: bool = False):
        """
        Decorator that can be used with or without parameters.

        Args:
            cls: The class being decorated (when used without parentheses)
            optional: Whether to wrap the field type with Optional (default: False)
        """
        def decorator(actual_cls):
            # Generate field and class names
            field_name = _camel_to_snake(actual_cls.__name__)
            lazy_class_name = f"{LAZY_CONFIG_PREFIX}{actual_cls.__name__}"

            # Add to pending injections for field injection
            _pending_injections[target_class_name]['configs_to_inject'].append({
                'config_class': actual_cls,
                'field_name': field_name,
                'lazy_class_name': lazy_class_name,
                'optional': optional  # Store the optional flag
            })

            # Immediately create lazy version of this config (not dependent on injection)
            lazy_class = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
                base_class=actual_cls,
                global_config_type=target_config_class,
                field_path=field_name,
                lazy_class_name=lazy_class_name
            )

            # Export lazy class to config module immediately
            config_module = sys.modules[actual_cls.__module__]
            setattr(config_module, lazy_class_name, lazy_class)

            return actual_cls

        # Handle both @decorator and @decorator() usage
        if cls is None:
            # Called with parentheses: @decorator(optional=True)
            return decorator
        else:
            # Called without parentheses: @decorator
            return decorator(cls)

    return global_default_decorator



def _inject_all_pending_fields():
    """Inject all accumulated fields at once."""
    for target_name, injection_data in _pending_injections.items():
        target_class = injection_data['target_class']
        configs = injection_data['configs_to_inject']

        if configs:  # Only inject if there are configs to inject
            _inject_multiple_fields_into_dataclass(target_class, configs)

def _camel_to_snake(name: str) -> str:
    """Convert CamelCase to snake_case for field names."""
    s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()

def _inject_multiple_fields_into_dataclass(target_class: Type, configs: List[Dict]) -> None:
    """Mathematical simplification: Batch field injection with direct dataclass recreation."""
    # Imports moved to top-level

    # Direct field reconstruction - guaranteed by dataclass contract
    existing_fields = [
        (f.name, f.type, field(default_factory=f.default_factory) if f.default_factory != MISSING
         else f.default if f.default != MISSING else f.type)
        for f in fields(target_class)
    ]

    # Mathematical simplification: Single expression for all field construction with optional support
    def create_field_definition(config):
        """Create field definition with optional support."""
        from typing import Union

        field_type = config['config_class']
        is_optional = config.get('optional', False)

        if is_optional:
            # Wrap with Optional and use None as default
            field_type = Union[field_type, type(None)]
            default_value = None
        else:
            # Use default factory for required fields - use lazy class, not base class
            # field_type is already the lazy type, so use it for the default factory
            default_value = field(default_factory=field_type)

        return (config['field_name'], field_type, default_value)

    all_fields = existing_fields + [create_field_definition(config) for config in configs]

    # Direct dataclass recreation - fail-loud
    new_class = make_dataclass(
        target_class.__name__,
        all_fields,
        bases=target_class.__bases__,
        frozen=target_class.__dataclass_params__.frozen
    )

    # Direct module replacement
    module = sys.modules[target_class.__module__]
    setattr(module, target_class.__name__, new_class)
    globals()[target_class.__name__] = new_class

    # Create lazy classes and recreate PipelineConfig inline
    for config in configs:
        lazy_class = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
            base_class=config['config_class'],
            global_config_type=new_class,
            field_path=config['field_name'],
            lazy_class_name=config['lazy_class_name']
        )
        setattr(sys.modules[config['config_class'].__module__], config['lazy_class_name'], lazy_class)

        # Also make lazy class available globally for type hint resolution
        globals()[config['lazy_class_name']] = lazy_class

    # Create lazy version of the updated global config itself with proper naming
    # Global configs must start with GLOBAL_CONFIG_PREFIX - fail-loud if not
    if not target_class.__name__.startswith(GLOBAL_CONFIG_PREFIX):
        raise ValueError(f"Target class '{target_class.__name__}' must start with '{GLOBAL_CONFIG_PREFIX}' prefix")

    # Remove global prefix (GlobalPipelineConfig → PipelineConfig)
    lazy_global_class_name = target_class.__name__[len(GLOBAL_CONFIG_PREFIX):]

    lazy_global_class = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
        base_class=new_class,
        global_config_type=new_class,
        field_path=None,
        lazy_class_name=lazy_global_class_name
    )

    # Export lazy global config to the module
    setattr(sys.modules[target_class.__module__], lazy_global_class_name, lazy_global_class)

    # Also make lazy global config available globally for type hint resolution
    globals()[lazy_global_class_name] = lazy_global_class





def auto_create_decorator(global_config_class):
    """
    Decorator that automatically creates:
    1. A field injection decorator for other configs to use
    2. A lazy version of the global config itself

    Global config classes must start with "Global" prefix.
    """
    # Validate naming convention
    if not global_config_class.__name__.startswith(GLOBAL_CONFIG_PREFIX):
        raise ValueError(f"Global config class '{global_config_class.__name__}' must start with '{GLOBAL_CONFIG_PREFIX}' prefix")

    decorator_name = _camel_to_snake(global_config_class.__name__)
    decorator = create_global_default_decorator(global_config_class)

    # Export decorator to module globals
    module = sys.modules[global_config_class.__module__]
    setattr(module, decorator_name, decorator)

    # Lazy global config will be created after field injection

    return global_config_class


# Old discovery system removed - decorators handle lazy class creation automatically


def is_field_sibling_inheritable(dataclass_type: Type, field_name: str) -> bool:
    """
    Check if a field supports sibling inheritance based on dataclass inheritance.

    A field is sibling-inheritable if:
    1. The dataclass inherits from another dataclass
    2. The parent dataclass has the same field name
    3. This enables automatic sibling inheritance without metadata

    Args:
        dataclass_type: The dataclass type to check
        field_name: The field name to check

    Returns:
        True if the field supports sibling inheritance
    """
    if not is_dataclass(dataclass_type):
        return False

    try:
        # Check if this dataclass has relationships (inheritance OR composition) with field
        related_types = FieldPathDetector.find_all_relationships(dataclass_type)
        return any(field_name in {f.name for f in fields(related_type)} for related_type in related_types if is_dataclass(related_type))
    except (AttributeError, TypeError):
        return False


def resolve_dataclass_with_sibling_inheritance(instance: Any, sibling_source: Any) -> Any:
    """
    Generic utility to resolve any dataclass with automatic sibling inheritance.

    For any dataclass that inherits from another dataclass, this function
    automatically resolves None fields by inheriting from the sibling source.

    Args:
        instance: The dataclass instance to resolve
        sibling_source: The sibling object to inherit from

    Returns:
        New dataclass instance with sibling inheritance resolved

    Example:
        # StepMaterializationConfig inherits from PathPlanningConfig
        resolved = resolve_dataclass_with_sibling_inheritance(
            materialization_config, path_planning_config
        )
    """
    if not is_dataclass(instance):
        return instance

    if sibling_source is None:
        return instance

    # Resolve all fields using concise comprehension (mathematical simplification)
    resolved_values = {
        field.name: (
            getattr(sibling_source, field.name, None)
            if (current_value := getattr(instance, field.name, None)) is None
            and is_field_sibling_inheritable(type(instance), field.name)
            else current_value
        )
        for field in fields(instance)
    }

    return type(instance)(**resolved_values)

