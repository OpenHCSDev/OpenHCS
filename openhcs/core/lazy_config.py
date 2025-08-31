"""Generic lazy dataclass factory using flexible resolution."""

# Standard library imports
import inspect
import logging
import re
import threading
from contextlib import contextmanager
from dataclasses import dataclass, fields, is_dataclass, make_dataclass, MISSING
from typing import Any, Callable, Dict, List, Optional, Tuple, Type, TypeVar, Union

# OpenHCS imports
from openhcs.core.config import (
    get_base_type_for_lazy,
    get_current_global_config,
    set_current_global_config,
    register_lazy_type_mapping,
    GlobalPipelineConfig
)
from openhcs.core.field_path_detection import FieldPathDetector

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

# Unified resolution config creator - eliminates conditional duplication
def _create_resolution_config(instance_provider, base_class, use_recursive_resolution, fallback_chain=None):
    """Create resolution config with unified fallback logic."""
    static_fallback = _create_static_field_extractor(base_class())
    safe_fallback = _create_field_value_extractor(instance_provider)

    final_fallback_chain = (fallback_chain or [static_fallback]) if use_recursive_resolution else [safe_fallback, static_fallback]

    return ResolutionConfig(instance_provider=instance_provider, fallback_chain=final_fallback_chain)


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
            value = object.__getattribute__(self, name)
            if value is None and name in {f.name for f in fields(self.__class__)}:
                return self._resolve_field_value(name)
            return value
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

            lazy_field_definitions.append((field.name, final_field_type, None))

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

        # Create resolution configuration using unified helper
        resolution_config = _create_resolution_config(instance_provider, base_class, use_recursive_resolution, fallback_chain)

        # Create lazy dataclass with introspected fields
        lazy_class = make_dataclass(
            lazy_class_name,
            LazyDataclassFactory._introspect_dataclass_fields(
                base_class, debug_template, global_config_type, parent_field_path, parent_instance_provider
            ),
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
    # Auto-discover hierarchy paths
    all_field_paths = FieldPathDetector.find_all_field_paths_for_type(global_config_type, base_class)
    parent_types = FieldPathDetector.find_inheritance_relationships(base_class)
    sibling_paths = [path for parent_type in parent_types for path in FieldPathDetector.find_all_field_paths_for_type(global_config_type, parent_type)]

    # Determine field classifications
    if parent_types:
        parent_fields = frozenset(f.name for f in fields(parent_types[0]))
        child_fields = frozenset(f.name for f in fields(base_class))
        inherited_fields, own_fields = parent_fields & child_fields, child_fields - parent_fields
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

        # Create config instance with resolved fields
        config_instance = type('FieldLevelInheritanceConfig', (), {})()
        for field_name in inherited_fields | own_fields:
            is_inherited = field_name in inherited_fields

            # Create sources for value resolution
            sources = []
            if not hierarchy_paths:
                if current_config:
                    sources.append(_create_static_field_extractor(current_config))
                if actual_global_config:
                    sources.append(_create_static_field_extractor(actual_global_config))
            else:
                for context_type, path in hierarchy_paths:
                    config = current_config if context_type == 'current' else actual_global_config
                    if config and (instance := FieldPathNavigator.navigate_to_instance(config, path)):
                        # Complex lambda with inheritance-aware validation: inherited fields reject empty strings
                        sources.append(lambda fn, inst=instance, inh=is_inherited: (
                            value if (value := _get_raw_field_value(inst, fn)) is not None and (not inh or value != "") else None
                        ))

            setattr(config_instance, field_name, _resolve_value_from_sources(field_name, *sources))

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


def _create_lazy_config_classes():
    """Create lazy config classes dynamically for all config classes."""
    import openhcs.core.config as config_module

    for name, obj in inspect.getmembers(config_module):
        if (inspect.isclass(obj) and is_dataclass(obj) and name.endswith('Config') and
            not name.startswith(('Lazy', 'Global')) and
            (field_path := FieldPathDetector.find_field_path_for_type(GlobalPipelineConfig, obj)) is not None):
            try:
                obj()  # Test instantiation
                lazy_class_name = f"Lazy{name}"
                globals()[lazy_class_name] = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
                    base_class=obj, global_config_type=GlobalPipelineConfig, field_path=field_path, lazy_class_name=lazy_class_name
                )
            except Exception:
                continue

# Create the lazy classes
_create_lazy_config_classes()

