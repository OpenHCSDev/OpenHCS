"""Generic lazy dataclass factory using flexible resolution."""

# Standard library imports
import dataclasses
import inspect
import logging
import re
import threading
import sys
from abc import ABCMeta
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

# Cache for lazy classes to prevent duplicate creation
_lazy_class_cache: Dict[str, Type] = {}


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
        # Move imports to module level to avoid repeated inline imports
        from openhcs.core.lazy_placeholder import _has_concrete_field_override
        from openhcs.core.context.global_config import get_current_global_config
        from openhcs.core.field_path_detection import FieldPathDetector, FieldPathNavigator

        def _find_mro_concrete_value(base_class, name):
            """Extract common MRO traversal pattern."""
            return next((getattr(cls, name) for cls in base_class.__mro__
                        if _has_concrete_field_override(cls, name)), None)

        def _try_global_context_value(self, base_class, name):
            """Extract global context resolution logic."""
            if not hasattr(self, '_global_config_type'):
                return None

            current_context = get_current_global_config(self._global_config_type)
            if not current_context:
                return None

            field_paths = FieldPathDetector.find_all_field_paths_unified(type(current_context), base_class)
            for field_path in field_paths:
                try:
                    context_value = FieldPathNavigator.navigate_to_instance(current_context, field_path)
                    if context_value and hasattr(context_value, name):
                        global_value = getattr(context_value, name)
                        if global_value is not None:
                            print(f"🔍 LAZY GETATTR: Using global context value for {base_class.__name__}.{name} = '{global_value}' from {field_path} (overriding MRO default)")
                            return global_value
                except (AttributeError, TypeError):
                    continue
            return None

        def __getattribute__(self: Any, name: str) -> Any:
            value = object.__getattribute__(self, name)
            if value is not None or name not in {f.name for f in fields(self.__class__)}:
                return value

            base_class = get_base_type_for_lazy(self.__class__)
            if not base_class:
                # No base class - fall through to normal lazy resolution
                pass
            elif not any(_has_concrete_field_override(cls, name) for cls in base_class.__mro__):
                # No concrete overrides in MRO - fall through to normal lazy resolution
                pass
            else:
                # Has concrete overrides - apply inheritance fix
                recursion_key = f"_inheritance_resolving_{id(self)}_{name}"
                if hasattr(self, recursion_key):
                    return _find_mro_concrete_value(base_class, name)

                object.__setattr__(self, recursion_key, True)
                try:
                    # Try global context first, then MRO fallback
                    return (_try_global_context_value(self, base_class, name) or
                           _find_mro_concrete_value(base_class, name))
                finally:
                    if hasattr(self, recursion_key):
                        object.__delattr__(self, recursion_key)

            # Fallback to normal lazy resolution if no inheritance fix needed
            try:
                resolve_method = object.__getattribute__(self, '_resolve_field_value')
                return resolve_method(name)
            except AttributeError:
                # If attribute doesn't exist on lazy class, try to get it from base class
                try:
                    base_class = object.__getattribute__(self, '_base_class')
                    if hasattr(base_class, name):
                        base_instance = self.to_base_config()
                        return getattr(base_instance, name)
                except AttributeError:
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
                # CRITICAL: field_type is already the lazy type, so use it directly
                default_value = dataclasses.field(default_factory=field_type)

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

        # Check cache first to prevent duplicate creation
        cache_key = f"{base_class.__name__}_{lazy_class_name}_{id(instance_provider)}"
        if cache_key in _lazy_class_cache:
            return _lazy_class_cache[cache_key]

        # Inlined resolution config creation (was single-use method)
        # CRITICAL FIX: Handle abstract base classes that can't be instantiated
        try:
            static_fallback = _create_static_field_extractor(base_class())
        except TypeError as e:
            if "Can't instantiate abstract class" in str(e):
                # Abstract class - skip static fallback
                static_fallback = None
                print(f"🔧 LAZY FACTORY: Skipping static fallback for abstract class {base_class.__name__}")
            else:
                raise

        safe_fallback = _create_field_value_extractor(instance_provider)
        final_fallback_chain = (fallback_chain or ([static_fallback] if static_fallback else [])) if use_recursive_resolution else ([safe_fallback] + ([static_fallback] if static_fallback else []))
        resolution_config = ResolutionConfig(instance_provider=instance_provider, fallback_chain=final_fallback_chain)

        # Create lazy dataclass with introspected fields
        # CRITICAL FIX: Avoid inheriting from classes with custom metaclasses to prevent descriptor conflicts
        # Exception: InheritAsNoneMeta is safe to inherit from as it only modifies field defaults
        # Exception: Classes with _inherit_as_none marker are safe even with ABCMeta (processed by @global_pipeline_config)
        base_metaclass = type(base_class)
        has_inherit_as_none_marker = hasattr(base_class, '_inherit_as_none') and base_class._inherit_as_none
        has_unsafe_metaclass = (
            (hasattr(base_class, '__metaclass__') or base_metaclass != type) and
            base_metaclass != InheritAsNoneMeta and
            not has_inherit_as_none_marker
        )

        if has_unsafe_metaclass:
            # Base class has unsafe custom metaclass - don't inherit, just copy interface
            print(f"🔧 LAZY FACTORY: {base_class.__name__} has custom metaclass {base_metaclass.__name__}, avoiding inheritance")
            lazy_class = make_dataclass(
                lazy_class_name,
                LazyDataclassFactory._introspect_dataclass_fields(
                    base_class, debug_template, global_config_type, parent_field_path, parent_instance_provider
                ),
                bases=(),  # No inheritance to avoid metaclass conflicts
                frozen=True
            )
        else:
            # Safe to inherit from regular dataclass
            lazy_class = make_dataclass(
                lazy_class_name,
                LazyDataclassFactory._introspect_dataclass_fields(
                    base_class, debug_template, global_config_type, parent_field_path, parent_instance_provider
                ),
                bases=(base_class,),
                frozen=True
            )

        # Add constructor parameter tracking to detect user-set fields
        original_init = lazy_class.__init__
        def __init_with_tracking__(self, **kwargs):
            # Track which fields were explicitly passed to constructor
            object.__setattr__(self, '_explicitly_set_fields', set(kwargs.keys()))
            # Store the global config type for inheritance resolution
            object.__setattr__(self, '_global_config_type', global_config_type)
            original_init(self, **kwargs)

        lazy_class.__init__ = __init_with_tracking__

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

        # Cache the created class to prevent duplicates
        _lazy_class_cache[cache_key] = lazy_class

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

        # DEBUG: Show what context the lazy resolution is using (removed to prevent infinite loops)

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

    # CRITICAL FIX: Create proper lazy instances for nested dataclass fields
    # This ensures that nested configs use lazy types for proper placeholder resolution
    field_values = {}
    for f in fields(dataclass_type):
        if preserve_values:
            field_values[f.name] = getattr(source_config, f.name)
        else:
            # For editing mode, create lazy instances for nested dataclass fields
            from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
            if is_dataclass(f.type) and LazyDefaultPlaceholderService.has_lazy_resolution(f.type):
                # Create lazy instance using the field's lazy type
                field_values[f.name] = f.type()
            else:
                field_values[f.name] = None

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



class InheritAsNoneMeta(ABCMeta):
    """
    Metaclass that applies inherit_as_none modifications during class creation.

    This runs BEFORE @dataclass and modifies the class definition to add
    field overrides with None defaults for inheritance.
    """

    def __new__(mcs, name, bases, namespace, **kwargs):
        # Create the class first
        cls = super().__new__(mcs, name, bases, namespace)

        # Check if this class should have inherit_as_none applied
        if hasattr(cls, '_inherit_as_none') and cls._inherit_as_none:
            # Add multiprocessing safety marker
            cls._multiprocessing_safe = True
            # Get explicitly defined fields (in this class's namespace)
            explicitly_defined_fields = set()
            if '__annotations__' in namespace:
                for field_name in namespace['__annotations__']:
                    if field_name in namespace:
                        explicitly_defined_fields.add(field_name)

            # Process parent classes to find fields that need None overrides
            processed_fields = set()
            for base in bases:
                if hasattr(base, '__annotations__'):
                    for field_name, field_type in base.__annotations__.items():
                        if field_name in processed_fields:
                            continue

                        # Check if parent has concrete default
                        parent_has_concrete_default = False
                        if hasattr(base, field_name):
                            parent_value = getattr(base, field_name)
                            parent_has_concrete_default = parent_value is not None

                        # Add None override if needed
                        if (field_name not in explicitly_defined_fields and parent_has_concrete_default):
                            # Set the class attribute to None
                            setattr(cls, field_name, None)

                            # Ensure annotation exists
                            if not hasattr(cls, '__annotations__'):
                                cls.__annotations__ = {}
                            cls.__annotations__[field_name] = field_type

                            processed_fields.add(field_name)
                        else:
                            processed_fields.add(field_name)

        return cls

    def __reduce__(cls):
        """Make classes with this metaclass pickle-safe for multiprocessing."""
        # Filter out problematic descriptors that cause conflicts during pickle/unpickle
        safe_dict = {}
        for key, value in cls.__dict__.items():
            # Skip descriptors that cause conflicts
            if hasattr(value, '__get__') and hasattr(value, '__set__'):
                continue  # Skip data descriptors
            if hasattr(value, '__dict__') and hasattr(value, '__class__'):
                # Skip complex objects that might have descriptor conflicts
                if 'descriptor' in str(type(value)).lower():
                    continue
            # Include safe attributes
            safe_dict[key] = value

        # Return reconstruction using the base type (not the metaclass)
        return (type, (cls.__name__, cls.__bases__, safe_dict))









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

    def global_default_decorator(cls=None, *, optional: bool = False, inherit_as_none: bool = True, ui_hidden: bool = False):
        """
        Decorator that can be used with or without parameters.

        Args:
            cls: The class being decorated (when used without parentheses)
            optional: Whether to wrap the field type with Optional (default: False)
            inherit_as_none: Whether to set all inherited fields to None by default (default: True)
            ui_hidden: Whether to hide from UI (apply decorator but don't inject into global config) (default: False)
        """
        def decorator(actual_cls):
            print(f"🔧 DECORATOR: Processing {actual_cls.__name__} with inherit_as_none={inherit_as_none}")

            # Apply inherit_as_none by modifying class BEFORE @dataclass (multiprocessing-safe)
            if inherit_as_none:
                # Mark the class for inherit_as_none processing
                actual_cls._inherit_as_none = True

                # Apply inherit_as_none logic by directly modifying the class definition
                # This must happen BEFORE @dataclass processes the class
                explicitly_defined_fields = set()
                if hasattr(actual_cls, '__annotations__'):
                    for field_name in actual_cls.__annotations__:
                        # Check if field has a concrete default value in THIS class definition
                        if hasattr(actual_cls, field_name):
                            field_value = getattr(actual_cls, field_name)
                            # Only consider it explicitly defined if it has a concrete value (not None)
                            if field_value is not None:
                                explicitly_defined_fields.add(field_name)

                # Process parent classes to find fields that need None overrides
                processed_fields = set()
                fields_set_to_none = set()  # Track which fields were actually set to None
                for base in actual_cls.__bases__:
                    if hasattr(base, '__annotations__'):
                        for field_name, field_type in base.__annotations__.items():
                            if field_name in processed_fields:
                                continue

                            # Set inherited fields to None (except explicitly defined ones)
                            if field_name not in explicitly_defined_fields:
                                # Set the class attribute to None
                                setattr(actual_cls, field_name, None)
                                fields_set_to_none.add(field_name)

                                # Ensure annotation exists
                                if not hasattr(actual_cls, '__annotations__'):
                                    actual_cls.__annotations__ = {}
                                actual_cls.__annotations__[field_name] = field_type

                            processed_fields.add(field_name)

                # CRITICAL: Update dataclass field definitions ONLY for fields set to None
                # This preserves concrete defaults for explicitly defined fields
                import dataclasses
                if hasattr(actual_cls, '__dataclass_fields__'):
                    for field_name in fields_set_to_none:  # Only fields actually set to None
                        if field_name in actual_cls.__dataclass_fields__:
                            # Update the existing field to use None as default
                            field_obj = actual_cls.__dataclass_fields__[field_name]
                            field_obj.default = None
                            field_obj.default_factory = dataclasses.MISSING

            # Generate field and class names
            field_name = _camel_to_snake(actual_cls.__name__)
            lazy_class_name = f"{LAZY_CONFIG_PREFIX}{actual_cls.__name__}"

            # Add to pending injections for field injection (unless ui_hidden)
            if not ui_hidden:
                _pending_injections[target_class_name]['configs_to_inject'].append({
                    'config_class': actual_cls,
                    'field_name': field_name,
                    'lazy_class_name': lazy_class_name,
                    'optional': optional,  # Store the optional flag
                    'inherit_as_none': inherit_as_none  # Store the inherit_as_none flag
                })
            else:
                print(f"🔧 DECORATOR: Hiding {actual_cls.__name__} from UI (ui_hidden=True)")

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

    # Mathematical simplification: Single expression for all field construction with optional and inherit_as_none support
    def create_field_definition(config):
        """Create field definition with optional and inherit_as_none support."""

        field_type = config['config_class']
        is_optional = config.get('optional', False)
        inherit_as_none = config.get('inherit_as_none', False)

        if is_optional:
            # Wrap with Optional and use None as default
            field_type = Union[field_type, type(None)]
            default_value = None
        elif inherit_as_none:
            # inherit_as_none modification is now done in the decorator
            # Just use default factory for the (already modified) field_type
            default_value = field(default_factory=field_type)
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

    # Add generic sibling inheritance support for all config classes
    import dataclasses
    def apply_sibling_inheritance_to_instance(instance, **provided_kwargs):
        """Apply sibling inheritance to any config instance generically."""
        from dataclasses import fields, is_dataclass, replace

        if not is_dataclass(instance):
            return instance

        # Find all fields that should inherit from siblings
        inheritance_updates = {}

        for field in fields(instance):
            current_value = getattr(instance, field.name)

            # Only inherit if current value is None and field supports sibling inheritance
            if current_value is None and is_field_sibling_inheritable(type(instance), field.name):
                # Find sibling config instances in provided_kwargs that have this field
                for kwarg_name, kwarg_value in provided_kwargs.items():
                    if is_dataclass(kwarg_value) and hasattr(kwarg_value, field.name):
                        sibling_value = getattr(kwarg_value, field.name)
                        if sibling_value is not None:
                            inheritance_updates[field.name] = sibling_value
                            break  # Use first non-None sibling value found

        # Apply inheritance updates if any were found
        if inheritance_updates:
            return replace(instance, **inheritance_updates)
        return instance

    # Apply sibling inheritance to all default_factory config fields
    original_new = new_class.__new__

    def __new__(cls, **kwargs):
        """Create instance with automatic sibling inheritance applied to all config fields."""
        # Create instance normally first
        if original_new is object.__new__:
            instance = original_new(cls)
        else:
            instance = original_new(cls, **kwargs)

        return instance

    def __init__(self, **kwargs):
        """Initialize with sibling inheritance applied to config fields."""
        # Apply sibling inheritance to any config fields that need it
        resolved_kwargs = dict(kwargs)

        # Get field defaults and apply sibling inheritance
        for field in fields(self):
            if field.name not in kwargs:
                if field.default_factory != dataclasses.MISSING:
                    # Create default instance with proper None values for inherited fields
                    default_class = field.default_factory

                    # Check if this class has inherit_as_none fields
                    if hasattr(default_class, '_inherit_as_none') and default_class._inherit_as_none:
                        # CRITICAL FIX: Force None values for all fields marked by inherit_as_none
                        # The decorator sets class attributes to None, but dataclass constructor ignores them
                        # We need to explicitly pass None for all inherited fields
                        instance_kwargs = {}
                        for class_field in fields(default_class):
                            if hasattr(default_class, class_field.name):
                                class_value = getattr(default_class, class_field.name)
                                if class_value is None:
                                    # Field was set to None by inherit_as_none - FORCE None in constructor
                                    instance_kwargs[class_field.name] = None
                                else:
                                    # Field has concrete value - use it
                                    instance_kwargs[class_field.name] = class_value
                            else:
                                # Field not on class - let dataclass use its default
                                pass

                        # Create instance with explicit None values to override dataclass defaults
                        default_instance = default_class(**instance_kwargs)
                    else:
                        # Normal instance creation
                        default_instance = default_class()

                    # Apply sibling inheritance
                    resolved_instance = apply_sibling_inheritance_to_instance(default_instance, **kwargs)
                    resolved_kwargs[field.name] = resolved_instance
                elif field.default != dataclasses.MISSING:
                    resolved_kwargs[field.name] = field.default

        # Set all field values directly (dataclasses don't have custom __init__)
        for field_name, field_value in resolved_kwargs.items():
            object.__setattr__(self, field_name, field_value)

    # Only add custom methods if this is a config class with inheritance relationships
    has_inheritance = any(
        any(is_field_sibling_inheritable(config['config_class'], f.name) for f in fields(config['config_class']))
        for config in configs
    )

    if has_inheritance:
        new_class.__new__ = __new__
        new_class.__init__ = __init__

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
            step_materialization_config, path_planning_config
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

