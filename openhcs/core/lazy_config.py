"""Generic lazy dataclass factory using flexible resolution."""

# Standard library imports
import dataclasses
import inspect
import logging
import re
import threading
import sys
import weakref
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
# Note: dual_axis_resolver_recursive and lazy_placeholder imports kept inline to avoid circular imports


# Type registry for lazy dataclass to base class mapping
_lazy_type_registry: Dict[Type, Type] = {}

# Cache for lazy classes to prevent duplicate creation
_lazy_class_cache: Dict[str, Type] = {}


class ContextEventCoordinator:
    """Generic event coordinator for any global config type changes."""

    def __init__(self):
        # Type-specific listeners: Dict[Type, List[weakref]]
        self._listeners: Dict[Type, List] = {}

    def register_listener(self, form_manager, config_type: Type) -> None:
        """Register form manager for specific config type events."""
        if config_type not in self._listeners:
            self._listeners[config_type] = []
        self._listeners[config_type].append(weakref.ref(form_manager))

    def emit_context_change(self, config_type: Type) -> None:
        """Emit context change event for specific config type with shared temporary context."""
        if config_type not in self._listeners:
            return

        # Get all active form managers for this config type
        active_managers = []
        for weak_ref in list(self._listeners[config_type]):
            if (form_manager := weak_ref()) is not None:
                active_managers.append(form_manager)

        if not active_managers:
            return

        # Build shared temporary context from all form managers
        shared_context = self._build_shared_temporary_context(config_type, active_managers)

        # Refresh all forms with the shared context
        for form_manager in active_managers:
            form_manager.refresh_placeholder_text_with_context(shared_context)

    def _build_shared_temporary_context(self, global_config_type, form_managers):
        """Build shared temporary context from all form managers in the same config window."""
        print(f"🔍 BUILD SHARED CONTEXT: Starting with global_config_type={global_config_type}")

        # CRITICAL FIX: Use current form context that respects shared reset state
        # Find a form manager that can build context from current form values
        base_context = None
        for manager in form_managers:
            if hasattr(manager, '_build_context_from_current_form_values'):
                base_context = manager._build_context_from_current_form_values()
                print(f"🔍 BUILD SHARED CONTEXT: Using current form context (respects shared reset state)")
                break

        # Fallback to orchestrator context if no form context available
        if not base_context:
            for manager in form_managers:
                if hasattr(manager, 'context_provider') and manager.context_provider:
                    base_context = manager.context_provider()
                    print(f"🔍 BUILD SHARED CONTEXT: Using orchestrator context as fallback")
                    break

        # Final fallback to recursive resolver context discovery
        if not base_context:
            from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver
            resolver = get_recursive_resolver()
            # The recursive resolver will discover context internally
            print(f"🔍 BUILD SHARED CONTEXT: Using recursive resolver as final fallback")

        print(f"🔍 BUILD SHARED CONTEXT: base_context={base_context}")
        if not base_context:
            print(f"🔍 BUILD SHARED CONTEXT: No base context, returning None")
            return None

        # Simple approach: collect current form values and build basic context updates
        context_updates = {}
        print(f"🔍 BUILD SHARED CONTEXT: Processing {len(form_managers)} form managers")

        for i, manager in enumerate(form_managers):
            print(f"🔍 BUILD SHARED CONTEXT: Manager {i}: field_id={getattr(manager, 'field_id', 'MISSING')}, dataclass_type={getattr(manager, 'dataclass_type', 'MISSING')}")

            if hasattr(manager, 'field_id') and hasattr(manager, 'get_current_values'):
                # Skip root config manager (field_id matches class name)
                if hasattr(manager, 'dataclass_type') and manager.dataclass_type and manager.field_id == manager.dataclass_type.__name__:
                    print(f"🔍 BUILD SHARED CONTEXT: Skipping root config {manager.field_id}")
                    continue

                # Get current form values
                current_values = manager.get_current_values()
                print(f"🔍 BUILD SHARED CONTEXT: {manager.field_id} current_values={current_values}")

                if current_values and hasattr(manager, 'dataclass_type') and manager.dataclass_type:
                    # Filter out None values to allow lazy resolution to work
                    filtered_values = {k: v for k, v in current_values.items() if v is not None}
                    print(f"🔍 BUILD SHARED CONTEXT: {manager.field_id} filtered_values={filtered_values}")

                    if filtered_values:  # Only create instance if there are non-None values
                        # Check if the dataclass type is abstract and can't be instantiated
                        import inspect
                        if inspect.isabstract(manager.dataclass_type):
                            print(f"🔍 BUILD SHARED CONTEXT: Skipping {manager.field_id} - abstract class {manager.dataclass_type.__name__}")
                        else:
                            # Build dataclass instance with only non-None values (allows lazy resolution for None fields)
                            current_instance = manager.dataclass_type(**filtered_values)
                            context_updates[manager.field_id] = current_instance
                            print(f"🔍 BUILD SHARED CONTEXT: Added {manager.field_id}={current_instance}")
                    else:
                        print(f"🔍 BUILD SHARED CONTEXT: Skipping {manager.field_id} - no non-None values")
                else:
                    print(f"🔍 BUILD SHARED CONTEXT: Skipping {manager.field_id} - no current values or dataclass type")
            else:
                print(f"🔍 BUILD SHARED CONTEXT: Skipping manager {i} - missing field_id or get_current_values")

        print(f"🔍 BUILD SHARED CONTEXT: context_updates={context_updates}")

        # Build final shared context with current form values
        if context_updates:
            from dataclasses import replace
            result = replace(base_context, **context_updates)
            print(f"🔍 BUILD SHARED CONTEXT: Returning updated context: {result}")
            return result

        print(f"🔍 BUILD SHARED CONTEXT: No context updates, returning base context")
        return base_context




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

LAZY_CLASS_NAME_PREFIX = "Lazy"

# Core helper functions to eliminate duplication
def _get_current_config(config_type):
    """Get current config using recursive resolver context discovery."""
    from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver
    # The recursive resolver handles context discovery internally
    # For now, return None and let the resolver handle it
    return None

# Helper functions removed - dual-axis resolver handles all resolution

# ResolutionConfig system removed - dual-axis resolver handles all resolution


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
    def create_resolver() -> Callable[[Any, str], Any]:
        """Create field resolver method using recursive dual-axis resolution."""
        from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver

        def _resolve_field_value(self, field_name: str) -> Any:
            # Use recursive dual-axis resolver - handles all resolution
            resolver = get_recursive_resolver()
            return resolver.resolve_field(self, field_name)

        return _resolve_field_value

    @staticmethod
    def create_getattribute() -> Callable[[Any, str], Any]:
        """Create lazy __getattribute__ method using recursive dual-axis resolution."""
        from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver
        from openhcs.core.lazy_placeholder import _has_concrete_field_override

        def _find_mro_concrete_value(base_class, name):
            """Extract common MRO traversal pattern."""
            return next((getattr(cls, name) for cls in base_class.__mro__
                        if _has_concrete_field_override(cls, name)), None)

        def _try_global_context_value(self, base_class, name):
            """Extract global context resolution logic using recursive dual-axis resolution."""
            if not hasattr(self, '_global_config_type'):
                return None

            # Use recursive dual-axis resolver
            resolver = get_recursive_resolver()
            resolved_value = resolver.resolve_field(self, name)

            if resolved_value is not None:
                return resolved_value

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

            # Fallback to recursive dual-axis resolution if no inheritance fix needed
            try:
                # Check if this is a nested config field first
                field_obj = next((f for f in fields(self.__class__) if f.name == name), None)
                if field_obj and is_dataclass(field_obj.type):
                    # CRITICAL FIX: For nested config fields, always return lazy instance
                    # This preserves None raw values for placeholder behavior while still
                    # allowing the lazy instance to resolve through dual-axis resolution
                    return field_obj.type()

                # For scalar fields, use recursive dual-axis resolver
                resolver = get_recursive_resolver()
                resolved_value = resolver.resolve_field(self, name)
                if resolved_value is not None:
                    return resolved_value

                # If no context found, try the old resolve method as final fallback
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
        def to_base_config(self):
            # Mathematical simplification: Convert loop to comprehension
            field_values = {f.name: getattr(self, f.name) for f in fields(self)}
            return base_class(**field_values)
        return to_base_config

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

        # ResolutionConfig system removed - dual-axis resolver handles all resolution

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
            RESOLVE_FIELD_VALUE_METHOD: LazyMethodBindings.create_resolver(),
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
            # Check if we're in a context where stack introspection should find context
            current_context = _get_current_config(global_config_type)

            if current_context is None and HAS_PYQT:
                # Check if we're in a PyQt app context where this shouldn't happen
                app_instance = QApplication.instance()
                if app_instance and hasattr(app_instance, 'global_config'):
                    logger.warning(
                        f"🚨 ARCHITECTURE WARNING: Static fallback used for {base_class.__name__}.{field_name} "
                        f"in PyQt app context where stack introspection should find context. "
                        f"This indicates a context discovery bug."
                    )

            # Use static default
            static_instance = base_class()
            static_value = _get_raw_field_value(static_instance, field_name)
            return static_value

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
    import dataclasses
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
        """Simplified provider that delegates to dual-axis resolver."""
        from openhcs.core.dual_axis_resolver_recursive import get_recursive_resolver

        # Create a dummy instance to use with the dual-axis resolver
        dummy_instance = base_class()
        resolver = get_recursive_resolver()

        # Get all fields that need resolution
        global_config_fields = {f.name for f in fields(global_config_type)} if global_config_type else set()
        all_resolvable_fields = inherited_fields | own_fields | global_config_fields

        # Create config instance with dual-axis resolved fields
        config_instance = type('FieldLevelInheritanceConfig', (), {})()

        for field_name in all_resolvable_fields:
            # Use dual-axis resolver for all field resolution
            resolved_value = resolver.resolve_field(dummy_instance, field_name)
            setattr(config_instance, field_name, resolved_value)

        return config_instance

    return field_level_provider


# Generic utility functions for clean thread-local storage management
def ensure_global_config_context(global_config_type: Type, global_config_instance: Any) -> None:
    """Ensure proper thread-local storage setup for any global config type."""
    from openhcs.core.context.global_config import set_global_config_for_editing
    set_global_config_for_editing(global_config_type, global_config_instance)


# Context provider registry and metaclass for automatic registration
CONTEXT_PROVIDERS = {}

from abc import ABCMeta

class ContextProviderMeta(ABCMeta):
    """Metaclass for automatic registration of context provider classes."""

    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)

        # Only register concrete classes that have a context_type attribute
        context_type = getattr(new_class, '_context_type', None)
        if context_type and not getattr(new_class, '__abstractmethods__', None):
            CONTEXT_PROVIDERS[context_type] = new_class
            logger.debug(f"Auto-registered context provider: {context_type} -> {name}")

        return new_class


class ContextProvider(metaclass=ContextProviderMeta):
    """Base class for objects that can provide context for lazy resolution."""
    _context_type: Optional[str] = None  # Override in subclasses


def _detect_context_type(obj: Any) -> Optional[str]:
    """
    Detect what type of context object this is using registered providers.

    Returns the context type name or None if not a recognized context type.
    """
    # Check for functions first (simple callable check)
    if callable(obj) and hasattr(obj, '__name__'):
        return "function"

    # Check if object is an instance of any registered context provider
    for context_type, provider_class in CONTEXT_PROVIDERS.items():
        if isinstance(obj, provider_class):
            return context_type

    return None


# Generic context injection utilities
class ContextInjector:
    """Generic context injection for dual-axis resolution."""

    @staticmethod
    def inject_context(context_obj: Any, context_type: str = "step") -> None:
        """
        Inject context into call stack for dual-axis resolution.

        Args:
            context_obj: The context object to inject
            context_type: Type of context (step, pipeline, orchestrator, etc.)
        """
        import inspect
        frame = inspect.currentframe().f_back  # Get caller's frame
        context_var_name = f"__{context_type}_context__"
        frame.f_locals[context_var_name] = context_obj

    @staticmethod
    def with_context(context_obj: Any, context_type: str = "step"):
        """
        Context manager for temporary context injection.

        Usage:
            with ContextInjector.with_context(step_obj, "step"):
                # Lazy resolution will find step_obj as context
                lazy_config.some_field  # Uses step_obj for resolution
        """
        import inspect
        from contextlib import contextmanager

        @contextmanager
        def _context_manager():
            frame = inspect.currentframe().f_back.f_back  # Get caller's caller frame
            context_var_name = f"__{context_type}_context__"
            frame.f_locals[context_var_name] = context_obj
            try:
                yield
            finally:
                if context_var_name in frame.f_locals:
                    del frame.f_locals[context_var_name]

        return _context_manager()




def resolve_lazy_configurations_for_serialization(data: Any) -> Any:
    """Recursively resolve lazy dataclass instances to concrete values for serialization."""
    # Resolve the object itself if it's a lazy dataclass
    resolved_data = (data.to_base_config()
                    if get_base_type_for_lazy(type(data)) is not None
                    else data)

    # CRITICAL FIX: Handle step objects (non-dataclass objects with dataclass attributes)
    step_context_type = _detect_context_type(resolved_data)
    if step_context_type:
        # This is a context object - inject it for its dataclass attributes
        import inspect
        frame = inspect.currentframe()
        context_var_name = f"__{step_context_type}_context__"
        frame.f_locals[context_var_name] = resolved_data
        print(f"🔍 CONTEXT_INJECTION DEBUG: Injected {context_var_name} = {type(resolved_data).__name__}")

        try:
            # Process step attributes recursively
            resolved_attrs = {}
            for attr_name in dir(resolved_data):
                if attr_name.startswith('_'):
                    continue
                try:
                    attr_value = getattr(resolved_data, attr_name)
                    if not callable(attr_value):  # Skip methods
                        print(f"🔍 STEP_ATTR_DEBUG: Resolving {type(resolved_data).__name__}.{attr_name} = {type(attr_value).__name__}")
                        resolved_attrs[attr_name] = resolve_lazy_configurations_for_serialization(attr_value)
                except (AttributeError, Exception):
                    continue

            # Handle function objects specially - they can't be recreated with __new__
            if step_context_type == "function":
                # For functions, just process attributes for resolution but return original function
                # The resolved config values will be stored in func plan by compiler
                return resolved_data

            # Create new step object with resolved attributes
            # CRITICAL FIX: Copy all original attributes using __dict__ to preserve everything
            new_step = type(resolved_data).__new__(type(resolved_data))

            # Copy all attributes from the original object's __dict__
            if hasattr(resolved_data, '__dict__'):
                new_step.__dict__.update(resolved_data.__dict__)

            # Update with resolved config attributes (these override the originals)
            for attr_name, attr_value in resolved_attrs.items():
                setattr(new_step, attr_name, attr_value)
            return new_step
        finally:
            if context_var_name in frame.f_locals:
                del frame.f_locals[context_var_name]
            del frame

    # Recursively process nested structures based on type
    elif is_dataclass(resolved_data) and not isinstance(resolved_data, type):
        # Process dataclass fields recursively - inline field processing pattern
        # CRITICAL FIX: Inject parent object as context for sibling config inheritance
        context_type = _detect_context_type(resolved_data) or "dataclass"  # Default to "dataclass" for generic dataclasses
        import inspect
        frame = inspect.currentframe()
        context_var_name = f"__{context_type}_context__"
        frame.f_locals[context_var_name] = resolved_data
        print(f"🔍 CONTEXT_INJECTION DEBUG: Injected {context_var_name} = {type(resolved_data).__name__}")

        # Add debug to see which fields are being resolved
        print(f"🔍 FIELD_RESOLUTION DEBUG: Resolving fields for {type(resolved_data).__name__}: {[f.name for f in fields(resolved_data)]}")

        try:
            resolved_fields = {}
            for f in fields(resolved_data):
                field_value = getattr(resolved_data, f.name)
                print(f"🔍 FIELD_DEBUG: Resolving {type(resolved_data).__name__}.{f.name} = {type(field_value).__name__}")
                resolved_fields[f.name] = resolve_lazy_configurations_for_serialization(field_value)
            return type(resolved_data)(**resolved_fields)
        finally:
            if context_var_name in frame.f_locals:
                del frame.f_locals[context_var_name]
            del frame

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

    # Mathematical simplification: Convert verbose loop to unified comprehension
    from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
    field_values = {
        f.name: (getattr(source_config, f.name) if preserve_values
                else f.type() if is_dataclass(f.type) and LazyDefaultPlaceholderService.has_lazy_resolution(f.type)
                else None)
        for f in fields(dataclass_type)
    }

    return dataclass_type(**field_values)





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
                        # Check if field has a concrete default value in THIS class definition (not inherited)
                        if field_name in actual_cls.__dict__:  # Only fields defined in THIS class
                            field_value = actual_cls.__dict__[field_name]
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
                                # CRITICAL: Force the field to be seen as locally defined by @dataclass
                                # We need to ensure @dataclass processes this as a local field, not inherited

                                # 1. Set the class attribute to None
                                setattr(actual_cls, field_name, None)
                                fields_set_to_none.add(field_name)

                                # 2. Ensure annotation exists in THIS class
                                if not hasattr(actual_cls, '__annotations__'):
                                    actual_cls.__annotations__ = {}
                                actual_cls.__annotations__[field_name] = field_type

                            processed_fields.add(field_name)

                # Note: We modify class attributes here, but we also need to fix the dataclass
                # field definitions after @dataclass runs, since @dataclass processes the MRO
                # and may use parent class field definitions instead of our modified attributes.

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

            # CRITICAL: Post-process dataclass fields after @dataclass has run
            # This fixes the constructor behavior for inherited fields that should be None
            if inherit_as_none and hasattr(actual_cls, '__dataclass_fields__'):
                _fix_dataclass_field_defaults_post_processing(actual_cls, fields_set_to_none)

            return actual_cls

        # Handle both @decorator and @decorator() usage
        if cls is None:
            # Called with parentheses: @decorator(optional=True)
            return decorator
        else:
            # Called without parentheses: @decorator
            return decorator(cls)

    return global_default_decorator


def _fix_dataclass_field_defaults_post_processing(cls: Type, fields_set_to_none: set) -> None:
    """
    Fix dataclass field defaults after @dataclass has processed the class.

    This is necessary because @dataclass processes the MRO and may use parent class
    field definitions instead of our modified class attributes. We need to ensure
    that fields we set to None actually use None as the default in the constructor.
    """
    import dataclasses

    # Store the original __init__ method
    original_init = cls.__init__

    def custom_init(self, **kwargs):
        """Custom __init__ that ensures inherited fields use None defaults."""
        # For fields that should be None, set them to None if not explicitly provided
        for field_name in fields_set_to_none:
            if field_name not in kwargs:
                kwargs[field_name] = None

        # Call the original __init__ with modified kwargs
        original_init(self, **kwargs)

    # Replace the __init__ method
    cls.__init__ = custom_init

    # Also update the field defaults for consistency
    for field_name in fields_set_to_none:
        if field_name in cls.__dataclass_fields__:
            # Get the field object
            field_obj = cls.__dataclass_fields__[field_name]

            # Update the field default to None (overriding any parent class default)
            field_obj.default = None
            field_obj.default_factory = dataclasses.MISSING

            # Also ensure the class attribute is None (should already be set, but double-check)
            setattr(cls, field_name, None)



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

    # Mathematical simplification: Unified field construction with algebraic common factors
    def create_field_definition(config):
        """Create field definition with optional and inherit_as_none support."""
        field_type = config['config_class']
        is_optional = config.get('optional', False)

        # Algebraic simplification: factor out common default_value logic
        if is_optional:
            field_type = Union[field_type, type(None)]
            default_value = None
        else:
            # Both inherit_as_none and regular cases use same default factory
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

    # Sibling inheritance is now handled by the dual-axis resolver system

    # Direct module replacement
    module = sys.modules[target_class.__module__]
    setattr(module, target_class.__name__, new_class)
    globals()[target_class.__name__] = new_class

    # Mathematical simplification: Extract common module assignment pattern
    def _register_lazy_class(lazy_class, class_name, module_name):
        """Register lazy class in both module and global namespace."""
        setattr(sys.modules[module_name], class_name, lazy_class)
        globals()[class_name] = lazy_class

    # Create lazy classes and recreate PipelineConfig inline
    for config in configs:
        lazy_class = LazyDataclassFactory.make_lazy_with_field_level_auto_hierarchy(
            base_class=config['config_class'],
            global_config_type=new_class,
            field_path=config['field_name'],
            lazy_class_name=config['lazy_class_name']
        )
        _register_lazy_class(lazy_class, config['lazy_class_name'], config['config_class'].__module__)

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

    # Use extracted helper for consistent registration
    _register_lazy_class(lazy_global_class, lazy_global_class_name, target_class.__module__)





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







