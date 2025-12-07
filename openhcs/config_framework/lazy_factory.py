"""Generic lazy dataclass factory using flexible resolution."""

# Standard library imports
import dataclasses
import logging
import re
import sys

from dataclasses import dataclass, fields, is_dataclass, make_dataclass, MISSING, field
from typing import Any, Callable, Dict, List, Optional, Tuple, Type, TypeVar, Union

# Note: dual_axis_resolver_recursive and lazy_placeholder imports kept inline to avoid circular imports


# Type registry for lazy dataclass to base class mapping
_lazy_type_registry: Dict[Type, Type] = {}

# Reverse registry for base class to lazy dataclass mapping (for O(1) lookup)
_base_to_lazy_registry: Dict[Type, Type] = {}

# Cache for lazy classes to prevent duplicate creation
_lazy_class_cache: Dict[str, Type] = {}


# =============================================================================
# UNIFIED NONE-FORCING: Single path for both base and lazy classes
# Replaces the old 3-stage approach (pre-process setattr, post-process Field patch)
# =============================================================================

def get_inherited_field_names(cls: Type) -> set:
    """
    Get names of fields inherited from parent dataclasses (not defined in cls itself).

    A field is "inherited" if it exists in a parent's __dataclass_fields__ but
    is NOT in this class's own __annotations__ (i.e., not redefined here).
    """
    # Get all field names from parent dataclasses
    parent_fields = set()
    for base in cls.__mro__[1:]:  # Skip cls itself
        if dataclasses.is_dataclass(base):
            parent_fields.update(base.__dataclass_fields__.keys())

    # Get cls's OWN annotations (not inherited) - check __dict__ not getattr
    own_defined = set()
    if '__annotations__' in cls.__dict__:
        own_defined = set(cls.__dict__['__annotations__'].keys())

    return parent_fields - own_defined


def rebuild_with_none_defaults(
    cls: Type,
    field_names_to_none: Optional[set] = None,
    new_name: Optional[str] = None
) -> Type:
    """
    Rebuild a dataclass via make_dataclass with None defaults for specified fields.

    This is the UNIFIED approach for both base classes (inherit_as_none) and lazy classes.
    Instead of patching Field objects after @dataclass, we rebuild with correct defaults.

    Args:
        cls: The dataclass to rebuild
        field_names_to_none: Fields that should have default=None.
                            If None, ALL fields get default=None (for lazy classes).
        new_name: Optional new class name (for lazy classes)

    Returns:
        A new class with the same fields but modified defaults
    """
    import copy

    if not dataclasses.is_dataclass(cls):
        raise ValueError(f"{cls} is not a dataclass")

    if field_names_to_none is None:
        # All fields get None (for lazy classes)
        field_names_to_none = {f.name for f in fields(cls)}

    # Build field definitions
    field_defs = []
    for f in fields(cls):
        if f.name in field_names_to_none:
            # Force None default, but preserve original default in metadata for fallback
            # This allows standalone usage to fall back to parent's static default
            new_metadata = dict(f.metadata) if f.metadata else {}
            new_metadata['_inherited_default'] = f.default if f.default is not MISSING else MISSING
            new_metadata['_inherited_default_factory'] = f.default_factory
            field_defs.append((f.name, f.type, field(default=None, metadata=new_metadata)))
        else:
            # Preserve original field (copy to avoid sharing)
            field_defs.append((f.name, f.type, copy.copy(f)))

    # Collect non-dunder attributes to preserve (methods, class vars, etc.)
    namespace = {}
    for key, value in cls.__dict__.items():
        if key.startswith('__') and key.endswith('__'):
            continue  # Skip dunders (make_dataclass will generate them)
        if key == '__dataclass_fields__':
            continue  # Will be regenerated
        namespace[key] = value

    # Keep original bases for isinstance() to work
    bases = cls.__bases__

    # Check if any base is a frozen dataclass - if so, new class must also be frozen
    is_frozen = any(
        dataclasses.is_dataclass(b) and b.__dataclass_fields__ and
        getattr(b, '__dataclass_params__', None) and b.__dataclass_params__.frozen
        for b in cls.__mro__[1:]
    )

    # Create new class
    new_cls = make_dataclass(
        new_name or cls.__name__,
        fields=field_defs,
        bases=bases,
        namespace=namespace,
        frozen=is_frozen,
    )

    # Preserve module and qualname
    new_cls.__module__ = cls.__module__
    if new_name is None:
        new_cls.__qualname__ = cls.__qualname__

    return new_cls


# ContextEventCoordinator removed - replaced with contextvars-based context system




def register_lazy_type_mapping(lazy_type: Type, base_type: Type) -> None:
    """Register mapping between lazy dataclass type and its base type."""
    _lazy_type_registry[lazy_type] = base_type
    _base_to_lazy_registry[base_type] = lazy_type


def get_base_type_for_lazy(lazy_type: Type) -> Optional[Type]:
    """Get the base type for a lazy dataclass type."""
    return _lazy_type_registry.get(lazy_type)


def is_lazy_dataclass(obj_or_type) -> bool:
    """
    Check if an object or type is a lazy dataclass.

    ANTI-DUCK-TYPING: Uses isinstance() check against LazyDataclass base class
    instead of hasattr() attribute sniffing.

    Works with both instances and types, and naturally handles Optional types
    without unwrapping.

    Args:
        obj_or_type: Either a dataclass instance or a dataclass type

    Returns:
        True if the object/type is a lazy dataclass

    Examples:
        >>> is_lazy_dataclass(PipelineConfig)  # True (type check)
        >>> is_lazy_dataclass(GlobalPipelineConfig)  # False
        >>> is_lazy_dataclass(pipeline_config_instance)  # True (instance check)
        >>> is_lazy_dataclass(LazyPathPlanningConfig)  # True
        >>> is_lazy_dataclass(PathPlanningConfig)  # False

        # Works with Optional without unwrapping!
        >>> config: Optional[PipelineConfig] = PipelineConfig()
        >>> is_lazy_dataclass(config)  # True - checks the instance, not the type annotation
    """
    if isinstance(obj_or_type, type):
        # Type check: is it a subclass of LazyDataclass?
        return issubclass(obj_or_type, LazyDataclass)
    else:
        # Instance check: is it an instance of LazyDataclass?
        return isinstance(obj_or_type, LazyDataclass)

logger = logging.getLogger(__name__)


# =============================================================================
# GENERIC SCOPE RULE: Virtual base class for global configs using __instancecheck__
# This allows isinstance() checks without actual inheritance, so lazy versions don't inherit it
# =============================================================================


class GlobalConfigMeta(type):
    """
    Metaclass that makes isinstance(obj, GlobalConfigBase) work by checking _is_global_config marker.

    This enables type-safe isinstance checks without inheritance:
        if isinstance(config, GlobalConfigBase):  # Returns True for GlobalPipelineConfig
                                                   # Returns False for PipelineConfig (lazy version)
    """
    def __instancecheck__(cls, instance):
        # Check if the instance's type has the _is_global_config marker
        return hasattr(type(instance), '_is_global_config') and type(instance)._is_global_config


class GlobalConfigBase(metaclass=GlobalConfigMeta):
    """
    Virtual base class for all global config types.

    Uses custom metaclass to check _is_global_config marker instead of actual inheritance.
    This prevents lazy versions (PipelineConfig) from being considered global configs.

    Usage:
        if isinstance(config, GlobalConfigBase):  # Generic, works for any global config

    Instead of:
        if isinstance(config, GlobalPipelineConfig):  # Hardcoded, breaks extensibility
    """
    pass


class LazyDataclass:
    """
    Base class for all lazy dataclasses created by LazyDataclassFactory.

    This enables isinstance() checks without duck typing or unwrapping:
        isinstance(config, LazyDataclass)  # Works!
        isinstance(optional_config, LazyDataclass)  # Works even for Optional!

    All lazy dataclasses inherit from this, regardless of naming convention:
    - PipelineConfig (lazy version of GlobalPipelineConfig)
    - LazyPathPlanningConfig
    - LazyWellFilterConfig
    - etc.

    ANTI-DUCK-TYPING: Use isinstance(obj, LazyDataclass) instead of hasattr() checks.
    """
    pass


def is_global_config_type(config_type: Type) -> bool:
    """
    Check if a config type is a global config (marked by @auto_create_decorator).

    GENERIC SCOPE RULE: Use this instead of hardcoding class name checks like:
        if config_class == GlobalPipelineConfig:

    Instead use:
        if is_global_config_type(config_class):

    Args:
        config_type: The config class to check

    Returns:
        True if the type is marked as a global config, False otherwise
    """
    return hasattr(config_type, '_is_global_config') and config_type._is_global_config


def is_global_config_instance(config_instance: Any) -> bool:
    """
    Check if a config instance is an instance of a global config class.

    GENERIC SCOPE RULE: Use this instead of hardcoding isinstance checks like:
        if isinstance(config, GlobalPipelineConfig):

    Instead use:
        if is_global_config_instance(config):

    Or use the virtual base class:
        if isinstance(config, GlobalConfigBase):

    Args:
        config_instance: The config instance to check

    Returns:
        True if the instance is of a global config type, False otherwise
    """
    return is_global_config_type(type(config_instance))


def get_lazy_type_for_base(base_type: Type) -> Optional[Type]:
    """Get the lazy type for a base dataclass type."""
    return _base_to_lazy_registry.get(base_type)


# =============================================================================
# Constants for lazy configuration system - simplified from class to module-level
MATERIALIZATION_DEFAULTS_PATH = "materialization_defaults"
RESOLVE_FIELD_VALUE_METHOD = "_resolve_field_value"
GET_ATTRIBUTE_METHOD = "__getattribute__"
TO_BASE_CONFIG_METHOD = "to_base_config"
WITH_DEFAULTS_METHOD = "with_defaults"
WITH_OVERRIDES_METHOD = "with_overrides"
LAZY_FIELD_DEBUG_TEMPLATE = "LAZY FIELD CREATION: {field_name} - original={original_type}, has_default={has_default}, final={final_type}"

LAZY_CLASS_NAME_PREFIX = "Lazy"

# Legacy helper functions removed - new context system handles all resolution


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


def bind_lazy_resolution_to_class(cls: Type) -> None:
    """
    Add lazy __getattribute__ to an existing class.

    This enables concrete classes (like WellFilterConfig stored in
    GlobalPipelineConfig) to resolve None values via MRO without
    changing their static defaults.

    Args:
        cls: The class to add lazy resolution to
    """
    # Don't double-bind
    if getattr(cls, '_has_lazy_resolution', False):
        return

    # Create and bind the __getattribute__ method
    lazy_getattribute = LazyMethodBindings.create_getattribute()
    cls.__getattribute__ = lazy_getattribute
    cls._has_lazy_resolution = True


@dataclass(frozen=True)
class LazyMethodBindings:
    """Declarative method bindings for lazy dataclasses."""

    @staticmethod
    def create_resolver() -> Callable[[Any, str], Any]:
        """Create field resolver method using new pure function interface."""
        from openhcs.config_framework.dual_axis_resolver import resolve_field_inheritance
        from openhcs.config_framework.context_manager import current_temp_global, extract_all_configs

        def _resolve_field_value(self, field_name: str) -> Any:
            # Get current context from contextvars
            try:
                current_context = current_temp_global.get()
                # Extract available configs from current context
                available_configs = extract_all_configs(current_context)

                # Use pure function for resolution
                return resolve_field_inheritance(self, field_name, available_configs)
            except LookupError:
                # No context available - return None (fail-loud approach)
                logger.debug(f"No context available for resolving {type(self).__name__}.{field_name}")
                return None

        return _resolve_field_value

    @staticmethod
    def create_getattribute() -> Callable[[Any, str], Any]:
        """Create lazy __getattribute__ method using new context system."""
        from openhcs.config_framework.dual_axis_resolver import resolve_field_inheritance, _has_concrete_field_override
        from openhcs.config_framework.context_manager import current_temp_global, extract_all_configs

        def _find_mro_concrete_value(base_class, name):
            """Extract common MRO traversal pattern."""
            return next((getattr(cls, name) for cls in base_class.__mro__
                        if _has_concrete_field_override(cls, name)), None)

        def __getattribute__(self: Any, name: str) -> Any:
            """
            Three-stage resolution using new context system.

            Stage 1: Check instance value
            Stage 2: Simple field path lookup in current scope's merged config
            Stage 3: Inheritance resolution using same merged context
            """
            # Stage 1: Get instance value
            value = object.__getattribute__(self, name)
            if value is not None or name not in {f.name for f in fields(self.__class__)}:
                return value

            # Stage 2: Simple field path lookup in current scope's merged global
            try:
                current_context = current_temp_global.get()
                if current_context is not None:
                    # Get the config type name for this lazy class
                    config_field_name = getattr(self, '_config_field_name', None)
                    if config_field_name:
                        try:
                            config_instance = getattr(current_context, config_field_name)
                            if config_instance is not None:
                                resolved_value = getattr(config_instance, name)
                                if resolved_value is not None:
                                    return resolved_value
                        except AttributeError:
                            # Field doesn't exist in merged config, continue to inheritance
                            pass
            except LookupError:
                # No context available, continue to inheritance
                pass

            # Stage 3: Inheritance resolution using same merged context
            try:
                current_context = current_temp_global.get()
                available_configs = extract_all_configs(current_context)
                resolved_value = resolve_field_inheritance(self, name, available_configs)

                if resolved_value is not None:
                    return resolved_value

                # For nested dataclass fields, return lazy instance
                field_obj = next((f for f in fields(self.__class__) if f.name == name), None)
                if field_obj and is_dataclass(field_obj.type):
                    return field_obj.type()

                # Fallback to inherited default from parent class (for standalone usage)
                if field_obj and '_inherited_default' in field_obj.metadata:
                    inherited = field_obj.metadata['_inherited_default']
                    if inherited is not MISSING:
                        return inherited
                    # Check for default_factory
                    factory = field_obj.metadata.get('_inherited_default_factory', MISSING)
                    if factory is not MISSING:
                        return factory()

                return None

            except LookupError:
                # No context available - fallback to MRO concrete values
                # For LazyDataclass types, get the base type; for concrete types, use self.__class__ directly
                base_type = get_base_type_for_lazy(self.__class__) or self.__class__
                mro_value = _find_mro_concrete_value(base_type, name)
                if mro_value is not None:
                    return mro_value

                # Also check inherited default metadata
                field_obj = next((f for f in fields(self.__class__) if f.name == name), None)
                if field_obj and '_inherited_default' in field_obj.metadata:
                    inherited = field_obj.metadata['_inherited_default']
                    if inherited is not MISSING:
                        return inherited
                    factory = field_obj.metadata.get('_inherited_default_factory', MISSING)
                    if factory is not MISSING:
                        return factory()

                return None
        return __getattribute__

    @staticmethod
    def create_to_base_config(base_class: Type) -> Callable[[Any], Any]:
        """Create base config converter method."""
        def to_base_config(self):
            # CRITICAL FIX: Use object.__getattribute__ to preserve raw None values
            # getattr() triggers lazy resolution, converting None to static defaults
            # None values must be preserved for dual-axis inheritance to work correctly
            #
            # Context: to_base_config() is called DURING config_context() setup (line 124 in context_manager.py)
            # If we use getattr() here, it triggers resolution BEFORE the context is fully set up,
            # causing resolution to use the wrong/stale context and losing the GlobalPipelineConfig base.
            # We must extract raw None values here, let config_context() merge them into the hierarchy,
            # and THEN resolution happens later with the properly built context.
            field_values = {f.name: object.__getattribute__(self, f.name) for f in fields(self)}
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
            lazy_nested_type = None  # Track if we created a lazy nested type
            if is_dataclass(field.type):
                # SIMPLIFIED: Create lazy version using simple factory
                lazy_nested_type = LazyDataclassFactory.make_lazy_simple(
                    base_class=field.type,
                    lazy_class_name=f"Lazy{field.type.__name__}"
                )
                field_type = lazy_nested_type
                logger.debug(f"Created lazy class for {field.name}: {field.type} -> {lazy_nested_type}")

            # Complex type logic: make Optional if no default, preserve existing Optional types
            if is_already_optional or not has_default:
                final_field_type = Union[field_type, type(None)] if not is_already_optional else field_type
            else:
                final_field_type = field_type

            # CRITICAL FIX: For lazy configs, nested dataclass fields should use default_factory
            # to provide lazy instances (e.g., LazyPathPlanningConfig), not None.
            # This allows getattr(pipeline_config, 'path_planning_config') to return an instance.
            # Non-dataclass fields still default to None for placeholder inheritance.
            # CRITICAL: Always preserve metadata from original field (e.g., ui_hidden flag)
            if lazy_nested_type is not None:
                # Nested dataclass field: use default_factory so accessing returns an instance
                # This matches AbstractStep pattern: napari_streaming_config = LazyNapariStreamingConfig()
                field_def = (field.name, final_field_type, dataclasses.field(default_factory=lazy_nested_type, metadata=field.metadata))
            elif field.metadata:
                # CRITICAL FIX: For lazy configs, ALL non-dataclass fields should default to None
                # This enables proper inheritance from parent configs and placeholder styling
                # We preserve metadata but override all defaults to None
                field_def = (field.name, final_field_type, dataclasses.field(default=None, metadata=field.metadata))
            else:
                # CRITICAL FIX: For lazy configs, ALL non-dataclass fields should default to None
                # This enables proper inheritance from parent configs and placeholder styling
                field_def = (field.name, final_field_type, dataclasses.field(default=None))

            lazy_field_definitions.append(field_def)

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
            not has_inherit_as_none_marker
        )

        # Determine inheritance: always include LazyDataclass, optionally include base_class
        if has_unsafe_metaclass:
            # Base class has unsafe custom metaclass - don't inherit, just copy interface
            print(f"🔧 LAZY FACTORY: {base_class.__name__} has custom metaclass {base_metaclass.__name__}, avoiding inheritance")
            bases = (LazyDataclass,)  # Only inherit from LazyDataclass
        else:
            # Safe to inherit from regular dataclass
            bases = (base_class, LazyDataclass)  # Inherit from both

        # Single make_dataclass call - no duplication
        lazy_class = make_dataclass(
            lazy_class_name,
            LazyDataclassFactory._introspect_dataclass_fields(
                base_class, debug_template, global_config_type, parent_field_path, parent_instance_provider
            ),
            bases=bases,
            frozen=True
        )

        # Add constructor parameter tracking to detect user-set fields
        original_init = lazy_class.__init__
        def __init_with_tracking__(self, **kwargs):
            # Track which fields were explicitly passed to constructor
            object.__setattr__(self, '_explicitly_set_fields', set(kwargs.keys()))
            # Store the global config type for inheritance resolution
            object.__setattr__(self, '_global_config_type', global_config_type)
            # Store the config field name for simple field path lookup
            import re
            def _camel_to_snake_local(name: str) -> str:
                s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
                return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()
            config_field_name = _camel_to_snake_local(base_class.__name__)
            object.__setattr__(self, '_config_field_name', config_field_name)
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

        # CRITICAL: Preserve original module for proper imports in generated code
        # make_dataclass() sets __module__ to the caller's module (lazy_factory.py)
        # We need to set it to the base class's original module for correct import paths
        lazy_class.__module__ = base_class.__module__

        # Automatically register the lazy dataclass with the type registry
        register_lazy_type_mapping(lazy_class, base_class)

        # Cache the created class to prevent duplicates

        # CRITICAL: Lazy types are NOT global configs, even if their base is
        # GlobalPipelineConfig is global, but PipelineConfig (lazy) is NOT
        lazy_class._is_global_config = False
        _lazy_class_cache[cache_key] = lazy_class

        return lazy_class





    @staticmethod
    def make_lazy_simple(
        base_class: Type,
        lazy_class_name: str = None
    ) -> Type:
        """
        Create lazy dataclass using new contextvars system.

        SIMPLIFIED: No complex hierarchy providers or field path detection needed.
        Uses new contextvars system for all resolution.

        Args:
            base_class: Base dataclass to make lazy
            lazy_class_name: Optional name for the lazy class

        Returns:
            Generated lazy dataclass with contextvars-based resolution
        """
        # Generate class name if not provided
        lazy_class_name = lazy_class_name or f"Lazy{base_class.__name__}"

        # Simple provider that uses new contextvars system
        def simple_provider():
            """Simple provider using new contextvars system."""
            return base_class()  # Lazy __getattribute__ handles resolution

        return LazyDataclassFactory._create_lazy_dataclass_unified(
            base_class=base_class,
            instance_provider=simple_provider,
            lazy_class_name=lazy_class_name,
            debug_template=f"Simple contextvars resolution for {base_class.__name__}",
            use_recursive_resolution=False,
            fallback_chain=[],
            global_config_type=None,
            parent_field_path=None,
            parent_instance_provider=None
        )

    # All legacy methods removed - use make_lazy_simple() for all use cases


# Generic utility functions for clean thread-local storage management
def ensure_global_config_context(global_config_type: Type, global_config_instance: Any) -> None:
    """Ensure proper thread-local storage setup for any global config type."""
    from openhcs.config_framework.global_config import set_global_config_for_editing
    set_global_config_for_editing(global_config_type, global_config_instance)


# ContextProvider infrastructure removed - was dead code feeding broken frame.f_locals manipulation




def resolve_lazy_configurations_for_serialization(data: Any) -> Any:
    """
    Recursively resolve lazy dataclass instances to concrete values for serialization.

    CRITICAL: This function must be called WITHIN a config_context() block!
    The context provides the hierarchy for lazy resolution.

    How it works:
    1. For lazy dataclasses: Access fields with getattr() to trigger resolution
    2. The lazy __getattribute__ uses the active config_context() to resolve None values
    3. Convert resolved values to base config for pickling

    Example (from README.md):
        with config_context(orchestrator.pipeline_config):
            # Lazy resolution happens here via context
            resolved_steps = resolve_lazy_configurations_for_serialization(steps)
    """
    # Check if this is a lazy dataclass
    base_type = get_base_type_for_lazy(type(data))
    if base_type is not None:
        # This is a lazy dataclass - resolve fields using getattr() within the active context
        # getattr() triggers lazy __getattribute__ which uses config_context() for resolution
        resolved_fields = {}
        for f in fields(data):
            # CRITICAL: Use getattr() to trigger lazy resolution via context
            # The active config_context() provides the hierarchy for resolution
            resolved_value = getattr(data, f.name)
            resolved_fields[f.name] = resolved_value

        # Create base config instance with resolved values
        resolved_data = base_type(**resolved_fields)
    else:
        # Not a lazy dataclass
        resolved_data = data

    # Recursively process nested structures based on type
    if is_dataclass(resolved_data) and not isinstance(resolved_data, type):
        # Process dataclass fields recursively
        logger.debug(f"Resolving fields for {type(resolved_data).__name__}: {[f.name for f in fields(resolved_data)]}")
        resolved_fields = {}
        for f in fields(resolved_data):
            field_value = getattr(resolved_data, f.name)
            logger.debug(f"Resolving {type(resolved_data).__name__}.{f.name} = {type(field_value).__name__}")
            resolved_fields[f.name] = resolve_lazy_configurations_for_serialization(field_value)
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

    # Mathematical simplification: Convert verbose loop to unified comprehension
    from openhcs.config_framework.placeholder import LazyDefaultPlaceholderService
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
                # Rebuild nested dataclass recursively
                # All @global_pipeline_config types now have lazy resolution via _has_lazy_resolution
                nested_result = rebuild_lazy_config_with_new_global_reference(raw_value, new_global_config, global_config_type)
                return nested_result
            except Exception as e:
                logger.debug(f"Failed to rebuild nested config {field_obj.name}: {e}")
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
            # UNIFIED NONE-FORCING: Single make_dataclass rebuild instead of old 3-stage approach
            if inherit_as_none:
                # Mark the class for inherit_as_none processing (used by lazy factory metaclass check)
                actual_cls._inherit_as_none = True

                # Rebuild class with None defaults for inherited fields
                # This replaces the old pre-process setattr + post-process Field patching
                inherited_fields = get_inherited_field_names(actual_cls)
                if inherited_fields:
                    actual_cls = rebuild_with_none_defaults(actual_cls, inherited_fields)

            # Generate field and class names
            field_name = _camel_to_snake(actual_cls.__name__)
            lazy_class_name = f"{LAZY_CONFIG_PREFIX}{actual_cls.__name__}"

            # Mark class with ui_hidden metadata for UI layer to check
            # This allows the config to remain in the context (for lazy resolution)
            # while being hidden from UI rendering
            if ui_hidden:
                actual_cls._ui_hidden = True

            # Check if class is abstract (has unimplemented abstract methods)
            # Abstract classes should NEVER be injected into GlobalPipelineConfig
            # because they can't be instantiated
            # NOTE: We need to check if the class ITSELF is abstract, not just if it inherits from ABC
            # Concrete subclasses of abstract classes should still be injected
            # We check for __abstractmethods__ attribute which exists even before @dataclass runs
            # (it's set by ABCMeta when the class is created)
            is_abstract = hasattr(actual_cls, '__abstractmethods__') and len(actual_cls.__abstractmethods__) > 0

            # Add to pending injections for field injection
            # Skip injection for abstract classes (they can't be instantiated)
            # For concrete classes: inject even if ui_hidden (needed for lazy resolution context)
            if not is_abstract:
                _pending_injections[target_class_name]['configs_to_inject'].append({
                    'config_class': actual_cls,
                    'field_name': field_name,
                    'lazy_class_name': lazy_class_name,
                    'optional': optional,  # Store the optional flag
                    'inherit_as_none': inherit_as_none,  # Store the inherit_as_none flag
                    'ui_hidden': ui_hidden  # Store the ui_hidden flag for field metadata
                })

            # Immediately create lazy version of this config (not dependent on injection)


            lazy_class = LazyDataclassFactory.make_lazy_simple(
                base_class=actual_cls,
                lazy_class_name=lazy_class_name
            )

            # Export lazy class to config module immediately
            config_module = sys.modules[actual_cls.__module__]
            setattr(config_module, lazy_class_name, lazy_class)

            # Also mark lazy class with ui_hidden metadata
            if ui_hidden:
                lazy_class._ui_hidden = True

            # Note: No Stage 3 post-processing needed!
            # - Base class: rebuilt via rebuild_with_none_defaults() above
            # - Lazy class: _introspect_dataclass_fields() already sets None defaults

            # PHASE 2 FIX: Add lazy resolution to the CONCRETE class
            # This allows GlobalPipelineConfig's nested configs to auto-resolve None values
            # without needing to look up the lazy type. Static defaults are preserved.
            bind_lazy_resolution_to_class(actual_cls)

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

    # Mathematical simplification: Unified field construction with algebraic common factors
    def create_field_definition(config):
        """Create field definition with optional and inherit_as_none support."""
        field_type = config['config_class']
        is_optional = config.get('optional', False)
        is_ui_hidden = config.get('ui_hidden', False)

        # Algebraic simplification: factor out common default_value logic
        if is_optional:
            field_type = Union[field_type, type(None)]
            default_value = None
        else:
            # CRITICAL: GlobalPipelineConfig needs default_factory to create instances with defaults
            # PipelineConfig (created by make_lazy_simple) automatically gets default=None
            # So we use default_factory here for GlobalPipelineConfig fields
            default_value = field(default_factory=field_type, metadata={'ui_hidden': is_ui_hidden})

        return (config['field_name'], field_type, default_value)

    all_fields = existing_fields + [create_field_definition(config) for config in configs]

    # Direct dataclass recreation - fail-loud
    new_class = make_dataclass(
        target_class.__name__,
        all_fields,
        bases=target_class.__bases__,
        frozen=target_class.__dataclass_params__.frozen
    )

    # CRITICAL: Preserve original module for proper imports in generated code
    # make_dataclass() sets __module__ to the caller's module (lazy_factory.py)
    # We need to set it to the target class's original module for correct import paths
    new_class.__module__ = target_class.__module__


    # CRITICAL: Preserve _is_global_config marker for GlobalPipelineConfig
    # This marker is set by @auto_create_decorator but lost when make_dataclass creates a new class
    if hasattr(target_class, '_is_global_config') and target_class._is_global_config:
        new_class._is_global_config = True
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
        lazy_class = LazyDataclassFactory.make_lazy_simple(
            base_class=config['config_class'],
            lazy_class_name=config['lazy_class_name']
        )
        _register_lazy_class(lazy_class, config['lazy_class_name'], config['config_class'].__module__)

    # Create lazy version of the updated global config itself with proper naming
    # Global configs must start with GLOBAL_CONFIG_PREFIX - fail-loud if not
    if not target_class.__name__.startswith(GLOBAL_CONFIG_PREFIX):
        raise ValueError(f"Target class '{target_class.__name__}' must start with '{GLOBAL_CONFIG_PREFIX}' prefix")

    # Remove global prefix (GlobalPipelineConfig → PipelineConfig)
    lazy_global_class_name = target_class.__name__[len(GLOBAL_CONFIG_PREFIX):]

    lazy_global_class = LazyDataclassFactory.make_lazy_simple(
        base_class=new_class,
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

    # Mark this class as a global config for isinstance checks via GlobalConfigBase
    global_config_class._is_global_config = True

    decorator_name = _camel_to_snake(global_config_class.__name__)
    decorator = create_global_default_decorator(global_config_class)

    # Export decorator to module globals
    module = sys.modules[global_config_class.__module__]
    setattr(module, decorator_name, decorator)

    # Lazy global config will be created after field injection

    return global_config_class






