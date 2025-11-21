"""Generic lazy dataclass factory using flexible resolution."""

# Standard library imports
import dataclasses
import logging
import re
import sys
from abc import ABCMeta
from dataclasses import dataclass, fields, is_dataclass, make_dataclass, MISSING, field
from typing import Any, Callable, Dict, List, Optional, Tuple, Type, TypeVar, Union

# OpenHCS imports
from openhcs.config_framework.placeholder import LazyDefaultPlaceholderService
from openhcs.core.auto_register_meta import AutoRegisterMeta, RegistryConfig
# Note: dual_axis_resolver_recursive and lazy_placeholder imports kept inline to avoid circular imports


# Type registry for lazy dataclass to base class mapping
_lazy_type_registry: Dict[Type, Type] = {}

# Reverse registry for base class to lazy dataclass mapping (for O(1) lookup)
_base_to_lazy_registry: Dict[Type, Type] = {}

# Cache for lazy classes to prevent duplicate creation
_lazy_class_cache: Dict[str, Type] = {}


# ContextEventCoordinator removed - replaced with contextvars-based context system




def register_lazy_type_mapping(lazy_type: Type, base_type: Type) -> None:
    """Register mapping between lazy dataclass type and its base type."""
    _lazy_type_registry[lazy_type] = base_type
    _base_to_lazy_registry[base_type] = lazy_type


def get_base_type_for_lazy(lazy_type: Type) -> Optional[Type]:
    """Get the base type for a lazy dataclass type."""
    return _lazy_type_registry.get(lazy_type)


def get_lazy_type_for_base(base_type: Type) -> Optional[Type]:
    """Get the lazy type for a base dataclass type."""
    return _base_to_lazy_registry.get(base_type)

# Optional imports (handled gracefully)
try:
    from PyQt6.QtWidgets import QApplication
    HAS_PYQT = True
except ImportError:
    QApplication = None
    HAS_PYQT = False

logger = logging.getLogger(__name__)


# GENERIC SCOPE RULE: Virtual base class for global configs using __instancecheck__
# This allows isinstance() checks without actual inheritance, so lazy versions don't inherit it
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
        if isinstance(config, GlobalConfigBase):

    This uses the GlobalConfigBase virtual base class with custom __instancecheck__.

    Args:
        config_instance: The config instance to check

    Returns:
        True if the instance is of a global config type, False otherwise
    """
    return isinstance(config_instance, GlobalConfigBase)


# PERFORMANCE: Class-level cache for lazy dataclass field resolution
# Shared across all instances to survive instance recreation (e.g., in pipeline editor)
# Cache key: (lazy_class_name, field_name, context_token) -> resolved_value
_lazy_resolution_cache: Dict[Tuple[str, str, int], Any] = {}
_LAZY_CACHE_MAX_SIZE = 10000  # Prevent unbounded growth

# PERFORMANCE: Cache field names per class to avoid repeated fields() introspection
# fields() is expensive - it introspects the class every time
# This cache maps class -> frozenset of field names for O(1) membership testing
_class_field_names_cache: Dict[Type, frozenset] = {}

# CRITICAL: Contextvar to disable cache during LiveContextResolver operations
# Flash detection uses LiveContextResolver with historical snapshots (before/after tokens)
# The class-level cache uses current token, which breaks flash detection
# When this is True, skip the cache and let LiveContextResolver handle caching
import contextvars
_disable_lazy_cache: contextvars.ContextVar[bool] = contextvars.ContextVar('_disable_lazy_cache', default=False)


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


@dataclass(frozen=True)
class LazyMethodBindings:
    """Declarative method bindings for lazy dataclasses."""

    @staticmethod
    def create_resolver() -> Callable[[Any, str], Any]:
        """Create field resolver method using new pure function interface."""
        from openhcs.config_framework.dual_axis_resolver import resolve_field_inheritance
        from openhcs.config_framework.context_manager import current_temp_global, current_extracted_configs, current_scope_id, current_config_scopes

        def _resolve_field_value(self, field_name: str) -> Any:
            # Get current context from contextvars
            try:
                current_context = current_temp_global.get()
                # Get cached extracted configs (already extracted when context was set)
                available_configs = current_extracted_configs.get()
                # Get scope information
                scope_id = current_scope_id.get()
                config_scopes = current_config_scopes.get()

                # Use pure function for resolution with scope information
                return resolve_field_inheritance(self, field_name, available_configs, scope_id, config_scopes)
            except LookupError:
                # No context available - return None (fail-loud approach)
                if field_name == 'well_filter_mode':
                    logger.info(f"❌ No context available for resolving {type(self).__name__}.{field_name}")
                logger.debug(f"No context available for resolving {type(self).__name__}.{field_name}")
                return None

        return _resolve_field_value

    @staticmethod
    def create_getattribute() -> Callable[[Any, str], Any]:
        """Create lazy __getattribute__ method using new context system."""
        from openhcs.config_framework.dual_axis_resolver import resolve_field_inheritance, _has_concrete_field_override
        from openhcs.config_framework.context_manager import current_temp_global, current_extracted_configs

        def _find_mro_concrete_value(base_class, name):
            """Extract common MRO traversal pattern."""
            return next((getattr(cls, name) for cls in base_class.__mro__
                        if _has_concrete_field_override(cls, name)), None)

        def _try_global_context_value(self, base_class, name):
            """Extract global context resolution logic using new pure function interface."""
            if not hasattr(self, '_global_config_type'):
                return None

            # Get current context from contextvars
            try:
                from openhcs.config_framework.context_manager import current_scope_id, current_config_scopes
                current_context = current_temp_global.get()
                # Get cached extracted configs (already extracted when context was set)
                available_configs = current_extracted_configs.get()
                # Get scope information
                scope_id = current_scope_id.get()
                config_scopes = current_config_scopes.get()

                # Use pure function for resolution with scope information
                resolved_value = resolve_field_inheritance(self, name, available_configs, scope_id, config_scopes)
                if resolved_value is not None:
                    return resolved_value
            except LookupError:
                # No context available - fall back to MRO
                pass

            # Fallback to MRO concrete value
            return _find_mro_concrete_value(base_class, name)

        def __getattribute__(self: Any, name: str) -> Any:
            """
            Three-stage resolution with class-level caching.

            PERFORMANCE: Cache resolved values in shared class-level dict to survive instance recreation.
            Pipeline editor creates new step instances on every keystroke (token change), so instance-level
            cache wouldn't work. Class-level cache survives across instance recreation.

            Cache Strategy:
            - Use global _lazy_resolution_cache dict shared across all instances
            - Cache key: (class_name, field_name, context_token)
            - Invalidate when context token changes (automatic via key mismatch)
            - Skip cache for private attributes and special methods

            Stage 0: Check class-level cache (PERFORMANCE OPTIMIZATION)
            Stage 1: Check instance value
            Stage 2: Simple field path lookup in current scope's merged config
            Stage 3: Inheritance resolution using same merged context
            """
            # Stage 0: Check class-level cache first (PERFORMANCE OPTIMIZATION)
            # Skip cache for special attributes, private attributes, and non-field attributes
            # PERFORMANCE: Cache field names to avoid repeated fields() introspection
            if not name.startswith('_'):
                cls = self.__class__
                if cls not in _class_field_names_cache:
                    _class_field_names_cache[cls] = frozenset(f.name for f in fields(cls))
                is_dataclass_field = name in _class_field_names_cache[cls]
            else:
                is_dataclass_field = False

            # CRITICAL: Check RAW instance value FIRST before cache
            # The cache stores RESOLVED values (from global config), but if the instance
            # has an explicit value set, we must return that instead of the cached global value
            value = object.__getattribute__(self, name)

            if value is not None or not is_dataclass_field:
                return value

            # CRITICAL: Skip cache if disabled (e.g., during LiveContextResolver flash detection)
            # Flash detection needs to resolve with historical tokens, not current token
            # Also skip if framework config disables this cache (for debugging)
            cache_disabled = _disable_lazy_cache.get(False)

            if not cache_disabled:
                try:
                    from openhcs.config_framework.config import get_framework_config
                    cache_disabled = get_framework_config().is_cache_disabled('lazy_resolution')
                except ImportError:
                    pass

            if is_dataclass_field and not cache_disabled:
                try:
                    # Get current token from ParameterFormManager
                    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
                    current_token = ParameterFormManager._live_context_token_counter

                    # Check class-level cache
                    cache_key = (self.__class__.__name__, name, current_token)
                    if cache_key in _lazy_resolution_cache:
                        # PERFORMANCE: Don't log cache hits - creates massive I/O bottleneck
                        # (414 log writes per keystroke was slower than the resolution itself!)
                        if name == 'well_filter_mode' or name == 'num_workers':
                            logger.info(f"🔍 CACHE HIT: {self.__class__.__name__}.{name} = {_lazy_resolution_cache[cache_key]} (token={current_token})")
                        return _lazy_resolution_cache[cache_key]
                    else:
                        if name == 'num_workers':
                            logger.info(f"🔍 CACHE MISS: {self.__class__.__name__}.{name} (token={current_token})")
                except ImportError:
                    # No ParameterFormManager available - skip caching
                    pass

            # Helper function to cache resolved value
            def cache_value(value):
                """Cache resolved value with current token in class-level cache."""
                # Skip caching if disabled (e.g., during LiveContextResolver flash detection)
                if is_dataclass_field and not cache_disabled:
                    try:
                        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
                        current_token = ParameterFormManager._live_context_token_counter

                        cache_key = (self.__class__.__name__, name, current_token)
                        _lazy_resolution_cache[cache_key] = value

                        if name == 'num_workers':
                            logger.info(f"🔍 CACHED: {self.__class__.__name__}.{name} = {value} (token={current_token})")

                        # Prevent unbounded growth by evicting oldest entries
                        if len(_lazy_resolution_cache) > _LAZY_CACHE_MAX_SIZE:
                            # Evict first 20% of entries (FIFO approximation using dict ordering)
                            num_to_evict = _LAZY_CACHE_MAX_SIZE // 5
                            keys_to_remove = list(_lazy_resolution_cache.keys())[:num_to_evict]
                            for key in keys_to_remove:
                                del _lazy_resolution_cache[key]
                            logger.info(f"🗑️ Evicted {num_to_evict} cache entries (max size={_LAZY_CACHE_MAX_SIZE})")

                        # PERFORMANCE: Don't log cache stores - creates I/O bottleneck
                    except ImportError:
                        # No ParameterFormManager available - skip caching
                        pass

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
                                    cache_value(resolved_value)
                                    return resolved_value
                        except AttributeError:
                            # Field doesn't exist in merged config, continue to inheritance
                            pass
            except LookupError:
                # No context available, continue to inheritance
                pass

            # Stage 3: Inheritance resolution using same merged context
            try:
                from openhcs.config_framework.context_manager import current_scope_id, current_config_scopes
                current_context = current_temp_global.get()
                # Get cached extracted configs (already extracted when context was set)
                available_configs = current_extracted_configs.get()
                # Get scope information
                scope_id = current_scope_id.get()
                config_scopes = current_config_scopes.get()

                if name == 'well_filter_mode':
                    logger.info(f"🔍 LAZY __getattribute__: {self.__class__.__name__}.{name} - calling resolve_field_inheritance")
                    logger.info(f"🔍 LAZY __getattribute__: available_configs = {list(available_configs.keys())}")

                resolved_value = resolve_field_inheritance(self, name, available_configs, scope_id, config_scopes)

                if name == 'well_filter_mode' or name == 'num_workers':
                    logger.info(f"🔍 LAZY __getattribute__: resolve_field_inheritance returned {resolved_value} for {self.__class__.__name__}.{name}")

                if resolved_value is not None:
                    if name == 'num_workers':
                        logger.info(f"🔍 LAZY __getattribute__: About to cache {resolved_value} for {self.__class__.__name__}.{name}")
                    cache_value(resolved_value)
                    return resolved_value

                # For nested dataclass fields, return lazy instance
                field_obj = next((f for f in fields(self.__class__) if f.name == name), None)
                if field_obj and is_dataclass(field_obj.type):
                    lazy_instance = field_obj.type()
                    cache_value(lazy_instance)
                    return lazy_instance

                return None

            except LookupError:
                # No context available - fallback to MRO concrete values
                # CRITICAL: DO NOT CACHE MRO fallback values!
                # MRO fallback is a "last resort" when no context is available.
                # If we cache it, it pollutes the cache and prevents proper context-based
                # resolution later (when context becomes available at the same token).
                if name == 'num_workers':
                    logger.info(f"🔍 LAZY __getattribute__: LookupError - falling back to MRO for {self.__class__.__name__}.{name}")
                fallback_value = _find_mro_concrete_value(get_base_type_for_lazy(self.__class__), name)
                if name == 'num_workers':
                    logger.info(f"🔍 LAZY __getattribute__: MRO fallback returned {fallback_value} for {self.__class__.__name__}.{name} (NOT CACHED)")
                # DO NOT call cache_value() here - MRO fallback should never be cached
                return fallback_value
        return __getattribute__

    @staticmethod
    def create_deepcopy() -> Callable:
        """Create __deepcopy__ method that preserves tracking attributes."""
        def __deepcopy__(self, memo):
            import copy
            logger.info(f"🔍 DEEPCOPY: {self.__class__.__name__}.__deepcopy__ called")
            # Create new instance with same field values
            field_values = {}
            for f in fields(self):
                value = object.__getattribute__(self, f.name)
                # Deepcopy the field value
                field_values[f.name] = copy.deepcopy(value, memo)

            # Create new instance
            new_instance = self.__class__(**field_values)

            # CRITICAL: Copy tracking attributes to new instance
            # These are set by the tracking wrapper in __init__ and must be preserved across deepcopy
            for attr in ['_explicitly_set_fields', '_global_config_type', '_config_field_name']:
                try:
                    value = object.__getattribute__(self, attr)
                    object.__setattr__(new_instance, attr, value)
                    logger.info(f"🔍 DEEPCOPY: Copied {attr}={value} to new instance")
                except AttributeError:
                    pass

            return new_instance
        return __deepcopy__

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

            # CRITICAL FIX: Create default factory for Optional dataclass fields
            # This eliminates the need for field introspection and ensures UI always has instances to render
            # CRITICAL: Always preserve metadata from original field (e.g., ui_hidden flag)
            if (is_already_optional or not has_default) and is_dataclass(field.type):
                # For Optional dataclass fields, create default factory that creates lazy instances
                # This ensures the UI always has nested lazy instances to render recursively
                # CRITICAL: field_type is already the lazy type, so use it directly
                field_def = (field.name, final_field_type, dataclasses.field(default_factory=field_type, metadata=field.metadata))
            elif field.metadata:
                # For fields with metadata but no dataclass default factory, create a Field object to preserve metadata
                # We need to replicate the original field's default behavior
                if field.default is not MISSING:
                    field_def = (field.name, final_field_type, dataclasses.field(default=field.default, metadata=field.metadata))
                elif field.default_factory is not MISSING:
                    if is_dataclass(field.type):
                        # Instantiate lazy dataclass instances instead of leaving field as None
                        # so that consumers can inspect inherited values without materializing overrides.
                        field_def = (field.name, final_field_type, dataclasses.field(default_factory=field_type, metadata=field.metadata))
                    else:
                        field_def = (field.name, final_field_type, dataclasses.field(default_factory=field.default_factory, metadata=field.metadata))
                else:
                    # Field has metadata but no default - use MISSING to indicate required field
                    field_def = (field.name, final_field_type, dataclasses.field(default=MISSING, metadata=field.metadata))
            else:
                # No metadata, no special handling needed
                field_def = (field.name, final_field_type, None)

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
            base_metaclass != InheritAsNoneMeta and
            not has_inherit_as_none_marker
        )

        # CRITICAL: Preserve inheritance hierarchy in lazy versions
        # If base_class inherits from other dataclasses, make the lazy version inherit from their lazy versions
        # This must happen BEFORE the has_unsafe_metaclass check so lazy_bases is populated
        lazy_bases = []
        for base in base_class.__bases__:
            if base is object:
                continue
            if is_dataclass(base):
                # Create or get lazy version of parent class
                lazy_parent_name = f"Lazy{base.__name__}"
                lazy_parent = LazyDataclassFactory.make_lazy_simple(
                    base_class=base,
                    lazy_class_name=lazy_parent_name
                )
                lazy_bases.append(lazy_parent)
                logger.debug(f"Lazy {lazy_class_name} inherits from lazy {lazy_parent_name}")

        if has_unsafe_metaclass:
            # Base class has unsafe custom metaclass - inherit using the same metaclass
            logger.debug(f"Lazy {lazy_class_name}: {base_class.__name__} has custom metaclass {base_metaclass.__name__}, using same metaclass")

            # CRITICAL: Inherit from base_class directly (e.g., PipelineConfig inherits from GlobalPipelineConfig)
            # Use the same metaclass to avoid conflicts
            from abc import ABCMeta
            from dataclasses import dataclass as dataclass_decorator, field as dataclass_field

            # Build class namespace with field annotations AND defaults
            namespace = {'__module__': base_class.__module__}
            annotations = {}

            # Add field annotations and defaults from introspected fields
            for field_info in LazyDataclassFactory._introspect_dataclass_fields(
                base_class, debug_template, global_config_type, parent_field_path, parent_instance_provider
            ):
                if isinstance(field_info, tuple):
                    if len(field_info) == 3:
                        field_name, field_type, field_default = field_info
                    else:
                        field_name, field_type = field_info
                        field_default = None
                else:
                    field_name = field_info.name
                    field_type = field_info.type
                    field_default = None

                annotations[field_name] = field_type
                # Set field default to None (or the provided default)
                if field_default is None:
                    namespace[field_name] = None
                else:
                    namespace[field_name] = field_default

            namespace['__annotations__'] = annotations

            # Create class with same metaclass, inheriting from base_class
            lazy_class = base_metaclass(
                lazy_class_name,
                (base_class,),  # Inherit from base_class directly
                namespace
            )
            # Apply dataclass decorator
            lazy_class = dataclass_decorator(frozen=True)(lazy_class)

            # CRITICAL: Copy methods from base class when avoiding inheritance
            # This includes abstract methods that need to be implemented
            for attr_name in dir(base_class):
                if not attr_name.startswith('_'):  # Skip private/magic methods
                    attr_value = getattr(base_class, attr_name, None)
                    # Only copy methods, not fields
                    if attr_value is not None and callable(attr_value) and not isinstance(attr_value, type):
                        # Don't copy if it's a dataclass field descriptor
                        if not hasattr(lazy_class, attr_name) or not hasattr(getattr(lazy_class, attr_name), '__set__'):
                            # CRITICAL: If this is an abstract method, we need to unwrap it
                            # Otherwise the new class will still be considered abstract
                            if hasattr(attr_value, '__isabstractmethod__') and attr_value.__isabstractmethod__:
                                # Get the underlying function without the abstractmethod wrapper
                                if hasattr(attr_value, '__func__'):
                                    actual_func = attr_value.__func__
                                else:
                                    actual_func = attr_value
                                # Create a new function without the abstractmethod marker
                                import types
                                new_func = types.FunctionType(
                                    actual_func.__code__,
                                    actual_func.__globals__,
                                    actual_func.__name__,
                                    actual_func.__defaults__,
                                    actual_func.__closure__
                                )
                                setattr(lazy_class, attr_name, new_func)
                            else:
                                setattr(lazy_class, attr_name, attr_value)

            # CRITICAL: Update __abstractmethods__ to reflect that we've implemented the abstract methods
            # Python's ABC system caches abstract status at class creation time, so we need to manually update it
            if hasattr(lazy_class, '__abstractmethods__'):
                # Remove any methods we just copied from the abstract methods set
                implemented_methods = {attr_name for attr_name in dir(base_class)
                                     if not attr_name.startswith('_') and callable(getattr(base_class, attr_name, None))}
                new_abstract_methods = lazy_class.__abstractmethods__ - implemented_methods
                lazy_class.__abstractmethods__ = frozenset(new_abstract_methods)
        else:
            # Safe to inherit - use lazy parent classes if available, otherwise inherit from base_class
            bases_to_use = tuple(lazy_bases) if lazy_bases else (base_class,)
            lazy_class = make_dataclass(
                lazy_class_name,
                LazyDataclassFactory._introspect_dataclass_fields(
                    base_class, debug_template, global_config_type, parent_field_path, parent_instance_provider
                ),
                bases=bases_to_use,
                frozen=True
            )

        # CRITICAL: Copy methods from base class to lazy class
        # make_dataclass() only copies bases, not methods defined in the class body
        # This preserves methods like build_scope_id() from ScopedObject implementations
        for attr_name in dir(base_class):
            if not attr_name.startswith('_'):  # Skip private/magic methods
                attr_value = getattr(base_class, attr_name, None)
                # Only copy methods, not fields (fields are already handled by make_dataclass)
                if attr_value is not None and callable(attr_value) and not isinstance(attr_value, type):
                    # Don't copy if it's a dataclass field descriptor
                    if not hasattr(lazy_class, attr_name) or not hasattr(getattr(lazy_class, attr_name), '__set__'):
                        setattr(lazy_class, attr_name, attr_value)

        # Add constructor parameter tracking to detect user-set fields
        # CRITICAL: Check if base_class already has a custom __init__ from @global_pipeline_config
        # If so, we need to preserve it and wrap it instead of replacing it
        base_has_custom_init = (
            hasattr(base_class, '__init__') and
            hasattr(base_class.__init__, '_is_custom_inherit_as_none_init') and
            base_class.__init__._is_custom_inherit_as_none_init
        )

        if base_has_custom_init:
            # Base class has custom __init__ from decorator - we need to apply the same logic to lazy class
            fields_set_to_none = base_class.__init__._fields_set_to_none
            logger.info(f"🔍 LAZY FACTORY: {lazy_class_name} - applying custom __init__ from base class {base_class.__name__} with fields_set_to_none={fields_set_to_none}")

            # Get the original dataclass-generated __init__ for lazy_class
            dataclass_init = lazy_class.__init__

            # CRITICAL FIX: Dynamically generate __init__ with explicit parameters
            # This is necessary because Python can't match LazyNapariStreamingConfig(enabled=True, port=5555)
            # to a signature of (self, **kwargs) - it needs explicit parameter names

            # Get all field names from the dataclass
            field_names = [f.name for f in dataclasses.fields(lazy_class)]

            # Build the parameter list string for exec()
            # Format: "self, *, field1=None, field2=None, ..."
            params_str = "self, *, " + ", ".join(f"{name}=None" for name in field_names)

            # Build the function body that collects all kwargs
            # We need to capture all the parameters into a kwargs dict
            kwargs_items = ", ".join(f"'{name}': {name}" for name in field_names)

            # Build the logging string for parameters at generation time
            params_log_str = ', '.join(f'{name}={{{name}}}' for name in field_names)

            # Create the function code
            func_code = f"""
def custom_init_with_tracking({params_str}):
    logger.info(f"🔍🔍🔍 {lazy_class_name}.__init__ CALLED with params: {params_log_str}")
    kwargs = {{{kwargs_items}}}
    logger.info(f"🔍 {lazy_class_name}.__init__: kwargs={{kwargs}}, fields_set_to_none={{fields_set_to_none}}")

    # First apply the inherit-as-none logic (set missing fields to None)
    for field_name in fields_set_to_none:
        if field_name not in kwargs:
            logger.info(f"🔍 {lazy_class_name}.__init__: Setting {{field_name}} = None (not in kwargs)")
            kwargs[field_name] = None
        else:
            logger.info(f"🔍 {lazy_class_name}.__init__: Keeping {{field_name}} = {{kwargs[field_name]}} (in kwargs)")

    # Then add tracking
    object.__setattr__(self, '_explicitly_set_fields', set(kwargs.keys()))
    object.__setattr__(self, '_global_config_type', global_config_type)
    import re
    def _camel_to_snake_local(name: str) -> str:
        s1 = re.sub('(.)([A-Z][a-z]+)', r'\\1_\\2', name)
        return re.sub('([a-z0-9])([A-Z])', r'\\1_\\2', s1).lower()
    config_field_name = _camel_to_snake_local(base_class.__name__)
    object.__setattr__(self, '_config_field_name', config_field_name)

    logger.info(f"🔍 {lazy_class_name}.__init__: Calling original_init with kwargs={{kwargs}}")
    # Call the dataclass-generated __init__
    dataclass_init(self, **kwargs)
"""

            # Execute the function code to create the function
            namespace = {
                'logger': logger,
                'fields_set_to_none': fields_set_to_none,
                'global_config_type': global_config_type,
                'base_class': base_class,
                'dataclass_init': dataclass_init,
                'object': object
            }
            exec(func_code, namespace)
            custom_init_with_tracking = namespace['custom_init_with_tracking']

            lazy_class.__init__ = custom_init_with_tracking
        else:
            # Normal case - no custom __init__ from decorator
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
            '__deepcopy__': LazyMethodBindings.create_deepcopy(),
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

        # CRITICAL: Check cache by class name BEFORE creating instance_provider
        # This ensures we return the same lazy class instance when called recursively
        simple_cache_key = f"{base_class.__module__}.{base_class.__name__}_{lazy_class_name}"
        if simple_cache_key in _lazy_class_cache:
            return _lazy_class_cache[simple_cache_key]

        # Simple provider that uses new contextvars system
        def simple_provider():
            """Simple provider using new contextvars system."""
            return base_class()  # Lazy __getattribute__ handles resolution

        lazy_class = LazyDataclassFactory._create_lazy_dataclass_unified(
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

        # Cache with simple key for future lookups
        _lazy_class_cache[simple_cache_key] = lazy_class

        return lazy_class

    # All legacy methods removed - use make_lazy_simple() for all use cases


# Generic utility functions for clean thread-local storage management
def ensure_global_config_context(global_config_type: Type, global_config_instance: Any) -> None:
    """Ensure proper thread-local storage setup for any global config type."""
    from openhcs.config_framework.global_config import set_global_config_for_editing
    set_global_config_for_editing(global_config_type, global_config_instance)


# Context provider registry and metaclass for automatic registration
CONTEXT_PROVIDERS = {}


# Configuration for context provider registration
_CONTEXT_PROVIDER_REGISTRY_CONFIG = RegistryConfig(
    registry_dict=CONTEXT_PROVIDERS,
    key_attribute='_context_type',
    key_extractor=None,  # Requires explicit _context_type
    skip_if_no_key=True,  # Skip if no _context_type set
    secondary_registries=None,
    log_registration=True,
    registry_name='context provider'
)


class ContextProviderMeta(AutoRegisterMeta):
    """Metaclass for automatic registration of context provider classes."""

    def __new__(mcs, name, bases, attrs):
        return super().__new__(mcs, name, bases, attrs,
                              registry_config=_CONTEXT_PROVIDER_REGISTRY_CONFIG)


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


# ContextInjector removed - replaced with contextvars-based context system




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

    # CRITICAL FIX: Handle step objects (non-dataclass objects with dataclass attributes)
    step_context_type = _detect_context_type(resolved_data)
    if step_context_type:
        # This is a context object - inject it for its dataclass attributes
        import inspect
        frame = inspect.currentframe()
        context_var_name = f"__{step_context_type}_context__"
        frame.f_locals[context_var_name] = resolved_data
        logger.debug(f"Injected {context_var_name} = {type(resolved_data).__name__}")

        try:
            # Process step attributes recursively
            resolved_attrs = {}
            for attr_name in dir(resolved_data):
                if attr_name.startswith('_'):
                    continue
                try:
                    attr_value = getattr(resolved_data, attr_name)
                    if not callable(attr_value):  # Skip methods
                        logger.debug(f"Resolving {type(resolved_data).__name__}.{attr_name} = {type(attr_value).__name__}")
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
        logger.debug(f"Injected {context_var_name} = {type(resolved_data).__name__}")

        # Add debug to see which fields are being resolved
        logger.debug(f"Resolving fields for {type(resolved_data).__name__}: {[f.name for f in fields(resolved_data)]}")

        try:
            resolved_fields = {}
            for f in fields(resolved_data):
                field_value = getattr(resolved_data, f.name)
                logger.debug(f"Resolving {type(resolved_data).__name__}.{f.name} = {type(field_value).__name__}")
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
                # Check if this is a concrete dataclass that should be converted to lazy
                is_lazy = LazyDefaultPlaceholderService.has_lazy_resolution(type(raw_value))

                if not is_lazy:
                    lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(type(raw_value))

                    if lazy_type:
                        # Convert concrete dataclass to lazy version while preserving ONLY non-default field values
                        # This allows fields that match class defaults to inherit from context
                        concrete_field_values = {}
                        for f in fields(raw_value):
                            field_value = object.__getattribute__(raw_value, f.name)

                            # Get the class default for this field
                            class_default = getattr(type(raw_value), f.name, None)

                            # Only preserve values that differ from class defaults
                            # This allows default values to be inherited from context
                            if field_value != class_default:
                                concrete_field_values[f.name] = field_value

                        logger.debug(f"Converting concrete {type(raw_value).__name__} to lazy version {lazy_type.__name__} for placeholder resolution")
                        return lazy_type(**concrete_field_values)

                # If already lazy or no lazy version available, rebuild recursively
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
            # Configure logging inline for decorator execution (runs at import time before logging is configured)
            import logging
            import sys
            _decorator_logger = logging.getLogger('openhcs.config_framework.lazy_factory')
            # DISABLED: StreamHandler causes print output even when logging is disabled
            # This logger will use the root logger's handlers configured in launch.py
            pass

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

            # CRITICAL: Post-process dataclass fields after @dataclass has run
            # This fixes the constructor behavior for inherited fields that should be None
            # Apply to BOTH base class AND lazy class
            # _decorator_logger.info(f"🔍 @global_pipeline_config: {actual_cls.__name__} - inherit_as_none={inherit_as_none}, fields_set_to_none={fields_set_to_none}")
            if inherit_as_none and hasattr(actual_cls, '__dataclass_fields__'):
                # _decorator_logger.info(f"🔍 BASE CLASS FIX: {actual_cls.__name__} - fixing {len(fields_set_to_none)} inherited fields")
                _fix_dataclass_field_defaults_post_processing(actual_cls, fields_set_to_none, _decorator_logger)

            # CRITICAL: Also fix lazy class to ensure ALL fields are None by default
            # For lazy classes, ALL fields should be None (not just inherited ones)
            # _decorator_logger.info(f"🔍 LAZY CLASS CHECK: {lazy_class.__name__} - inherit_as_none={inherit_as_none}, has_dataclass_fields={hasattr(lazy_class, '__dataclass_fields__')}")
            if inherit_as_none:
                if hasattr(lazy_class, '__dataclass_fields__'):
                    # Compute ALL fields for lazy class (not just inherited ones)
                    lazy_fields_to_set_none = set(lazy_class.__dataclass_fields__.keys())
                    # _decorator_logger.info(f"🔍 LAZY CLASS FIX: {lazy_class.__name__} - setting {len(lazy_fields_to_set_none)} fields to None: {lazy_fields_to_set_none}")
                    _fix_dataclass_field_defaults_post_processing(lazy_class, lazy_fields_to_set_none, _decorator_logger)
                else:
                    # _decorator_logger.warning(f"🔍 WARNING: {lazy_class.__name__} does not have __dataclass_fields__!")
                    pass

            return actual_cls

        # Handle both @decorator and @decorator() usage
        if cls is None:
            # Called with parentheses: @decorator(optional=True)
            return decorator
        else:
            # Called without parentheses: @decorator
            return decorator(cls)

    return global_default_decorator


def _fix_dataclass_field_defaults_post_processing(cls: Type, fields_set_to_none: set, inline_logger=None) -> None:
    """
    Fix dataclass field defaults after @dataclass has processed the class.

    This is necessary because @dataclass processes the MRO and may use parent class
    field definitions instead of our modified class attributes. We need to ensure
    that fields we set to None actually use None as the default in the constructor.
    """
    import dataclasses

    _log = inline_logger if inline_logger else logger
    _log.info(f"🔍 _fix_dataclass_field_defaults_post_processing: {cls.__name__} - fixing {len(fields_set_to_none)} fields: {fields_set_to_none}")

    # CRITICAL: Check if this is a lazy class that already has tracking wrapper
    # If so, DON'T replace it - the tracking wrapper already handles inherit-as-none logic
    if hasattr(cls.__init__, '__name__') and 'tracking' in cls.__init__.__name__:
        _log.info(f"🔍 _fix_dataclass_field_defaults_post_processing: {cls.__name__} already has tracking wrapper, skipping")
        # Still update field defaults for consistency
        for field_name in fields_set_to_none:
            if field_name in cls.__dataclass_fields__:
                field_obj = cls.__dataclass_fields__[field_name]
                field_obj.default = None
                field_obj.default_factory = dataclasses.MISSING
                setattr(cls, field_name, None)
        return

    # Store the original __init__ method
    original_init = cls.__init__

    # CRITICAL FIX: Dynamically generate __init__ with explicit parameters
    # This is necessary because Python can't match LazyNapariStreamingConfig(enabled=True, port=5555)
    # to a signature of (self, **kwargs) - it needs explicit parameter names

    # Get all field names from the dataclass
    field_names = [f.name for f in dataclasses.fields(cls)]

    # Build the parameter list string for exec()
    # Format: "self, *, field1=None, field2=None, ..."
    params_str = "self, *, " + ", ".join(f"{name}=None" for name in field_names)

    # Build the function body that collects all kwargs
    # We need to capture all the parameters into a kwargs dict
    kwargs_items = ", ".join(f"'{name}': {name}" for name in field_names)

    # Build the logging string for parameters at generation time
    params_log_str = ', '.join(f'{name}={{{name}}}' for name in field_names)

    # Create the function code
    func_code = f"""
def custom_init({params_str}):
    \"\"\"Custom __init__ that ensures inherited fields use None defaults.\"\"\"
    _log.info(f"🔍 {cls.__name__}.__init__ CALLED with params: {params_log_str}")
    kwargs = {{{kwargs_items}}}
    _log.info(f"🔍 {cls.__name__}.__init__: kwargs={{kwargs}}, fields_set_to_none={{fields_set_to_none}}")
    # For fields that should be None, set them to None if not explicitly provided
    for field_name in fields_set_to_none:
        if field_name not in kwargs:
            kwargs[field_name] = None
            _log.info(f"🔍 {cls.__name__}.__init__: Setting {{field_name}} = None (not in kwargs)")

    # Call the original __init__ with modified kwargs
    _log.info(f"🔍 {cls.__name__}.__init__: Calling original_init with kwargs={{kwargs}}")
    original_init(self, **kwargs)
"""

    # Execute the function code to create the function
    namespace = {
        '_log': _log,
        'fields_set_to_none': fields_set_to_none,
        'original_init': original_init
    }
    exec(func_code, namespace)
    custom_init = namespace['custom_init']

    # Replace the __init__ method and mark it as custom
    cls.__init__ = custom_init
    cls.__init__._is_custom_inherit_as_none_init = True
    cls.__init__._fields_set_to_none = fields_set_to_none  # Store for later use

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

    # CRITICAL: Copy methods from original class to new class
    # make_dataclass() only copies bases, not methods defined in the class body
    # This preserves methods like build_scope_id() from ScopedObject implementations
    for attr_name in dir(target_class):
        if not attr_name.startswith('_'):  # Skip private/magic methods
            attr_value = getattr(target_class, attr_name)
            # Only copy methods, not fields (fields are already in all_fields)
            if callable(attr_value) and not isinstance(attr_value, type):
                # CRITICAL: If this is an abstract method, we need to unwrap it
                # Otherwise the new class will still be considered abstract
                if hasattr(attr_value, '__isabstractmethod__') and attr_value.__isabstractmethod__:
                    # Get the underlying function without the abstractmethod wrapper
                    # The actual function is stored in __func__ for bound methods
                    if hasattr(attr_value, '__func__'):
                        actual_func = attr_value.__func__
                    else:
                        actual_func = attr_value
                    # Create a new function without the abstractmethod marker
                    import types
                    new_func = types.FunctionType(
                        actual_func.__code__,
                        actual_func.__globals__,
                        actual_func.__name__,
                        actual_func.__defaults__,
                        actual_func.__closure__
                    )
                    setattr(new_class, attr_name, new_func)
                else:
                    setattr(new_class, attr_name, attr_value)

    # CRITICAL: Update __abstractmethods__ to reflect that we've implemented the abstract methods
    # Python's ABC system caches abstract status at class creation time, so we need to manually update it
    if hasattr(new_class, '__abstractmethods__'):
        # Remove any methods we just copied from the abstract methods set
        implemented_methods = {attr_name for attr_name in dir(target_class)
                             if not attr_name.startswith('_') and callable(getattr(target_class, attr_name, None))}
        new_abstract_methods = new_class.__abstractmethods__ - implemented_methods
        new_class.__abstractmethods__ = frozenset(new_abstract_methods)

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

    decorator_name = _camel_to_snake(global_config_class.__name__)
    decorator = create_global_default_decorator(global_config_class)

    # Export decorator to module globals
    module = sys.modules[global_config_class.__module__]
    setattr(module, decorator_name, decorator)

    # Lazy global config will be created after field injection

    return global_config_class






