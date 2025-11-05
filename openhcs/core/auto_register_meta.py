"""
Generic metaclass infrastructure for automatic plugin registration.

This module provides reusable metaclass infrastructure for Pattern A registry systems
(1:1 class-to-plugin mapping with automatic discovery). It eliminates code duplication
across MicroscopeHandlerMeta, StorageBackendMeta, and ContextProviderMeta.

Pattern Selection Guide:
-----------------------
Use AutoRegisterMeta (Pattern A) when:
- You have a 1:1 mapping between classes and plugins
- Plugins should be automatically discovered and registered
- Registration happens at class definition time
- Simple metadata (just a key and maybe one secondary registry)

Use Service Pattern (Pattern B) when:
- You have many-to-one mapping (multiple items per plugin)
- Complex metadata (FunctionMetadata with 8+ fields)
- Need aggregation across multiple sources
- Examples: Function registry, Format registry

Use Functional Registry (Pattern C) when:
- Simple type-to-handler mappings
- No state needed
- Functional programming style preferred
- Examples: Widget creation registries

Use Manual Registration (Pattern D) when:
- Complex initialization logic required
- Explicit control over registration timing needed
- Very few plugins (< 3)
- Examples: ZMQ servers, Pipeline steps

Architecture:
------------
AutoRegisterMeta uses a configuration-driven approach:
1. RegistryConfig defines registration behavior
2. AutoRegisterMeta applies the configuration during class creation
3. Domain-specific metaclasses provide thin wrappers with their config

This maintains domain-specific features while eliminating duplication.
"""

import importlib
import logging
import threading
from abc import ABCMeta
from dataclasses import dataclass
from typing import Dict, Type, Optional, Callable, Any

logger = logging.getLogger(__name__)

# Lazy import to avoid circular dependency
_registry_cache_manager = None

def _get_cache_manager():
    """Lazy import of RegistryCacheManager to avoid circular imports."""
    global _registry_cache_manager
    if _registry_cache_manager is None:
        from openhcs.core.registry_cache import (
            RegistryCacheManager,
            CacheConfig,
            serialize_plugin_class,
            deserialize_plugin_class,
            get_package_file_mtimes
        )
        _registry_cache_manager = {
            'RegistryCacheManager': RegistryCacheManager,
            'CacheConfig': CacheConfig,
            'serialize_plugin_class': serialize_plugin_class,
            'deserialize_plugin_class': deserialize_plugin_class,
            'get_package_file_mtimes': get_package_file_mtimes
        }
    return _registry_cache_manager


# Type aliases for clarity
RegistryDict = Dict[str, Type]
KeyExtractor = Callable[[str, Type], str]

# Constants for key sources
PRIMARY_KEY = 'primary'


class SecondaryRegistryDict(dict):
    """
    Dict for secondary registries that auto-triggers primary registry discovery.

    When accessed, this dict triggers discovery of the primary registry,
    which populates both the primary and secondary registries.
    """

    def __init__(self, primary_registry: 'LazyDiscoveryDict'):
        super().__init__()
        self._primary_registry = primary_registry

    def _ensure_discovered(self):
        """Trigger discovery of primary registry (which populates this secondary registry)."""
        if hasattr(self._primary_registry, '_discover'):
            self._primary_registry._discover()

    def __getitem__(self, key):
        self._ensure_discovered()
        return super().__getitem__(key)

    def __contains__(self, key):
        self._ensure_discovered()
        return super().__contains__(key)

    def __iter__(self):
        self._ensure_discovered()
        return super().__iter__()

    def __len__(self):
        self._ensure_discovered()
        return super().__len__()

    def keys(self):
        self._ensure_discovered()
        return super().keys()

    def values(self):
        self._ensure_discovered()
        return super().values()

    def items(self):
        self._ensure_discovered()
        return super().items()

    def get(self, key, default=None):
        self._ensure_discovered()
        return super().get(key, default)


class LazyDiscoveryDict(dict):
    """
    Dict that auto-discovers plugins on first access with optional caching.

    Supports caching discovered plugins to speed up subsequent application starts.
    Cache is validated against package version and file modification times.

    Thread-safe: Uses double-checked locking to ensure discovery happens only once
    even when accessed from multiple threads simultaneously.
    """

    def __init__(self, enable_cache: bool = True):
        """
        Initialize lazy discovery dict.

        Args:
            enable_cache: If True, use caching to speed up discovery
        """
        super().__init__()
        self._base_class = None
        self._config = None
        self._discovered = False
        self._enable_cache = enable_cache
        self._cache_manager = None
        self._discovery_lock = threading.RLock()  # Reentrant lock for same-thread re-entry

    def _set_config(self, base_class: Type, config: 'RegistryConfig') -> None:
        self._base_class = base_class
        self._config = config

        # Initialize cache manager if caching is enabled
        if self._enable_cache and config.discovery_package:
            try:
                cache_utils = _get_cache_manager()

                # Get version getter (use openhcs version)
                def get_version():
                    try:
                        import openhcs
                        return openhcs.__version__
                    except:
                        return "unknown"

                self._cache_manager = cache_utils['RegistryCacheManager'](
                    cache_name=f"{config.registry_name.replace(' ', '_')}_registry",
                    version_getter=get_version,
                    serializer=cache_utils['serialize_plugin_class'],
                    deserializer=cache_utils['deserialize_plugin_class'],
                    config=cache_utils['CacheConfig'](
                        max_age_days=7,
                        check_mtimes=True  # Validate file modifications
                    )
                )
            except Exception as e:
                logger.debug(f"Failed to initialize cache manager: {e}")
                self._cache_manager = None

    def _discover(self) -> None:
        """
        Run discovery once, using cache if available.

        Thread-safe: Discovery happens inside the lock to ensure atomicity.
        The lock is held for the entire duration to prevent other threads
        from reading a partially-populated registry.

        CRITICAL: No fast path check outside the lock! All threads must acquire
        the lock to ensure they don't read a partially-populated registry.
        """
        # No config = nothing to discover
        if not self._config or not self._config.discovery_package:
            return

        # ALWAYS acquire lock - no fast path to avoid race condition
        # RLock allows same thread to re-acquire during module imports
        with self._discovery_lock:
            # Check if already discovered (inside lock)
            if self._discovered:
                return

            # Mark as discovered to prevent infinite re-entry from same thread
            # (module imports during discovery might access registry)
            self._discovered = True

            # Try to load from cache first
            if self._cache_manager:
                try:
                    cached_plugins = self._cache_manager.load_cache()
                    if cached_plugins is not None:
                        # Reconstruct registry from cache
                        self.update(cached_plugins)
                        logger.info(
                            f"✅ Loaded {len(self)} {self._config.registry_name}s from cache"
                        )
                        return
                except Exception as e:
                    logger.debug(f"Cache load failed for {self._config.registry_name}: {e}")

            # Cache miss or disabled - perform full discovery
            try:
                pkg = importlib.import_module(self._config.discovery_package)

                if self._config.discovery_function:
                    self._config.discovery_function(
                        pkg.__path__,
                        f"{self._config.discovery_package}.",
                        self._base_class
                    )
                else:
                    root = self._config.discovery_package.split('.')[0]
                    mod = importlib.import_module(f"{root}.core.registry_discovery")
                    func = (
                        mod.discover_registry_classes_recursive
                        if self._config.discovery_recursive
                        else mod.discover_registry_classes
                    )
                    func(pkg.__path__, f"{self._config.discovery_package}.", self._base_class)

                logger.debug(f"Discovered {len(self)} {self._config.registry_name}s")

                # Save to cache if enabled
                if self._cache_manager:
                    try:
                        cache_utils = _get_cache_manager()
                        file_mtimes = cache_utils['get_package_file_mtimes'](
                            self._config.discovery_package
                        )
                        self._cache_manager.save_cache(dict(self), file_mtimes)
                    except Exception as e:
                        logger.debug(f"Failed to save cache for {self._config.registry_name}: {e}")

            except Exception as e:
                logger.warning(f"Discovery failed: {e}")
        # Lock released here - registry is now fully populated and safe to read

    def __getitem__(self, k):
        with self._discovery_lock:
            self._discover()
            return super().__getitem__(k)

    def __contains__(self, k):
        with self._discovery_lock:
            self._discover()
            return super().__contains__(k)

    def __iter__(self):
        with self._discovery_lock:
            self._discover()
            return super().__iter__()

    def __len__(self):
        with self._discovery_lock:
            self._discover()
            return super().__len__()

    def keys(self):
        with self._discovery_lock:
            self._discover()
            return super().keys()

    def values(self):
        with self._discovery_lock:
            self._discover()
            return super().values()

    def items(self):
        with self._discovery_lock:
            self._discover()
            return super().items()

    def get(self, k, default=None):
        with self._discovery_lock:
            self._discover()
            return super().get(k, default)


@dataclass(frozen=True)
class SecondaryRegistry:
    """Configuration for a secondary registry (e.g., metadata handlers)."""
    registry_dict: RegistryDict
    key_source: str  # 'primary' or attribute name
    attr_name: str   # Attribute to check on the class


@dataclass(frozen=True)
class RegistryConfig:
    """
    Configuration for automatic class registration behavior.

    This dataclass encapsulates all the configuration needed for metaclass
    registration, making the pattern explicit and easy to understand.

    Attributes:
        registry_dict: Dictionary to register classes into (e.g., MICROSCOPE_HANDLERS)
        key_attribute: Name of class attribute containing the registration key
                      (e.g., '_microscope_type', '_backend_type', '_context_type')
        key_extractor: Optional function to derive key from class name if key_attribute
                      is not set. Signature: (class_name: str, cls: Type) -> str
        skip_if_no_key: If True, skip registration when key_attribute is None.
                       If False, require either key_attribute or key_extractor.
        secondary_registries: Optional list of secondary registry configurations
        log_registration: If True, log debug message when class is registered
        registry_name: Human-readable name for logging (e.g., 'microscope handler')
        discovery_package: Optional package name to auto-discover (e.g., 'openhcs.microscopes')
        discovery_recursive: If True, use recursive discovery (default: False)

    Examples:
        # Microscope handlers with name-based key extraction and secondary registry
        RegistryConfig(
            registry_dict=MICROSCOPE_HANDLERS,
            key_attribute='_microscope_type',
            key_extractor=extract_key_from_handler_suffix,
            skip_if_no_key=False,
            secondary_registries=[
                SecondaryRegistry(
                    registry_dict=METADATA_HANDLERS,
                    key_source=PRIMARY_KEY,
                    attr_name='_metadata_handler_class'
                )
            ],
            log_registration=True,
            registry_name='microscope handler'
        )

        # Storage backends with explicit key and skip-if-none behavior
        RegistryConfig(
            registry_dict=STORAGE_BACKENDS,
            key_attribute='_backend_type',
            skip_if_no_key=True,
            registry_name='storage backend'
        )

        # Context providers with simple explicit key
        RegistryConfig(
            registry_dict=CONTEXT_PROVIDERS,
            key_attribute='_context_type',
            skip_if_no_key=True,
            registry_name='context provider'
        )
    """
    registry_dict: RegistryDict
    key_attribute: str
    key_extractor: Optional[KeyExtractor] = None
    skip_if_no_key: bool = False
    secondary_registries: Optional[list[SecondaryRegistry]] = None
    log_registration: bool = True
    registry_name: str = "plugin"
    discovery_package: Optional[str] = None  # Auto-inferred from base class module if None
    discovery_recursive: bool = False
    discovery_function: Optional[Callable] = None  # Custom discovery function


class AutoRegisterMeta(ABCMeta):
    """
    Generic metaclass for automatic plugin registration (Pattern A).
    
    This metaclass automatically registers concrete classes in a global registry
    when they are defined, eliminating the need for manual registration calls.
    
    Features:
    - Skips abstract classes (checks __abstractmethods__)
    - Supports explicit keys via class attributes
    - Supports derived keys via key extraction functions
    - Supports secondary registries (e.g., metadata handlers)
    - Configurable skip-if-no-key behavior
    - Debug logging for registration events
    
    Usage:
        # Create domain-specific metaclass
        class MicroscopeHandlerMeta(AutoRegisterMeta):
            def __new__(mcs, name, bases, attrs):
                return super().__new__(mcs, name, bases, attrs,
                                      registry_config=_MICROSCOPE_REGISTRY_CONFIG)
        
        # Use in class definition
        class ImageXpressHandler(MicroscopeHandler, metaclass=MicroscopeHandlerMeta):
            _microscope_type = 'imagexpress'  # Optional if key_extractor is provided
            _metadata_handler_class = ImageXpressMetadata  # Optional secondary registration
    
    Design Principles:
    - Explicit configuration over magic behavior
    - Preserve all domain-specific features
    - Zero breaking changes to existing code
    - Easy to understand and debug
    """
    
    def __new__(mcs, name: str, bases: tuple, attrs: dict,
                registry_config: Optional[RegistryConfig] = None):
        """
        Create a new class and register it if appropriate.

        Args:
            name: Name of the class being created
            bases: Base classes
            attrs: Class attributes dictionary
            registry_config: Configuration for registration behavior.
                           If None, auto-configures from class attributes or skips registration.

        Returns:
            The newly created class
        """
        # Create the class using ABCMeta
        new_class = super().__new__(mcs, name, bases, attrs)

        # Auto-configure registry if not provided but class has __registry__ attributes
        if registry_config is None:
            registry_config = mcs._auto_configure_registry(new_class, attrs)
            if registry_config is None:
                return new_class  # No config and no auto-config possible

        # Set up lazy discovery if registry dict supports it (only once for base class)
        if isinstance(registry_config.registry_dict, LazyDiscoveryDict) and not registry_config.registry_dict._config:
            from dataclasses import replace

            # Auto-infer discovery_package from base class module if not specified
            config = registry_config
            if config.discovery_package is None:
                # Extract package from base class module (e.g., 'openhcs.microscopes.microscope_base' → 'openhcs.microscopes')
                module_parts = new_class.__module__.rsplit('.', 1)
                inferred_package = module_parts[0] if len(module_parts) > 1 else new_class.__module__
                # Create new config with inferred package
                config = replace(config, discovery_package=inferred_package)
                logger.debug(f"Auto-inferred discovery_package='{inferred_package}' from {new_class.__module__}")

            # Auto-infer discovery_recursive based on package structure
            # Check if package has subdirectories with __init__.py (indicating nested structure)
            if config.discovery_package:
                try:
                    pkg = importlib.import_module(config.discovery_package)
                    if hasattr(pkg, '__path__'):
                        import os
                        has_subpackages = False
                        for path in pkg.__path__:
                            if os.path.isdir(path):
                                # Check if any subdirectories contain __init__.py
                                for entry in os.listdir(path):
                                    subdir = os.path.join(path, entry)
                                    if os.path.isdir(subdir) and os.path.exists(os.path.join(subdir, '__init__.py')):
                                        has_subpackages = True
                                        break
                            if has_subpackages:
                                break

                        # Only override if discovery_recursive is still at default (False)
                        # This allows explicit overrides to take precedence
                        if has_subpackages and not config.discovery_recursive:
                            config = replace(config, discovery_recursive=True)
                            logger.debug(f"Auto-inferred discovery_recursive=True for '{config.discovery_package}' (has subpackages)")
                        elif not has_subpackages and config.discovery_recursive:
                            logger.debug(f"Keeping explicit discovery_recursive=True for '{config.discovery_package}' (no subpackages detected)")
                except Exception as e:
                    logger.debug(f"Failed to auto-infer discovery_recursive: {e}")

            # Auto-wrap secondary registries with SecondaryRegistryDict
            if config.secondary_registries:
                import sys
                wrapped_secondaries = []
                module = sys.modules.get(new_class.__module__)

                for sec_reg in config.secondary_registries:
                    # Check if secondary registry needs wrapping
                    if isinstance(sec_reg.registry_dict, dict) and not isinstance(sec_reg.registry_dict, SecondaryRegistryDict):
                        # Create a new SecondaryRegistryDict wrapping the primary registry
                        wrapped_dict = SecondaryRegistryDict(registry_config.registry_dict)
                        # Copy any existing entries from the old dict
                        wrapped_dict.update(sec_reg.registry_dict)

                        # Find and update the module global variable
                        if module:
                            for var_name, var_value in vars(module).items():
                                if var_value is sec_reg.registry_dict:
                                    setattr(module, var_name, wrapped_dict)
                                    logger.debug(f"Auto-wrapped secondary registry '{var_name}' in {new_class.__module__}")
                                    break

                        # Create new SecondaryRegistry with wrapped dict
                        wrapped_sec_reg = SecondaryRegistry(
                            registry_dict=wrapped_dict,
                            key_source=sec_reg.key_source,
                            attr_name=sec_reg.attr_name
                        )
                        wrapped_secondaries.append(wrapped_sec_reg)
                    else:
                        wrapped_secondaries.append(sec_reg)

                # Rebuild config with wrapped secondary registries
                config = replace(config, secondary_registries=wrapped_secondaries)

            registry_config.registry_dict._set_config(new_class, config)

        # Only register concrete classes (not abstract base classes)
        if not bases or getattr(new_class, '__abstractmethods__', None):
            return new_class

        # Get or derive the registration key
        key = mcs._get_registration_key(name, new_class, registry_config)

        # Handle missing key
        if key is None:
            return mcs._handle_missing_key(name, registry_config)

        # Register in primary registry
        mcs._register_class(new_class, key, registry_config)

        # Handle secondary registrations
        if registry_config.secondary_registries:
            mcs._register_secondary(new_class, key, registry_config.secondary_registries)

        # Log registration if enabled
        if registry_config.log_registration:
            logger.debug(f"Auto-registered {name} as '{key}' {registry_config.registry_name}")

        return new_class
    
    @staticmethod
    def _get_registration_key(name: str, cls: Type, config: RegistryConfig) -> Optional[str]:
        """Get the registration key for a class (explicit or derived)."""
        # Try explicit key first
        key = getattr(cls, config.key_attribute, None)
        if key is not None:
            return key

        # Try key extractor if provided
        if config.key_extractor is not None:
            return config.key_extractor(name, cls)

        return None

    @staticmethod
    def _handle_missing_key(name: str, config: RegistryConfig) -> Type:
        """Handle case where no registration key is available."""
        if config.skip_if_no_key:
            if config.log_registration:
                logger.debug(f"Skipping registration for {name} - no {config.key_attribute}")
            return None  # Will be returned from __new__
        else:
            raise ValueError(
                f"Class {name} must have {config.key_attribute} attribute "
                f"or provide a key_extractor in registry config"
            )

    @classmethod
    def _auto_configure_registry(mcs, new_class: Type, attrs: dict) -> Optional[RegistryConfig]:
        """
        Auto-configure registry from metaclass OR base class attributes.

        Priority:
        1. Metaclass attributes (__registry_dict__, __registry_key__ on metaclass)
        2. Base class attributes (__registry_key__ on class, auto-create __registry__)
        3. Parent class __registry__ (inherit from parent)

        Returns:
            RegistryConfig if auto-configuration successful, None otherwise
        """
        # Check if the metaclass has __registry_dict__ attribute (old style)
        registry_dict = getattr(mcs, '__registry_dict__', None)

        # If no metaclass registry, check if base class wants auto-creation or inheritance
        if registry_dict is None:
            # First check if any parent class has __registry__ (inherit from parent)
            # This takes priority over creating a new registry
            for base in new_class.__mro__[1:]:  # Skip self
                if hasattr(base, '__registry__'):
                    registry_dict = base.__registry__
                    key_attribute = getattr(base, '__registry_key__', None)
                    key_extractor = getattr(base, '__key_extractor__', None)
                    skip_if_no_key = getattr(base, '__skip_if_no_key__', True)
                    secondary_registries = getattr(base, '__secondary_registries__', None)
                    registry_name = getattr(base, '__registry_name__', None)
                    break
            else:
                # No parent registry found - check if class explicitly defines __registry_key__
                # (only create new registry if __registry_key__ is in the class body, not inherited)
                key_attribute = attrs.get('__registry_key__')
                if key_attribute is not None:
                    # Auto-create registry dict and store on the class
                    registry_dict = LazyDiscoveryDict()
                    new_class.__registry__ = registry_dict

                    # Get other optional attributes from class
                    key_extractor = attrs.get('__key_extractor__')
                    skip_if_no_key = attrs.get('__skip_if_no_key__', True)
                    secondary_registries = attrs.get('__secondary_registries__')
                    registry_name = attrs.get('__registry_name__')
                else:
                    return None  # No registry configuration found
        else:
            # Old style: get from metaclass
            key_attribute = getattr(mcs, '__registry_key__', '_registry_key')
            key_extractor = getattr(mcs, '__key_extractor__', None)
            skip_if_no_key = getattr(mcs, '__skip_if_no_key__', True)
            secondary_registries = getattr(mcs, '__secondary_registries__', None)
            registry_name = getattr(mcs, '__registry_name__', None)

        # Auto-derive registry name if not provided
        if registry_name is None:
            # Derive from class name: "StorageBackend" → "storage backend"
            clean_name = new_class.__name__
            for suffix in ['Base', 'Meta', 'Handler', 'Registry']:
                if clean_name.endswith(suffix):
                    clean_name = clean_name[:-len(suffix)]
                    break
            # Convert CamelCase to space-separated lowercase
            import re
            registry_name = re.sub(r'([A-Z])', r' \1', clean_name).strip().lower()

        logger.debug(f"Auto-configured registry for {new_class.__name__}: "
                    f"key_attribute={key_attribute}, registry_name={registry_name}")

        return RegistryConfig(
            registry_dict=registry_dict,
            key_attribute=key_attribute,
            key_extractor=key_extractor,
            skip_if_no_key=skip_if_no_key,
            secondary_registries=secondary_registries,
            registry_name=registry_name
        )

    @staticmethod
    def _register_class(cls: Type, key: str, config: RegistryConfig) -> None:
        """Register class in primary registry."""
        config.registry_dict[key] = cls
        setattr(cls, config.key_attribute, key)

    @staticmethod
    def _register_secondary(
        cls: Type,
        primary_key: str,
        secondary_registries: list[SecondaryRegistry]
    ) -> None:
        """Handle secondary registry registrations."""
        for sec_reg in secondary_registries:
            value = getattr(cls, sec_reg.attr_name, None)
            if value is None:
                continue

            # Determine the key for secondary registration
            if sec_reg.key_source == PRIMARY_KEY:
                secondary_key = primary_key
            else:
                secondary_key = getattr(cls, sec_reg.key_source, None)
                if secondary_key is None:
                    logger.warning(
                        f"Cannot register {sec_reg.attr_name} for {cls.__name__} - "
                        f"no {sec_reg.key_source} attribute"
                    )
                    continue

            # Register in secondary registry
            sec_reg.registry_dict[secondary_key] = value
            logger.debug(f"Auto-registered {sec_reg.attr_name} from {cls.__name__} as '{secondary_key}'")


# Helper functions for common key extraction patterns

def make_suffix_extractor(suffix: str) -> KeyExtractor:
    """
    Create a key extractor that removes a suffix from class names.

    Args:
        suffix: The suffix to remove (e.g., 'Handler', 'Backend')

    Returns:
        A key extractor function

    Examples:
        extract_handler = make_suffix_extractor('Handler')
        extract_handler('ImageXpressHandler', cls) -> 'imagexpress'

        extract_backend = make_suffix_extractor('Backend')
        extract_backend('DiskStorageBackend', cls) -> 'diskstorage'
    """
    suffix_len = len(suffix)

    def extractor(name: str, cls: Type) -> str:
        if name.endswith(suffix):
            return name[:-suffix_len].lower()
        return name.lower()

    return extractor


# Pre-built extractors for common patterns
extract_key_from_handler_suffix = make_suffix_extractor('Handler')
extract_key_from_backend_suffix = make_suffix_extractor('Backend')

