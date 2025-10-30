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
from abc import ABCMeta
from dataclasses import dataclass
from typing import Dict, Type, Optional, Callable, Any

logger = logging.getLogger(__name__)


# Type aliases for clarity
RegistryDict = Dict[str, Type]
KeyExtractor = Callable[[str, Type], str]

# Constants for key sources
PRIMARY_KEY = 'primary'


class LazyDiscoveryDict(dict):
    """Dict that auto-discovers plugins on first access."""

    def __init__(self):
        super().__init__()
        self._base_class = None
        self._config = None
        self._discovered = False

    def _set_config(self, base_class: Type, config: 'RegistryConfig') -> None:
        self._base_class = base_class
        self._config = config

    def _discover(self) -> None:
        """Run discovery once."""
        if self._discovered or not self._config or not self._config.discovery_package:
            return
        self._discovered = True

        try:
            pkg = importlib.import_module(self._config.discovery_package)

            if self._config.discovery_function:
                self._config.discovery_function(pkg.__path__, f"{self._config.discovery_package}.", self._base_class)
            else:
                root = self._config.discovery_package.split('.')[0]
                mod = importlib.import_module(f"{root}.core.registry_discovery")
                func = mod.discover_registry_classes_recursive if self._config.discovery_recursive else mod.discover_registry_classes
                func(pkg.__path__, f"{self._config.discovery_package}.", self._base_class)

            logger.debug(f"Discovered {len(self)} {self._config.registry_name}s")
        except Exception as e:
            logger.warning(f"Discovery failed: {e}")

    def __getitem__(self, k):
        self._discover()
        return super().__getitem__(k)

    def __contains__(self, k):
        self._discover()
        return super().__contains__(k)

    def __iter__(self):
        self._discover()
        return super().__iter__()

    def __len__(self):
        self._discover()
        return super().__len__()

    def keys(self):
        self._discover()
        return super().keys()

    def values(self):
        self._discover()
        return super().values()

    def items(self):
        self._discover()
        return super().items()

    def get(self, k, default=None):
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
                           If None, no registration is performed (for base metaclass itself).

        Returns:
            The newly created class
        """
        # Create the class using ABCMeta
        new_class = super().__new__(mcs, name, bases, attrs)

        # Skip registration if no config provided (base metaclass itself)
        if registry_config is None:
            return new_class

        # Set up lazy discovery if registry dict supports it (only once for base class)
        if isinstance(registry_config.registry_dict, LazyDiscoveryDict) and not registry_config.registry_dict._config:
            # Auto-infer discovery_package from base class module if not specified
            config = registry_config
            if config.discovery_package is None:
                # Extract package from base class module (e.g., 'openhcs.microscopes.microscope_base' → 'openhcs.microscopes')
                module_parts = new_class.__module__.rsplit('.', 1)
                inferred_package = module_parts[0] if len(module_parts) > 1 else new_class.__module__
                # Create new config with inferred package
                from dataclasses import replace
                config = replace(config, discovery_package=inferred_package)
                logger.debug(f"Auto-inferred discovery_package='{inferred_package}' from {new_class.__module__}")

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

