"""
Registry Service - Clean function discovery and metadata access.

Provides unified access to all registry implementations with automatic discovery.
Follows OpenHCS generic solution principle - automatically adapts to new registries.
"""

import pkgutil
import importlib
import inspect
import logging
from typing import Dict, List, Optional
from .unified_registry import LibraryRegistryBase, FunctionMetadata

logger = logging.getLogger(__name__)


class RegistryService:
    """
    Clean service for registry discovery and function metadata access.
    
    Automatically discovers all registry implementations and provides
    unified access to their functions with caching.
    """
    
    _metadata_cache: Optional[Dict[str, FunctionMetadata]] = None
    
    @classmethod
    def get_all_functions_with_metadata(cls) -> Dict[str, FunctionMetadata]:
        """Get unified metadata for all functions from all registries."""
        if cls._metadata_cache is not None:
            logger.debug(f"🎯 REGISTRY SERVICE: Using cached metadata ({len(cls._metadata_cache)} functions)")
            return cls._metadata_cache

        logger.debug("🎯 REGISTRY SERVICE: Discovering functions from all registries...")
        all_functions = {}

        # Discover all registry classes automatically
        registry_classes = cls._discover_registries()

        # Load functions from each registry
        for registry_class in registry_classes:
            try:
                registry_instance = registry_class()

                # Skip if library not available
                if not registry_instance.is_library_available():
                    logger.warning(f"Library {registry_instance.library_name} not available, skipping")
                    continue

                # Get functions from this registry (with caching)
                logger.debug(f"🎯 REGISTRY SERVICE: Calling _load_or_discover_functions for {registry_instance.library_name}")
                functions = registry_instance._load_or_discover_functions()
                logger.debug(f"🎯 REGISTRY SERVICE: Retrieved {len(functions)} {registry_instance.library_name} functions")

                # Use composite keys to prevent function name collisions between backends
                # Format: "backend:function_name" (e.g., "torch:stack_percentile_normalize")
                for func_name, metadata in functions.items():
                    composite_key = f"{registry_instance.library_name}:{func_name}"
                    all_functions[composite_key] = metadata

            except Exception as e:
                logger.warning(f"Failed to load registry {registry_class.__name__}: {e}")
                continue

        logger.info(f"Total functions discovered: {len(all_functions)}")
        cls._metadata_cache = all_functions
        return all_functions
    
    @classmethod
    def _discover_registries(cls) -> List[type]:
        """Automatically discover all registry implementations."""
        registry_classes = []
        
        # Scan lib_registry package for modules
        import openhcs.processing.backends.lib_registry as registry_package
        registry_path = registry_package.__path__
        registry_prefix = registry_package.__name__ + "."
        
        for importer, module_name, ispkg in pkgutil.iter_modules(registry_path, registry_prefix):
            # Skip unified_registry (contains base classes)
            if module_name.endswith('.unified_registry'):
                continue
                
            try:
                module = importlib.import_module(module_name)
                
                # Find registry classes in module
                for name, obj in inspect.getmembers(module, inspect.isclass):
                    if (issubclass(obj, LibraryRegistryBase) and 
                        obj is not LibraryRegistryBase and
                        obj.__module__ == module_name):
                        
                        registry_classes.append(obj)
                        
            except Exception as e:
                logger.warning(f"Failed to load registry module {module_name}: {e}")
                continue
        
        logger.info(f"Discovered {len(registry_classes)} registry implementations")
        return registry_classes
    
    @classmethod
    def clear_metadata_cache(cls) -> None:
        """Clear cached metadata to force re-discovery."""
        cls._metadata_cache = None
        logger.info("Registry metadata cache cleared")


# Backward compatibility aliases
FunctionRegistryService = RegistryService
get_all_functions_with_metadata = RegistryService.get_all_functions_with_metadata
clear_metadata_cache = RegistryService.clear_metadata_cache
