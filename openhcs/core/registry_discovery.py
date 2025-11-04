"""
Generic registry class discovery utility.

Consolidates duplicated registry discovery patterns across:
- Library registries (processing backends)
- Format registries (experimental analysis)
- Microscope handler registries
- Storage backend registries

This module eliminates ~70 lines of duplicated pkgutil + importlib boilerplate
by providing a single, well-tested discovery function.
"""

import importlib
import inspect
import logging
import pkgutil
from collections.abc import Iterable
from typing import Callable, List, Optional, Set, Type

logger = logging.getLogger(__name__)


def discover_registry_classes(
    package_path: Iterable[str],
    package_prefix: str,
    base_class: Type,
    exclude_modules: Optional[Set[str]] = None,
    validation_func: Optional[Callable[[Type], bool]] = None,
    skip_packages: bool = True
) -> List[Type]:
    """
    Generic registry class discovery using pkgutil + importlib pattern.
    
    Scans a package for classes that inherit from a base class and automatically
    discovers them for registration. This eliminates duplicated discovery code
    across different registry systems.
    
    Args:
        package_path: Package __path__ attribute to scan (e.g., openhcs.io.__path__)
                     Accepts any iterable of strings (List, Tuple, _NamespacePath, etc.)
        package_prefix: Module prefix for importlib (e.g., "openhcs.io.")
        base_class: Base class to filter for (e.g., StorageBackend)
        exclude_modules: Set of module name substrings to skip (e.g., {'base', 'registry'})
        validation_func: Optional function to validate discovered classes
                        Should return True to include, False to exclude
        skip_packages: If True, skip package directories (default: True)
        
    Returns:
        List of discovered registry classes
        
    Example:
        >>> from openhcs.io.base import StorageBackend
        >>> import openhcs.io
        >>> backends = discover_registry_classes(
        ...     package_path=openhcs.io.__path__,
        ...     package_prefix="openhcs.io.",
        ...     base_class=StorageBackend,
        ...     exclude_modules={'base', 'backend_registry'}
        ... )
        >>> print([b.__name__ for b in backends])
        ['DiskStorageBackend', 'MemoryStorageBackend', 'ZarrStorageBackend']
    """
    registry_classes = []
    exclude_modules = exclude_modules or set()
    
    logger.debug(
        f"Discovering registry classes: base={base_class.__name__}, "
        f"prefix={package_prefix}, exclude={exclude_modules}"
    )
    
    for importer, module_name, ispkg in pkgutil.iter_modules(package_path, package_prefix):
        # Skip packages if requested
        if ispkg and skip_packages:
            continue
            
        # Skip excluded modules
        if any(excluded in module_name for excluded in exclude_modules):
            logger.debug(f"Skipping excluded module: {module_name}")
            continue
            
        try:
            # Import the module
            module = importlib.import_module(module_name)
            
            # Find all classes in the module
            for name, obj in inspect.getmembers(module, inspect.isclass):
                # Filter for subclasses of base_class
                if not issubclass(obj, base_class):
                    continue
                    
                # Exclude the base class itself
                if obj is base_class:
                    continue
                    
                # Only include classes defined in this module (not imported)
                if obj.__module__ != module_name:
                    continue
                    
                # Apply optional validation function
                if validation_func and not validation_func(obj):
                    logger.debug(f"Validation failed for {obj.__name__}")
                    continue
                    
                logger.debug(f"Discovered registry class: {obj.__name__} from {module_name}")
                registry_classes.append(obj)
                    
        except ImportError as e:
            # Skip modules that can't be imported (e.g., missing optional dependencies)
            logger.debug(f"Could not import module {module_name}: {e}")
            continue
        except Exception as e:
            # Log unexpected errors but continue discovery
            logger.warning(f"Failed to load registry module {module_name}: {e}")
            continue
    
    logger.info(
        f"Discovered {len(registry_classes)} registry classes for {base_class.__name__}: "
        f"{[cls.__name__ for cls in registry_classes]}"
    )
    
    return registry_classes


def discover_registry_classes_recursive(
    package_path: Iterable[str],
    package_prefix: str,
    base_class: Type,
    exclude_modules: Optional[Set[str]] = None,
    validation_func: Optional[Callable[[Type], bool]] = None
) -> List[Type]:
    """
    Recursive version of discover_registry_classes that walks entire package tree.
    
    Uses pkgutil.walk_packages instead of iter_modules to recursively scan
    all subpackages. Useful for deeply nested registry structures.
    
    Args:
        package_path: Package __path__ attribute to scan
                     Accepts any iterable of strings (List, Tuple, _NamespacePath, etc.)
        package_prefix: Module prefix for importlib
        base_class: Base class to filter for
        exclude_modules: Set of module name substrings to skip
        validation_func: Optional function to validate discovered classes
        
    Returns:
        List of discovered registry classes
        
    Example:
        >>> from openhcs.processing.backends.lib_registry.unified_registry import LibraryRegistryBase
        >>> import openhcs.processing.backends.experimental_analysis
        >>> registries = discover_registry_classes_recursive(
        ...     package_path=openhcs.processing.backends.experimental_analysis.__path__,
        ...     package_prefix="openhcs.processing.backends.experimental_analysis.",
        ...     base_class=MicroscopeFormatRegistryBase,
        ...     exclude_modules={'base'}
        ... )
    """
    registry_classes = []
    exclude_modules = exclude_modules or set()
    
    logger.debug(
        f"Discovering registry classes (recursive): base={base_class.__name__}, "
        f"prefix={package_prefix}, exclude={exclude_modules}"
    )
    
    # Walk through all modules in the package tree
    for importer, modname, ispkg in pkgutil.walk_packages(package_path, prefix=package_prefix):
        # Skip packages (only process modules)
        if ispkg:
            continue
            
        # Skip excluded modules
        if any(excluded in modname for excluded in exclude_modules):
            logger.debug(f"Skipping excluded module: {modname}")
            continue
            
        try:
            # Import the module
            module = importlib.import_module(modname)
            
            # Find all classes in the module
            for attr_name in dir(module):
                attr = getattr(module, attr_name)
                
                # Check if it's a class
                if not isinstance(attr, type):
                    continue
                    
                # Check if it's a subclass of base_class
                if not issubclass(attr, base_class):
                    continue
                    
                # Exclude the base class itself
                if attr is base_class:
                    continue
                    
                # Apply optional validation function
                if validation_func and not validation_func(attr):
                    logger.debug(f"Validation failed for {attr.__name__}")
                    continue
                    
                logger.debug(f"Discovered registry class: {attr.__name__} from {modname}")
                registry_classes.append(attr)
                    
        except ImportError as e:
            # Skip modules that can't be imported
            logger.debug(f"Could not import module {modname}: {e}")
            continue
        except Exception as e:
            # Log unexpected errors but continue discovery
            logger.warning(f"Failed to load registry module {modname}: {e}")
            continue
    
    logger.info(
        f"Discovered {len(registry_classes)} registry classes (recursive) for {base_class.__name__}: "
        f"{[cls.__name__ for cls in registry_classes]}"
    )
    
    return registry_classes

