"""
Storage backend metaclass registration system.

Eliminates hardcoded backend registration by using metaclass auto-registration
following OpenHCS generic solution principles. Backends are automatically
discovered and registered when their classes are defined.
"""

import logging
from abc import ABCMeta
from typing import Dict, Type
from openhcs.io.base import DataSink, StorageBackend

logger = logging.getLogger(__name__)

# Global registry of storage backends - populated by metaclass
STORAGE_BACKENDS: Dict[str, Type[DataSink]] = {}

# Global registry of backend instances - created lazily
_backend_instances: Dict[str, DataSink] = {}


class StorageBackendMeta(ABCMeta):
    """
    Metaclass for automatic registration of storage backends.
    
    Automatically registers backend classes when they are defined,
    eliminating the need for hardcoded registration in factory functions.
    """

    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)

        # Only register concrete implementations (not abstract base classes)
        if not getattr(new_class, '__abstractmethods__', None):
            # Extract backend type from class attributes or class name
            backend_type = getattr(new_class, '_backend_type', None)
            
            if backend_type is None:
                # Skip registration if no explicit backend type
                logger.debug(f"Skipping registration for {name} - no explicit _backend_type attribute")
                return new_class

            # Auto-register in STORAGE_BACKENDS
            STORAGE_BACKENDS[backend_type] = new_class

            # Store the backend type as a class attribute
            new_class._backend_type = backend_type

            logger.debug(f"Auto-registered {name} as '{backend_type}' backend")

        return new_class


def get_backend_instance(backend_type: str) -> DataSink:
    """
    Get backend instance by type with lazy instantiation.

    Args:
        backend_type: Backend type identifier (e.g., 'disk', 'memory')

    Returns:
        Backend instance

    Raises:
        KeyError: If backend type not registered
        RuntimeError: If backend instantiation fails
    """
    backend_type = backend_type.lower()

    # Return cached instance if available
    if backend_type in _backend_instances:
        return _backend_instances[backend_type]

    # Get backend class from registry
    if backend_type not in STORAGE_BACKENDS:
        raise KeyError(f"Backend type '{backend_type}' not registered. "
                      f"Available backends: {list(STORAGE_BACKENDS.keys())}")

    backend_class = STORAGE_BACKENDS[backend_type]

    try:
        # Create and cache instance
        instance = backend_class()
        _backend_instances[backend_type] = instance
        logger.debug(f"Created instance for backend '{backend_type}'")
        return instance
    except Exception as e:
        raise RuntimeError(f"Failed to instantiate backend '{backend_type}': {e}") from e


def create_storage_registry() -> Dict[str, DataSink]:
    """
    Create storage registry with all registered backends.

    Returns:
        Dictionary mapping backend types to instances
    """
    # Ensure all backends are discovered
    discover_all_backends()

    # Backends that require context-specific initialization (e.g., plate_root)
    # These are registered lazily when needed, not at startup
    SKIP_BACKENDS = {'virtual_workspace'}

    registry = {}
    for backend_type in STORAGE_BACKENDS.keys():
        # Skip backends that need context-specific initialization
        if backend_type in SKIP_BACKENDS:
            logger.debug(f"Skipping backend '{backend_type}' - requires context-specific initialization")
            continue

        try:
            registry[backend_type] = get_backend_instance(backend_type)
        except Exception as e:
            logger.warning(f"Failed to create instance for backend '{backend_type}': {e}")
            continue

    logger.info(f"Created storage registry with {len(registry)} backends: {list(registry.keys())}")
    return registry


def cleanup_backend_connections() -> None:
    """
    Clean up backend connections without affecting persistent resources.

    For napari streaming backend, this cleans up ZeroMQ connections but
    leaves the napari window open for future use.
    """
    import os

    # Check if we're running in test mode
    is_test_mode = (
        'pytest' in os.environ.get('_', '') or
        'PYTEST_CURRENT_TEST' in os.environ or
        any('pytest' in arg for arg in __import__('sys').argv)
    )

    for backend_type, instance in _backend_instances.items():
        # Use targeted cleanup for napari streaming to preserve window
        if hasattr(instance, 'cleanup_connections'):
            try:
                instance.cleanup_connections()
                logger.debug(f"Cleaned up connections for backend '{backend_type}'")
            except Exception as e:
                logger.warning(f"Failed to cleanup connections for backend '{backend_type}': {e}")
        elif hasattr(instance, 'cleanup') and backend_type != 'napari_stream':
            try:
                instance.cleanup()
                logger.debug(f"Cleaned up backend '{backend_type}'")
            except Exception as e:
                logger.warning(f"Failed to cleanup backend '{backend_type}': {e}")

    # In test mode, also stop viewer processes to allow pytest to exit
    if is_test_mode:
        try:
            from openhcs.runtime.napari_stream_visualizer import _cleanup_global_viewer
            _cleanup_global_viewer()
            logger.debug("Cleaned up napari viewer for test mode")
        except ImportError:
            pass  # napari not available
        except Exception as e:
            logger.warning(f"Failed to cleanup napari viewer: {e}")

        try:
            from openhcs.runtime.fiji_stream_visualizer import _cleanup_global_fiji_viewer
            _cleanup_global_fiji_viewer()
            logger.debug("Cleaned up Fiji viewer for test mode")
        except ImportError:
            pass  # fiji visualizer not available
        except Exception as e:
            logger.warning(f"Failed to cleanup Fiji viewer: {e}")

    logger.info(f"Backend connections cleaned up ({'test mode' if is_test_mode else 'napari window preserved'})")


def cleanup_all_backends() -> None:
    """
    Clean up all cached backend instances completely.

    This is for full shutdown - clears instance cache and calls full cleanup.
    Use cleanup_backend_connections() for test cleanup to preserve napari window.
    """
    for backend_type, instance in _backend_instances.items():
        if hasattr(instance, 'cleanup'):
            try:
                instance.cleanup()
                logger.debug(f"Cleaned up backend '{backend_type}'")
            except Exception as e:
                logger.warning(f"Failed to cleanup backend '{backend_type}': {e}")

    _backend_instances.clear()
    logger.info("All backend instances cleaned up")


def discover_all_backends() -> None:
    """
    Discover all storage backends using generic discovery.

    Uses generic discovery to find and import all StorageBackend subclasses,
    which triggers their metaclass registration into STORAGE_BACKENDS.

    In subprocess runner mode (OPENHCS_SUBPROCESS_NO_GPU=1), only discovers
    essential backends (disk, memory) to avoid GPU library imports.
    """
    import os
    from openhcs.core.registry_discovery import discover_registry_classes

    # Check if we're in subprocess runner mode and should skip GPU-heavy backends
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        # Subprocess runner mode - only discover essential backends
        # Import essential backend modules directly to trigger registration
        try:
            import openhcs.io.disk  # noqa: F401
            import openhcs.io.memory  # noqa: F401
            logger.debug(f"Subprocess runner mode - discovered {len(STORAGE_BACKENDS)} essential backends: {list(STORAGE_BACKENDS.keys())}")
        except ImportError as e:
            logger.warning(f"Could not import essential backend modules: {e}")
    else:
        # Normal mode - discover all backends using generic discovery
        import openhcs.io

        # Use generic discovery to find all backends
        # This imports the modules, triggering metaclass registration
        _ = discover_registry_classes(
            package_path=openhcs.io.__path__,
            package_prefix="openhcs.io.",
            base_class=StorageBackend,
            exclude_modules={'base', 'backend_registry', 'exceptions', 'atomic', 'filemanager', 'metadata_writer'}
        )

        logger.debug(f"Discovered {len(STORAGE_BACKENDS)} storage backends: {list(STORAGE_BACKENDS.keys())}")
