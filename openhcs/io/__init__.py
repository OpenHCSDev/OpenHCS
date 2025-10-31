"""
Storage backends package for openhcs.

This package contains the storage backend implementations for openhcs.
"""

import os

# Essential imports (always available)
from .atomic import file_lock, atomic_write_json, atomic_update_json, FileLockError, FileLockTimeoutError
from .base import BackendBase, DataSink, DataSource, ReadOnlyBackend, StorageBackend, storage_registry, reset_memory_backend, ensure_storage_registry, get_backend
from .backend_registry import (
    get_backend_instance,
    cleanup_backend_connections, cleanup_all_backends, STORAGE_BACKENDS
)
from .disk import DiskStorageBackend
from .filemanager import FileManager
from .memory import MemoryStorageBackend
from .metadata_writer import AtomicMetadataWriter, MetadataWriteError, get_metadata_path, get_subdirectory_name
from .metadata_migration import detect_legacy_format, migrate_legacy_metadata, migrate_plate_metadata
from .pipeline_migration import detect_legacy_pipeline, migrate_pipeline_file, load_pipeline_with_migration
from .streaming import StreamingBackend

# GPU-heavy backend classes are imported lazily via __getattr__ below
# This prevents blocking imports of zarr (→ ome-zarr → dask → GPU libs)
# and streaming backends (→ napari/fiji)

__all__ = [
    'BackendBase',
    'DataSink',
    'DataSource',
    'ReadOnlyBackend',
    'StorageBackend',
    'StreamingBackend',
    'storage_registry',
    'reset_memory_backend',
    'ensure_storage_registry',
    'get_backend',
    'get_backend_instance',
    'cleanup_all_backends',
    'STORAGE_BACKENDS',
    'DiskStorageBackend',
    'MemoryStorageBackend',
    'NapariStreamingBackend',
    'FijiStreamingBackend',
    'ZarrStorageBackend',
    'FileManager',
    'file_lock',
    'atomic_write_json',
    'atomic_update_json',
    'FileLockError',
    'FileLockTimeoutError',
    'AtomicMetadataWriter',
    'MetadataWriteError',
    'get_metadata_path',
    'get_subdirectory_name',
    'detect_legacy_format',
    'migrate_legacy_metadata',
    'migrate_plate_metadata',
    'detect_legacy_pipeline',
    'migrate_pipeline_file',
    'load_pipeline_with_migration'
]


# Registry for lazy-loaded GPU-heavy backends
_LAZY_BACKEND_REGISTRY = {
    'NapariStreamingBackend': ('openhcs.io.napari_stream', 'NapariStreamingBackend'),
    'FijiStreamingBackend': ('openhcs.io.fiji_stream', 'FijiStreamingBackend'),
    'ZarrStorageBackend': ('openhcs.io.zarr', 'ZarrStorageBackend'),
}


def __getattr__(name):
    """
    Lazy import of GPU-heavy backend classes.

    This prevents blocking imports during `import openhcs.io` while
    still allowing code to import backend classes when needed.
    """
    # Check if name is in lazy backend registry
    if name not in _LAZY_BACKEND_REGISTRY:
        raise AttributeError(f"module '{__name__}' has no attribute '{name}'")

    # Subprocess runner mode - create placeholder
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        class PlaceholderBackend:
            """Placeholder for subprocess runner mode."""
            pass
        PlaceholderBackend.__name__ = name
        PlaceholderBackend.__qualname__ = name
        return PlaceholderBackend

    # Normal mode - lazy import from registry
    module_path, class_name = _LAZY_BACKEND_REGISTRY[name]
    import importlib
    module = importlib.import_module(module_path)
    return getattr(module, class_name)
