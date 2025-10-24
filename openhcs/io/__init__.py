"""
Storage backends package for openhcs.

This package contains the storage backend implementations for openhcs.
"""

import os

# Essential imports (always available)
from .atomic import file_lock, atomic_write_json, atomic_update_json, FileLockError, FileLockTimeoutError
from .base import DataSink, StorageBackend, storage_registry, reset_memory_backend, ensure_storage_registry, get_backend
from .backend_registry import (
    StorageBackendMeta, get_backend_instance, discover_all_backends,
    cleanup_backend_connections, cleanup_all_backends, STORAGE_BACKENDS
)
from .disk import DiskStorageBackend
from .filemanager import FileManager
from .memory import MemoryStorageBackend
from .metadata_writer import AtomicMetadataWriter, MetadataWriteError, get_metadata_path
from .metadata_migration import detect_legacy_format, migrate_legacy_metadata, migrate_plate_metadata
from .pipeline_migration import detect_legacy_pipeline, migrate_pipeline_file, load_pipeline_with_migration
from .streaming import StreamingBackend

# GPU-heavy backend classes are imported lazily via __getattr__ below
# This prevents blocking imports of zarr (→ ome-zarr → dask → GPU libs)
# and streaming backends (→ napari/fiji)

__all__ = [
    'DataSink',
    'StorageBackend',
    'StreamingBackend',
    'storage_registry',
    'reset_memory_backend',
    'ensure_storage_registry',
    'get_backend',
    'StorageBackendMeta',
    'get_backend_instance',
    'discover_all_backends',
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
    'detect_legacy_format',
    'migrate_legacy_metadata',
    'migrate_plate_metadata',
    'detect_legacy_pipeline',
    'migrate_pipeline_file',
    'load_pipeline_with_migration'
]


def __getattr__(name):
    """
    Lazy import of GPU-heavy backend classes.

    This prevents blocking imports during `import openhcs.io` while
    still allowing code to import backend classes when needed.
    """
    # Check if we're in subprocess runner mode
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        # Subprocess runner mode - create placeholder classes
        if name in ('NapariStreamingBackend', 'FijiStreamingBackend', 'ZarrStorageBackend'):
            class PlaceholderBackend:
                """Placeholder for subprocess runner mode."""
                pass
            PlaceholderBackend.__name__ = name
            PlaceholderBackend.__qualname__ = name
            return PlaceholderBackend
    else:
        # Normal mode - lazy import the real classes
        if name == 'NapariStreamingBackend':
            from openhcs.io.napari_stream import NapariStreamingBackend
            return NapariStreamingBackend
        elif name == 'FijiStreamingBackend':
            from openhcs.io.fiji_stream import FijiStreamingBackend
            return FijiStreamingBackend
        elif name == 'ZarrStorageBackend':
            from openhcs.io.zarr import ZarrStorageBackend
            return ZarrStorageBackend

    raise AttributeError(f"module '{__name__}' has no attribute '{name}'")
