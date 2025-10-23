"""
Storage backends package for openhcs.

This package contains the storage backend implementations for openhcs.
"""

import os

# Essential imports (always available)
from .atomic import file_lock, atomic_write_json, atomic_update_json, FileLockError, FileLockTimeoutError
from .base import DataSink, StorageBackend, storage_registry, reset_memory_backend
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

# GPU-heavy imports (only in normal mode)
if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') != '1':
    from .napari_stream import NapariStreamingBackend
    from .fiji_stream import FijiStreamingBackend
    from .zarr import ZarrStorageBackend
else:
    # Subprocess runner mode - create placeholder classes to avoid import errors
    class NapariStreamingBackend:
        """Placeholder for subprocess runner mode."""
        pass

    class FijiStreamingBackend:
        """Placeholder for subprocess runner mode."""
        pass

    class ZarrStorageBackend:
        """Placeholder for subprocess runner mode."""
        pass

__all__ = [
    'DataSink',
    'StorageBackend',
    'StreamingBackend',
    'storage_registry',
    'reset_memory_backend',
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
