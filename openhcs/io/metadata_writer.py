"""
Atomic metadata writer for OpenHCS with concurrency safety.

Provides specialized atomic operations for OpenHCS metadata files with proper
locking and merging to prevent race conditions in multiprocessing environments.
"""

import logging
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Dict, Optional, Union

from .atomic import atomic_update_json, FileLockError, LOCK_CONFIG

logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class MetadataConfig:
    """Configuration constants for metadata operations."""
    METADATA_FILENAME: str = "openhcs_metadata.json"
    SUBDIRECTORIES_KEY: str = "subdirectories"
    AVAILABLE_BACKENDS_KEY: str = "available_backends"
    DEFAULT_TIMEOUT: float = LOCK_CONFIG.DEFAULT_TIMEOUT


METADATA_CONFIG = MetadataConfig()


class MetadataWriteError(Exception):
    """Raised when metadata write operations fail."""
    pass


class AtomicMetadataWriter:
    """Atomic metadata writer with file locking for concurrent safety."""

    def __init__(self, timeout: float = METADATA_CONFIG.DEFAULT_TIMEOUT):
        self.timeout = timeout
        self.logger = logging.getLogger(__name__)

    def _execute_update(self, metadata_path: Union[str, Path], update_func: Callable, default_data: Optional[Dict] = None) -> None:
        """Execute atomic update with error handling."""
        try:
            atomic_update_json(metadata_path, update_func, self.timeout, default_data)
        except FileLockError as e:
            raise MetadataWriteError(f"Failed to update metadata: {e}") from e

    def _ensure_subdirectories_structure(self, data: Optional[Dict[str, Any]]) -> Dict[str, Any]:
        """Ensure metadata has proper subdirectories structure."""
        data = data or {}
        data.setdefault(METADATA_CONFIG.SUBDIRECTORIES_KEY, {})
        return data


    
    def update_available_backends(self, metadata_path: Union[str, Path], available_backends: Dict[str, bool]) -> None:
        """Atomically update available backends in metadata."""
        def update_func(data):
            if data is None:
                raise MetadataWriteError("Cannot update backends: metadata file does not exist")
            data[METADATA_CONFIG.AVAILABLE_BACKENDS_KEY] = available_backends
            return data

        self._execute_update(metadata_path, update_func)
        self.logger.debug(f"Updated available backends in {metadata_path}")
    
    def merge_subdirectory_metadata(self, metadata_path: Union[str, Path], subdirectory_updates: Dict[str, Dict[str, Any]]) -> None:
        """Atomically merge multiple subdirectory metadata updates.

        Performs deep merge - updates fields within subdirectories without replacing entire entries.

        Example:
            Existing: {"TimePoint_1": {"available_backends": {"disk": True}, "main": True}}
            Updates:  {"TimePoint_1": {"main": False}}
            Result:   {"TimePoint_1": {"available_backends": {"disk": True}, "main": False}}
        """
        def update_func(data):
            data = self._ensure_subdirectories_structure(data)
            subdirs = data[METADATA_CONFIG.SUBDIRECTORIES_KEY]

            # Deep merge each subdirectory update
            for subdir_name, updates in subdirectory_updates.items():
                if subdir_name in subdirs:
                    # Merge into existing subdirectory
                    subdirs[subdir_name].update(updates)
                else:
                    # Create new subdirectory
                    subdirs[subdir_name] = updates

            return data

        self._execute_update(metadata_path, update_func, {METADATA_CONFIG.SUBDIRECTORIES_KEY: {}})
        self.logger.debug(f"Merged {len(subdirectory_updates)} subdirectories in {metadata_path}")
    



def get_metadata_path(plate_root: Union[str, Path]) -> Path:
    """
    Get the standard metadata file path for a plate root directory.
    
    Args:
        plate_root: Path to the plate root directory
        
    Returns:
        Path to the metadata file
    """
    return Path(plate_root) / METADATA_CONFIG.METADATA_FILENAME
