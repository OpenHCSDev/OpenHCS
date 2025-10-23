"""Virtual Workspace Backend - Symlink-free workspace using metadata mapping."""

import logging
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Union
from fnmatch import fnmatch

from openhcs.io.backend_registry import StorageBackendMeta
from openhcs.io.disk import DiskStorageBackend
from openhcs.io.metadata_writer import get_metadata_path
from openhcs.io.exceptions import StorageResolutionError

logger = logging.getLogger(__name__)


class VirtualWorkspaceBackend(metaclass=StorageBackendMeta):
    """
    Read-only path translation layer for virtual workspace.

    Maps virtual filenames to real plate files using workspace_mapping from
    openhcs_metadata.json (plate-relative paths), then delegates I/O to DiskStorageBackend.

    This is NOT a storage backend - it's a path resolver. It does not support save operations.

    Follows OMERO backend pattern:
    - Explicit initialization with plate_root
    - Fail-loud path resolution
    - No path inspection or 'workspace' searching

    Uses PLATE-RELATIVE paths (no workspace directory):
    - Mapping: {"Images/r01c01f05.tif": "Images/r01c01f01.tif"}
    - Resolution: plate_root / "Images/r01c01f05.tif" → plate_root / "Images/r01c01f01.tif"

    Example:
        backend = VirtualWorkspaceBackend(plate_root=Path("/data/plate"))
        # Input: plate_root / "Images/r01c01f05.tif" (doesn't exist)
        # Resolves to: plate_root / "Images/r01c01f01.tif" (exists)
    """
    
    _backend_type = 'virtual_workspace'  # Auto-registers via metaclass
    
    def __init__(self, plate_root: Path):
        """
        Initialize with explicit plate root.
        
        Args:
            plate_root: Path to plate directory containing openhcs_metadata.json
            
        Raises:
            FileNotFoundError: If metadata file doesn't exist
            ValueError: If no workspace_mapping in metadata
        """
        self.plate_root = Path(plate_root)
        self.disk_backend = DiskStorageBackend()
        self._mapping_cache: Optional[Dict[str, str]] = None
        self._cache_mtime: Optional[float] = None
        
        # Load mapping eagerly - fail loud if metadata missing
        self._load_mapping()
    
    def _load_mapping(self) -> Dict[str, str]:
        """
        Load workspace_mapping from metadata with mtime-based caching.
        
        Returns:
            Combined mapping from all subdirectories
            
        Raises:
            FileNotFoundError: If metadata file doesn't exist
            ValueError: If no workspace_mapping in metadata
        """
        metadata_path = get_metadata_path(self.plate_root)
        if not metadata_path.exists():
            raise FileNotFoundError(
                f"Metadata not found: {metadata_path}\n"
                f"Plate root: {self.plate_root}"
            )
        
        # Check cache with mtime invalidation
        current_mtime = metadata_path.stat().st_mtime
        if self._mapping_cache is not None and self._cache_mtime == current_mtime:
            return self._mapping_cache
        
        # Load and combine mappings from all subdirectories
        with open(metadata_path, 'r') as f:
            metadata = json.load(f)
        
        combined_mapping = {}
        for subdir_data in metadata.get('subdirectories', {}).values():
            workspace_mapping = subdir_data.get('workspace_mapping', {})
            combined_mapping.update(workspace_mapping)
        
        if not combined_mapping:
            raise ValueError(
                f"No workspace_mapping in {metadata_path}\n"
                f"Plate root: {self.plate_root}\n"
                f"This is not a virtual workspace."
            )
        
        # Cache it
        self._mapping_cache = combined_mapping
        self._cache_mtime = current_mtime
        
        logger.info(f"Loaded {len(combined_mapping)} mappings for {self.plate_root}")
        return combined_mapping
    
    def _resolve_path(self, path: Union[str, Path]) -> str:
        """
        Resolve virtual path to real plate path using plate-relative mapping.

        Pure mapping-based resolution - no physical path fallbacks.
        Follows OMERO backend pattern: all paths go through mapping.

        Args:
            path: Absolute or relative path (e.g., "/data/plate/Images/r01c01f05.tif" or "Images/r01c01f05.tif")

        Returns:
            Real absolute path: e.g., "/data/plate/Images/r01c01f01.tif"

        Raises:
            StorageResolutionError: If path not in mapping
        """
        path_obj = Path(path)

        # Convert to plate-relative path
        try:
            relative_path = path_obj.relative_to(self.plate_root)
        except ValueError:
            # Already relative or different root
            relative_path = path_obj

        # Normalize Windows backslashes to forward slashes
        relative_str = str(relative_path).replace('\\', '/')

        # Load mapping if not cached
        if self._mapping_cache is None:
            self._load_mapping()

        # Resolve via mapping - fail loud if not in mapping
        if relative_str not in self._mapping_cache:
            raise StorageResolutionError(
                f"Path not in virtual workspace mapping: {relative_str}\n"
                f"Plate root: {self.plate_root}\n"
                f"Available virtual paths: {len(self._mapping_cache)}\n"
                f"This path must be accessed through the virtual workspace mapping."
            )

        real_relative = self._mapping_cache[relative_str]
        real_absolute = self.plate_root / real_relative
        logger.debug(f"Resolved virtual → real: {relative_str} → {real_relative}")
        return str(real_absolute)
    
    def load(self, file_path: Union[str, Path], **kwargs) -> Any:
        """Load file from virtual workspace."""
        real_path = self._resolve_path(file_path)
        return self.disk_backend.load(real_path, **kwargs)
    
    def load_batch(self, file_paths: List[Union[str, Path]], **kwargs) -> List[Any]:
        """Load multiple files from virtual workspace."""
        real_paths = [self._resolve_path(fp) for fp in file_paths]
        return self.disk_backend.load_batch(real_paths, **kwargs)
    
    def list_files(self, directory: Union[str, Path], pattern: Optional[str] = None,
                  extensions: Optional[Set[str]] = None, recursive: bool = False,
                  **kwargs) -> List[str]:
        """
        List files in directory (returns absolute paths of virtual files).

        Returns absolute virtual paths from mapping that match the directory.

        Raises:
            ValueError: If mapping not loaded
        """
        dir_path = Path(directory)

        # Convert to plate-relative
        try:
            relative_dir = dir_path.relative_to(self.plate_root)
        except ValueError:
            # Already relative
            relative_dir = dir_path

        # Load mapping - fail loud if missing
        if self._mapping_cache is None:
            self._load_mapping()

        # Filter paths in this directory
        results = []
        for virtual_relative in self._mapping_cache.keys():
            vpath = Path(virtual_relative)

            # Check directory match
            if recursive:
                try:
                    vpath.relative_to(relative_dir)
                except ValueError:
                    continue
            else:
                if vpath.parent != relative_dir:
                    continue

            # Apply filters
            if pattern and not fnmatch(vpath.name, pattern):
                continue
            if extensions and vpath.suffix not in extensions:
                continue

            # Return absolute path
            results.append(str(self.plate_root / virtual_relative))

        return sorted(results)

    def list_dir(self, path: Union[str, Path]) -> List[str]:
        """
        List directory entries (names only, not full paths).

        For virtual workspace, this returns the unique directory names
        that exist in the mapping under the given path.
        """
        path = Path(path)

        # Convert to plate-relative path
        if path.is_absolute():
            try:
                relative_path = path.relative_to(self.plate_root)
            except ValueError:
                # Path is not under plate_root
                raise FileNotFoundError(f"Path not under plate root: {path}")
        else:
            relative_path = path

        # Normalize to string with forward slashes
        relative_str = str(relative_path).replace('\\', '/')
        if relative_str == '.':
            relative_str = ''

        # Collect all unique directory/file names under this path
        entries = set()
        for virtual_relative in self._mapping_cache.keys():
            # Check if this virtual path is under the requested directory
            if relative_str:
                # Looking for children of a subdirectory
                if not virtual_relative.startswith(relative_str + '/'):
                    continue
                # Get the part after the directory prefix
                remainder = virtual_relative[len(relative_str) + 1:]
            else:
                # Looking for top-level entries
                remainder = virtual_relative

            # Get the first component (immediate child)
            first_component = remainder.split('/')[0] if '/' in remainder else remainder
            if first_component:
                entries.add(first_component)

        return sorted(entries)

    def exists(self, path: Union[str, Path]) -> bool:
        """Check if virtual path exists (file in mapping or directory containing files)."""
        if self._mapping_cache is None:
            self._load_mapping()

        try:
            relative_str = str(Path(path).relative_to(self.plate_root))
        except ValueError:
            relative_str = str(path)

        # Normalize Windows backslashes to forward slashes
        relative_str = relative_str.replace('\\', '/')

        # File in mapping or directory prefix
        return (relative_str in self._mapping_cache or
                any(vp.startswith(relative_str + '/') for vp in self._mapping_cache))
    
    def is_file(self, path: Union[str, Path]) -> bool:
        """Check if virtual path is a file (exists in mapping directly)."""
        if self._mapping_cache is None:
            self._load_mapping()

        try:
            relative_str = str(Path(path).relative_to(self.plate_root))
        except ValueError:
            relative_str = str(path)

        # Normalize Windows backslashes to forward slashes
        relative_str = relative_str.replace('\\', '/')

        # File if it's directly in the mapping
        return relative_str in self._mapping_cache

    def is_dir(self, path: Union[str, Path]) -> bool:
        """Check if virtual path is a directory (has files under it)."""
        if self._mapping_cache is None:
            self._load_mapping()

        try:
            relative_str = str(Path(path).relative_to(self.plate_root))
        except ValueError:
            relative_str = str(path)

        # Normalize to string with forward slashes
        relative_str = relative_str.replace('\\', '/')
        if relative_str == '.':
            relative_str = ''

        # Directory if any virtual path starts with this prefix
        if relative_str:
            return any(vp.startswith(relative_str + '/') for vp in self._mapping_cache)
        else:
            # Root is always a directory if mapping exists
            return len(self._mapping_cache) > 0

    @property
    def requires_filesystem_validation(self) -> bool:
        """Virtual backends don't require filesystem validation."""
        return False

