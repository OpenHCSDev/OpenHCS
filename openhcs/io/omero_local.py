# openhcs/io/omero_local.py
"""
OMERO Local Storage Backend - Zero-copy server-side OMERO access.

Reads directly from OMERO binary repository, saves results back to OMERO.
"""

import logging
from pathlib import Path
from typing import Any, List, Optional, Union

import numpy as np

from openhcs.io.base import StorageBackend
from openhcs.io.backend_registry import StorageBackendMeta

logger = logging.getLogger(__name__)


class OMEROLocalBackend(StorageBackend, metaclass=StorageBackendMeta):
    """Storage backend for OMERO server-side execution with zero-copy access."""

    _backend_type = 'omero_local'

    def __init__(self, omero_data_dir: Optional[Path] = None, omero_conn=None):
        try:
            from omero.gateway import BlitzGateway
            self._BlitzGateway = BlitzGateway
        except ImportError:
            raise ImportError("omero-py required: pip install omero-py")

        if omero_data_dir:
            omero_data_dir = Path(omero_data_dir)
            if not omero_data_dir.exists():
                raise ValueError(f"OMERO data directory not found: {omero_data_dir}")

        self.omero_data_dir = omero_data_dir
        self.omero_conn = omero_conn

    def _get_connection(self, **kwargs):
        """Get OMERO connection from instance or kwargs."""
        conn = kwargs.get('omero_conn', self.omero_conn)
        if not conn:
            raise ValueError("No OMERO connection available")
        return conn
    
    def _get_local_file_path(self, image_id: int, conn) -> Path:
        """Resolve OMERO image ID to local filesystem path."""
        image = conn.getObject("Image", image_id)
        if not image:
            raise FileNotFoundError(f"OMERO image not found: {image_id}")

        fileset = image.getFileset()
        if not fileset:
            raise ValueError(f"Image {image_id} has no fileset")

        orig_files = list(fileset.listFiles())
        if not orig_files:
            raise ValueError(f"Image {image_id} has no files")

        orig_file = orig_files[0]

        if not self.omero_data_dir:
            raise ValueError("omero_data_dir not set")

        file_path = self.omero_data_dir / orig_file.getPath() / orig_file.getName()

        if not file_path.exists():
            raise FileNotFoundError(f"File not found: {file_path}")

        return file_path
    
    def load(self, file_path: Union[str, Path], **kwargs) -> Any:
        """Load image from OMERO. Returns 3D numpy array."""
        conn = self._get_connection(**kwargs)

        # Get image ID
        image_id = kwargs.get('image_id')
        if not image_id:
            try:
                image_id = int(file_path)
            except (ValueError, TypeError):
                raise ValueError(f"image_id required, got file_path={file_path}")

        # Two modes: direct file access (zero-copy) or API access
        if self.omero_data_dir:
            # Mode 1: Direct file access (zero-copy, server-side only)
            local_path = self._get_local_file_path(image_id, conn)
            suffix = local_path.suffix.lower()

            if suffix in ['.tif', '.tiff']:
                import tifffile
                data = tifffile.imread(local_path)
            elif suffix == '.zarr':
                import zarr
                data = zarr.open(local_path, mode='r')[:]
            else:
                raise ValueError(f"Unsupported format: {suffix}")
        else:
            # Mode 2: OMERO API access (works from anywhere)
            data = self._load_via_api(image_id, conn)

        # Ensure 3D
        if data.ndim == 2:
            data = data[np.newaxis, ...]

        return data

    def _load_via_api(self, image_id: int, conn) -> np.ndarray:
        """Load image via OMERO API (slower but works remotely)."""
        image = conn.getObject("Image", image_id)
        if not image:
            raise FileNotFoundError(f"OMERO image not found: {image_id}")

        # Get image dimensions
        sizeZ = image.getSizeZ()
        sizeC = image.getSizeC()
        sizeT = image.getSizeT()
        sizeY = image.getSizeY()
        sizeX = image.getSizeX()

        # For now, load first timepoint only
        # TODO: Support multi-timepoint images
        if sizeT > 1:
            logger.warning(f"Image {image_id} has {sizeT} timepoints, loading first only")

        # Load pixels
        pixels = image.getPrimaryPixels()

        # Build 3D array (Z, Y, X) or 4D (Z, C, Y, X)
        if sizeC == 1:
            # Single channel: (Z, Y, X)
            data = np.zeros((sizeZ, sizeY, sizeX), dtype=np.uint16)
            for z in range(sizeZ):
                plane = pixels.getPlane(z, 0, 0)  # z, c, t
                data[z] = plane
        else:
            # Multi-channel: (Z, C, Y, X)
            data = np.zeros((sizeZ, sizeC, sizeY, sizeX), dtype=np.uint16)
            for z in range(sizeZ):
                for c in range(sizeC):
                    plane = pixels.getPlane(z, c, 0)  # z, c, t
                    data[z, c] = plane

        return data
    
    def save(self, data: Any, output_path: Union[str, Path], **kwargs) -> None:
        """Save data to OMERO as new image."""
        conn = self._get_connection(**kwargs)

        dataset_id = kwargs.get('dataset_id')
        if not dataset_id:
            raise ValueError("dataset_id required")

        dataset = conn.getObject("Dataset", dataset_id)
        if not dataset:
            raise ValueError(f"Dataset not found: {dataset_id}")

        image_name = Path(output_path).stem if isinstance(output_path, (str, Path)) else str(output_path)

        # Get dimensions
        if data.ndim == 3:
            sizeZ, sizeY, sizeX = data.shape
            sizeC, sizeT = 1, 1
        elif data.ndim == 4:
            sizeZ, sizeC, sizeY, sizeX = data.shape
            sizeT = 1
        else:
            raise ValueError(f"Data must be 3D or 4D, got {data.shape}")

        # Plane generator
        def planes():
            if data.ndim == 3:
                for z in range(sizeZ):
                    yield data[z]
            else:
                for z in range(sizeZ):
                    for c in range(sizeC):
                        yield data[z, c]

        # Create image
        new_image = conn.createImageFromNumpySeq(
            planes(),
            image_name,
            sizeZ=sizeZ,
            sizeC=sizeC,
            sizeT=sizeT,
            description=kwargs.get('description', 'Processed by OpenHCS'),
            dataset=dataset
        )

        logger.info(f"Created OMERO image {new_image.getId()}: {image_name}")
    
    def save_batch(self, data_list: List[Any], identifiers: List[Union[str, Path]], **kwargs) -> None:
        """Save multiple images to OMERO."""
        if len(data_list) != len(identifiers):
            raise ValueError(f"Length mismatch: {len(data_list)} vs {len(identifiers)}")

        for data, identifier in zip(data_list, identifiers):
            self.save(data, identifier, **kwargs)

    def list_files(self, directory: Union[str, Path], pattern: str = "*", **kwargs) -> List[Path]:
        """List images in OMERO dataset."""
        conn = self._get_connection(**kwargs)

        try:
            dataset_id = int(directory)
        except (ValueError, TypeError):
            raise ValueError(f"directory must be dataset ID, got: {directory}")

        dataset = conn.getObject("Dataset", dataset_id)
        if not dataset:
            raise ValueError(f"Dataset not found: {dataset_id}")

        # List images
        image_ids = []
        for image in dataset.listChildren():
            if pattern != "*":
                import fnmatch
                if not fnmatch.fnmatch(image.getName(), pattern):
                    continue

            image_ids.append(Path(str(image.getId())))

        return image_ids

    def load_batch(self, file_paths: List[Union[str, Path]], **kwargs) -> List[Any]:
        """Load multiple images from OMERO."""
        return [self.load(fp, **kwargs) for fp in file_paths]

    # Filesystem operations - not supported for OMERO
    def list_dir(self, path: Union[str, Path]) -> List[str]:
        """Not supported for OMERO backend."""
        raise NotImplementedError("list_dir not supported for OMERO backend")

    def delete(self, file_path: Union[str, Path]) -> None:
        """Not supported for OMERO backend."""
        raise NotImplementedError("delete not supported for OMERO backend")

    def delete_all(self, file_path: Union[str, Path]) -> None:
        """Not supported for OMERO backend."""
        raise NotImplementedError("delete_all not supported for OMERO backend")

    def ensure_directory(self, directory: Union[str, Path]) -> Path:
        """Not supported for OMERO backend."""
        raise NotImplementedError("ensure_directory not supported for OMERO backend")

    def create_symlink(self, source: Union[str, Path], link_name: Union[str, Path]):
        """Not supported for OMERO backend."""
        raise NotImplementedError("create_symlink not supported for OMERO backend")

    def is_symlink(self, source: Union[str, Path]) -> bool:
        """Not supported for OMERO backend."""
        raise NotImplementedError("is_symlink not supported for OMERO backend")

    def is_file(self, source: Union[str, Path]) -> bool:
        """Not supported for OMERO backend."""
        raise NotImplementedError("is_file not supported for OMERO backend")

    def is_dir(self, source: Union[str, Path]) -> bool:
        """Not supported for OMERO backend."""
        raise NotImplementedError("is_dir not supported for OMERO backend")

    def move(self, src: Union[str, Path], dst: Union[str, Path]) -> None:
        """Not supported for OMERO backend."""
        raise NotImplementedError("move not supported for OMERO backend")

    def copy(self, src: Union[str, Path], dst: Union[str, Path]) -> None:
        """Not supported for OMERO backend."""
        raise NotImplementedError("copy not supported for OMERO backend")

    def stat(self, path: Union[str, Path]) -> dict:
        """Not supported for OMERO backend."""
        raise NotImplementedError("stat not supported for OMERO backend")

