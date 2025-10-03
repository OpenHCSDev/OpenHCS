# openhcs/io/omero_local.py
"""
OMERO Local Storage Backend

This module provides a storage backend that reads directly from OMERO's binary
repository using local filesystem access. This is designed for server-side
execution where OpenHCS runs on the same machine as OMERO.server.

Key Features:
- Zero-copy data access (reads directly from OMERO binary repository)
- Saves results back to OMERO as new images
- Preserves metadata and provenance
- Fail-loud error handling (no defensive programming)

Architecture:
- Uses BlitzGateway for OMERO metadata queries
- Uses local filesystem access for image data (no network overhead)
- Integrates with OpenHCS FileManager via StorageBackend interface
"""

import logging
from pathlib import Path
from typing import Any, Dict, List, Optional, Union

import numpy as np

from openhcs.io.base import StorageBackend
from openhcs.io.backend_registry import StorageBackendMeta

logger = logging.getLogger(__name__)


class OMEROLocalBackend(StorageBackend, metaclass=StorageBackendMeta):
    """
    Storage backend for OMERO server-side execution.
    
    Reads directly from OMERO binary repository using local filesystem access.
    Saves results back to OMERO as new images.
    
    This backend is designed for use when OpenHCS runs on the same server as
    OMERO, enabling zero-copy data access.
    """
    
    # Backend type for registration
    _backend_type = 'omero_local'
    
    def __init__(self, omero_data_dir: Optional[Path] = None, omero_conn=None):
        """
        Initialize OMERO local backend.
        
        Args:
            omero_data_dir: Path to OMERO binary repository (e.g., /OMERO/Files)
                           If None, will attempt to detect from environment
            omero_conn: BlitzGateway connection for metadata queries
                       If None, backend will require connection to be passed in kwargs
        
        Raises:
            ImportError: If omero-py is not installed
            ValueError: If omero_data_dir doesn't exist
        """
        # Import OMERO dependencies
        try:
            from omero.gateway import BlitzGateway
            self._BlitzGateway = BlitzGateway
        except ImportError:
            raise ImportError(
                "omero-py is required for OMEROLocalBackend. "
                "Install with: pip install omero-py"
            )
        
        # Store OMERO data directory
        if omero_data_dir is not None:
            omero_data_dir = Path(omero_data_dir)
            if not omero_data_dir.exists():
                raise ValueError(f"OMERO data directory does not exist: {omero_data_dir}")
        
        self.omero_data_dir = omero_data_dir
        self.omero_conn = omero_conn
        
        logger.info(f"Initialized OMEROLocalBackend with data_dir={omero_data_dir}")
    
    def _get_connection(self, **kwargs):
        """
        Get OMERO connection from instance or kwargs.
        
        Args:
            **kwargs: May contain 'omero_conn' key
        
        Returns:
            BlitzGateway connection
        
        Raises:
            ValueError: If no connection available
        """
        conn = kwargs.get('omero_conn', self.omero_conn)
        if conn is None:
            raise ValueError(
                "No OMERO connection available. "
                "Pass omero_conn in kwargs or provide during initialization."
            )
        return conn
    
    def _get_local_file_path(self, image_id: int, conn) -> Path:
        """
        Resolve OMERO image ID to local filesystem path.
        
        Args:
            image_id: OMERO image ID
            conn: BlitzGateway connection
        
        Returns:
            Path to image file in OMERO binary repository
        
        Raises:
            FileNotFoundError: If image or file doesn't exist
            ValueError: If image has no associated files
        """
        # Get image object
        image = conn.getObject("Image", image_id)
        if image is None:
            raise FileNotFoundError(f"OMERO image not found: {image_id}")
        
        # Get fileset (original files)
        fileset = image.getFileset()
        if fileset is None:
            raise ValueError(f"Image {image_id} has no associated fileset")
        
        # Get first original file
        # Note: For multi-file formats, this gets the first file
        # TODO: Handle multi-file formats properly
        orig_files = list(fileset.listFiles())
        if not orig_files:
            raise ValueError(f"Image {image_id} has no original files")
        
        orig_file = orig_files[0]
        
        # Construct local path
        # OMERO stores files in: /OMERO/Files/<hash>/<filename>
        if self.omero_data_dir is None:
            raise ValueError("omero_data_dir not set - cannot resolve local path")
        
        file_path = self.omero_data_dir / orig_file.getPath() / orig_file.getName()
        
        if not file_path.exists():
            raise FileNotFoundError(
                f"OMERO file not found at expected path: {file_path}\n"
                f"Image ID: {image_id}, File ID: {orig_file.getId()}"
            )
        
        return file_path
    
    def load(self, file_path: Union[str, Path], **kwargs) -> Any:
        """
        Load image from OMERO.
        
        Args:
            file_path: OMERO image ID (as string/int) or path
            **kwargs: Must contain either:
                     - 'image_id': OMERO image ID (int)
                     - 'omero_conn': BlitzGateway connection (optional if set in __init__)
        
        Returns:
            3D numpy array (Z, Y, X) or (Z, C, Y, X) for multi-channel
        
        Raises:
            FileNotFoundError: If image doesn't exist
            ValueError: If image_id not provided
            ImportError: If required image library not available
        """
        conn = self._get_connection(**kwargs)
        
        # Get image ID from kwargs
        image_id = kwargs.get('image_id')
        if image_id is None:
            # Try to parse from file_path if it's an integer
            try:
                image_id = int(file_path)
            except (ValueError, TypeError):
                raise ValueError(
                    "image_id must be provided in kwargs for OMERO backend. "
                    f"Got file_path={file_path}"
                )
        
        # Get local file path
        local_path = self._get_local_file_path(image_id, conn)
        
        # Load image based on file extension
        suffix = local_path.suffix.lower()
        
        if suffix in ['.tif', '.tiff']:
            # Load TIFF
            try:
                import tifffile
            except ImportError:
                raise ImportError("tifffile required for TIFF support: pip install tifffile")
            
            data = tifffile.imread(local_path)
            
        elif suffix == '.zarr':
            # Load Zarr
            try:
                import zarr
            except ImportError:
                raise ImportError("zarr required for Zarr support: pip install zarr")
            
            data = zarr.open(local_path, mode='r')[:]
            
        else:
            raise ValueError(f"Unsupported file format: {suffix}")
        
        # Ensure 3D array (OpenHCS contract)
        if data.ndim == 2:
            data = data[np.newaxis, ...]  # Add Z dimension
        
        logger.debug(f"Loaded image {image_id} from {local_path}, shape={data.shape}")
        return data
    
    def save(self, data: Any, output_path: Union[str, Path], **kwargs) -> None:
        """
        Save data to OMERO as a new image.
        
        Args:
            data: Numpy array to save (3D or 4D)
            output_path: Image name in OMERO
            **kwargs: Must contain:
                     - 'dataset_id': OMERO dataset ID to link image to
                     - 'omero_conn': BlitzGateway connection (optional if set in __init__)
                     Optional:
                     - 'description': Image description
                     - 'channel_names': List of channel names
        
        Raises:
            ValueError: If dataset_id not provided
            RuntimeError: If image creation fails
        """
        conn = self._get_connection(**kwargs)
        
        # Get dataset ID
        dataset_id = kwargs.get('dataset_id')
        if dataset_id is None:
            raise ValueError("dataset_id must be provided in kwargs for OMERO save")
        
        # Get dataset
        dataset = conn.getObject("Dataset", dataset_id)
        if dataset is None:
            raise ValueError(f"OMERO dataset not found: {dataset_id}")
        
        # Prepare image name
        image_name = Path(output_path).stem if isinstance(output_path, (str, Path)) else str(output_path)
        
        # Get image dimensions
        if data.ndim == 3:
            sizeZ, sizeY, sizeX = data.shape
            sizeC = 1
            sizeT = 1
        elif data.ndim == 4:
            sizeZ, sizeC, sizeY, sizeX = data.shape
            sizeT = 1
        else:
            raise ValueError(f"Data must be 3D or 4D, got shape {data.shape}")
        
        # Create plane generator
        def plane_generator():
            """Generate 2D planes for OMERO upload."""
            if data.ndim == 3:
                # Single channel
                for z in range(sizeZ):
                    yield data[z]
            else:
                # Multi-channel
                for z in range(sizeZ):
                    for c in range(sizeC):
                        yield data[z, c]
        
        # Create image in OMERO
        try:
            new_image = conn.createImageFromNumpySeq(
                plane_generator(),
                image_name,
                sizeZ=sizeZ,
                sizeC=sizeC,
                sizeT=sizeT,
                description=kwargs.get('description', f'Processed by OpenHCS'),
                dataset=dataset
            )
            
            logger.info(f"Created OMERO image {new_image.getId()}: {image_name}")
            
        except Exception as e:
            raise RuntimeError(f"Failed to create OMERO image: {e}") from e
    
    def save_batch(self, data_list: List[Any], identifiers: List[Union[str, Path]], **kwargs) -> None:
        """
        Save multiple images to OMERO.
        
        Args:
            data_list: List of numpy arrays
            identifiers: List of image names
            **kwargs: Same as save()
        
        Raises:
            ValueError: If data_list and identifiers have different lengths
        """
        if len(data_list) != len(identifiers):
            raise ValueError(
                f"data_list and identifiers must have same length. "
                f"Got {len(data_list)} and {len(identifiers)}"
            )
        
        for data, identifier in zip(data_list, identifiers):
            self.save(data, identifier, **kwargs)
    
    def list_files(self, directory: Union[str, Path], pattern: str = "*", **kwargs) -> List[Path]:
        """
        List images in OMERO dataset.
        
        Args:
            directory: OMERO dataset ID (as string/int)
            pattern: Filename pattern (glob-style)
            **kwargs: Must contain 'omero_conn' (optional if set in __init__)
        
        Returns:
            List of image IDs as Path objects (for compatibility)
        
        Raises:
            ValueError: If dataset not found
        """
        conn = self._get_connection(**kwargs)
        
        # Get dataset ID
        try:
            dataset_id = int(directory)
        except (ValueError, TypeError):
            raise ValueError(f"directory must be OMERO dataset ID, got: {directory}")
        
        # Get dataset
        dataset = conn.getObject("Dataset", dataset_id)
        if dataset is None:
            raise ValueError(f"OMERO dataset not found: {dataset_id}")
        
        # List images
        image_ids = []
        for image in dataset.listChildren():
            # Filter by pattern if needed
            if pattern != "*":
                import fnmatch
                if not fnmatch.fnmatch(image.getName(), pattern):
                    continue
            
            # Return image ID as Path (for compatibility with StorageBackend interface)
            image_ids.append(Path(str(image.getId())))
        
        logger.debug(f"Listed {len(image_ids)} images in dataset {dataset_id}")
        return image_ids

