"""
Fiji streaming backend for OpenHCS.

Streams image data directly to Fiji/ImageJ GUI for interactive exploration.
Uses PyImageJ to send numpy arrays directly to running Fiji instance.
Requires PyImageJ, JPype, and Maven to be properly configured.
"""

import logging
from pathlib import Path
from typing import Any, Union, List
import numpy as np

from openhcs.io.streaming import StreamingBackend
from openhcs.io.backend_registry import StorageBackendMeta
from openhcs.constants.constants import Backend

logger = logging.getLogger(__name__)


class FijiStreamingBackend(StreamingBackend, metaclass=StorageBackendMeta):
    """
    Fiji streaming backend with automatic metaclass registration.

    Streams image data directly to Fiji/ImageJ GUI for interactive exploration.
    Uses PyImageJ to send numpy arrays directly to running Fiji instance.
    """
    
    # Backend type from enum for registration
    _backend_type = Backend.FIJI_STREAM.value  # You'd need to add this to the Backend enum
    
    def __init__(self):
        """Initialize the Fiji streaming backend."""
        self._ij = None
        
    def save(self, data: Any, file_path: Union[str, Path], **kwargs) -> None:
        """
        Stream single image to Fiji.
        
        Args:
            data: Image data (numpy array)
            file_path: Identifier for the image
            **kwargs: Additional metadata
        """
        if not isinstance(data, np.ndarray):
            logger.warning(f"Fiji streaming requires numpy arrays, got {type(data)}")
            return
            
        # Send image directly to Fiji GUI using PyImageJ (fail loudly)
        self._send_to_fiji_pyimagej(data, str(file_path), **kwargs)
        logger.debug(f"🔬 FIJI: Streamed {file_path} to Fiji GUI for exploration")
    
    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """
        Stream batch of images to Fiji.
        
        Args:
            data_list: List of image data arrays
            file_paths: List of file path identifiers
            **kwargs: Additional metadata
        """
        if len(data_list) != len(file_paths):
            raise ValueError("Data list and file paths must have same length")
        
        for data, file_path in zip(data_list, file_paths):
            self.save(data, file_path, **kwargs)
        
        logger.info(f"🔬 FIJI: Streamed batch of {len(data_list)} images to Fiji")

    def _send_to_fiji_pyimagej(self, data: np.ndarray, identifier: str, **kwargs) -> None:
        """Send image directly to Fiji using PyImageJ."""
        # Try to import PyImageJ
        try:
            import imagej
        except ImportError:
            raise ImportError("PyImageJ not available. Install with: pip install 'openhcs[viz]'")

        # Initialize PyImageJ connection if not already done
        if not hasattr(self, '_ij') or self._ij is None:
            logger.info("🔬 FIJI: Attempting to connect via PyImageJ...")
            self._ij = imagej.init(mode='interactive')
            logger.info("🔬 FIJI: ✅ Connected to Fiji via PyImageJ")

        # Convert numpy array to ImageJ format and display
        ij_image = self._ij.py.to_java(data)
        self._ij.ui().show(identifier, ij_image)

        # Apply auto-contrast if requested
        if kwargs.get('auto_contrast', True):
            self._ij.op().run("enhance.contrast", ij_image)

        logger.info(f"🔬 FIJI: ✅ Sent {identifier} to Fiji via PyImageJ")


    


        
        # Example using command line (requires Fiji installation)
        try:
            import subprocess
            
            # Write macro to temporary file
            macro_file = self._temp_dir / "temp_macro.ijm"
            macro_file.write_text(macro_cmd)
            
            # Execute via Fiji (adjust path as needed)
            fiji_path = self._get_fiji_path()
            if fiji_path:
                subprocess.run([
                    str(fiji_path), 
                    "--headless", 
                    "--console", 
                    "-macro", 
                    str(macro_file)
                ], check=False, capture_output=True)
            
        except Exception as e:
            logger.warning(f"Failed to execute Fiji macro: {e}")
    
    def _get_fiji_path(self) -> Path:
        """Get path to Fiji executable."""
        # Try common Fiji installation paths
        common_paths = [
            Path("/Applications/Fiji.app/Contents/MacOS/ImageJ-macosx"),  # macOS
            Path("C:/Fiji.app/ImageJ-win64.exe"),  # Windows
            Path("/opt/fiji/ImageJ-linux64"),  # Linux
            Path.home() / "Fiji.app" / "ImageJ-linux64",  # User installation
        ]
        
        for path in common_paths:
            if path.exists():
                return path
        
        logger.warning("Fiji executable not found in common locations")
        return None
    
    def cleanup(self) -> None:
        """Clean up temporary files and resources."""
        # Clean up temporary directory
        if self._temp_dir and self._temp_dir.exists():
            try:
                import shutil
                shutil.rmtree(self._temp_dir)
                logger.debug("Cleaned up Fiji temporary files")
            except Exception as e:
                logger.warning(f"Failed to cleanup Fiji temp directory: {e}")
        
        self._temp_dir = None
        self._macro_queue.clear()
        
        logger.debug("Fiji streaming backend cleaned up")
