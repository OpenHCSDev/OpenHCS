"""
Napari streaming backend for real-time visualization during processing.

This module provides a storage backend that streams image data to a napari viewer
for real-time visualization during pipeline execution. Uses ZeroMQ for IPC
and shared memory for efficient data transfer.
"""

import logging
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Union, Set
from os import PathLike

import numpy as np

from openhcs.io.streaming import StreamingBackend
from openhcs.constants.constants import DEFAULT_NAPARI_STREAM_PORT

logger = logging.getLogger(__name__)


class NapariStreamingBackend(StreamingBackend):
    """
    Napari streaming backend for real-time visualization.

    Streams image data to napari viewer using ZeroMQ.
    Connects to existing NapariStreamVisualizer process.
    Inherits from StreamingBackend - no file system operations.
    """

    def __init__(self):
        """Initialize the napari streaming backend."""
        self._publisher = None
        self._shared_memory_blocks = {}

    def _get_publisher(self):
        """Lazy initialization of ZeroMQ publisher."""
        if self._publisher is None:
            try:
                import zmq
                context = zmq.Context()
                self._publisher = context.socket(zmq.PUB)

                # Connect to napari viewer process on constant port
                self._publisher.connect(f"tcp://localhost:{DEFAULT_NAPARI_STREAM_PORT}")
                logger.info(f"Napari streaming publisher connected to viewer on port {DEFAULT_NAPARI_STREAM_PORT}")

                # Small delay to ensure socket is ready
                time.sleep(0.1)

            except ImportError:
                logger.error("ZeroMQ not available - napari streaming disabled")
                raise RuntimeError("ZeroMQ required for napari streaming")

        return self._publisher
    
    def save(self, data: Any, file_path: Union[str, Path], **kwargs) -> None:
        """
        Stream a single image to napari.
        
        Args:
            data: Image data (numpy array or compatible)
            file_path: Path identifier for the image
            **kwargs: Additional metadata
        """
        try:
            publisher = self._get_publisher()
            
            # Convert data to numpy if needed
            if hasattr(data, 'cpu'):  # PyTorch tensor
                np_data = data.cpu().numpy()
            elif hasattr(data, 'get'):  # CuPy array
                np_data = data.get()
            else:
                np_data = np.asarray(data)
            
            # Create shared memory block
            import multiprocessing as mp
            shm_name = f"napari_stream_{id(data)}_{time.time_ns()}"
            
            try:
                shm = mp.shared_memory.SharedMemory(create=True, size=np_data.nbytes, name=shm_name)
                shm_array = np.ndarray(np_data.shape, dtype=np_data.dtype, buffer=shm.buf)
                shm_array[:] = np_data[:]
                
                # Send metadata via ZeroMQ
                metadata = {
                    'path': str(file_path),
                    'shape': np_data.shape,
                    'dtype': str(np_data.dtype),
                    'shm_name': shm_name,
                    'timestamp': time.time()
                }
                
                publisher.send_json(metadata)
                logger.debug(f"Streamed {file_path} to napari (shape: {np_data.shape})")
                
                # Store reference to prevent cleanup
                self._shared_memory_blocks[shm_name] = shm
                
            except Exception as e:
                logger.warning(f"Failed to create shared memory for {file_path}: {e}")
                # Fallback: send data directly (less efficient)
                metadata = {
                    'path': str(file_path),
                    'data': np_data.tolist(),
                    'shape': np_data.shape,
                    'dtype': str(np_data.dtype),
                    'timestamp': time.time()
                }
                publisher.send_json(metadata)
                
        except Exception as e:
            logger.warning(f"Failed to stream {file_path} to napari: {e}")
    
    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """
        Stream multiple images to napari.
        
        Args:
            data_list: List of image data
            file_paths: List of path identifiers
            **kwargs: Additional metadata
        """
        if len(data_list) != len(file_paths):
            raise ValueError("data_list and file_paths must have the same length")
        
        for data, path in zip(data_list, file_paths):
            self.save(data, path, **kwargs)
    
    # REMOVED: All file system methods (load, load_batch, exists, list_files, delete, etc.)
    # These are no longer inherited - clean interface!
    
    def cleanup(self) -> None:
        """Clean up shared memory blocks and close publisher."""
        # Clean up shared memory blocks
        for shm_name, shm in self._shared_memory_blocks.items():
            try:
                shm.close()
                shm.unlink()
            except Exception as e:
                logger.warning(f"Failed to cleanup shared memory {shm_name}: {e}")
        
        self._shared_memory_blocks.clear()
        
        # Close publisher
        if self._publisher is not None:
            self._publisher.close()
            self._publisher = None
            
        logger.debug("Napari streaming backend cleaned up")
    
    def __del__(self):
        """Cleanup on deletion."""
        self.cleanup()
