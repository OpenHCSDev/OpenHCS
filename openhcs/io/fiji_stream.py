"""
Fiji streaming backend for OpenHCS.

Streams image data to Fiji/ImageJ viewer using ZMQ for IPC.
Follows same architecture as Napari streaming for consistency.
"""

import logging
import time
from pathlib import Path
from typing import Any, Union, List
import os
import numpy as np

from openhcs.io.streaming import StreamingBackend
from openhcs.io.backend_registry import StorageBackendMeta
from openhcs.constants.constants import Backend

logger = logging.getLogger(__name__)


class FijiStreamingBackend(StreamingBackend, metaclass=StorageBackendMeta):
    """Fiji streaming backend with ZMQ publisher pattern (matches Napari architecture)."""

    _backend_type = Backend.FIJI_STREAM.value

    def __init__(self):
        """Initialize Fiji streaming backend with ZMQ publisher pooling."""
        self._publishers = {}
        self._context = None
        self._shared_memory_blocks = {}

    def _get_publisher(self, fiji_host: str, fiji_port: int):
        """Lazy initialization of ZeroMQ publisher for given host:port."""
        key = f"{fiji_host}:{fiji_port}"
        if key not in self._publishers:
            import zmq
            if self._context is None:
                self._context = zmq.Context()

            publisher = self._context.socket(zmq.PUB)
            # Set high water mark to allow more buffering (default is 1000)
            # This prevents blocking when Fiji is slow to process hyperstacks
            publisher.setsockopt(zmq.SNDHWM, 10000)
            publisher.connect(f"tcp://{fiji_host}:{fiji_port}")
            logger.info(f"Fiji streaming publisher connected to {fiji_host}:{fiji_port}")
            time.sleep(0.1)  # Socket ready delay
            self._publishers[key] = publisher

        return self._publishers[key]

    def save(self, data: Any, file_path: Union[str, Path], **kwargs) -> None:
        """Stream single image to Fiji."""
        self.save_batch([data], [file_path], **kwargs)

    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """Stream batch of images to Fiji via ZMQ."""
        if len(data_list) != len(file_paths):
            raise ValueError("data_list and file_paths must have same length")

        # Extract required kwargs
        fiji_host = kwargs.get('fiji_host', 'localhost')
        fiji_port = kwargs['fiji_port']
        publisher = self._get_publisher(fiji_host, fiji_port)
        display_config = kwargs['display_config']
        microscope_handler = kwargs['microscope_handler']
        step_index = kwargs.get('step_index', 0)
        step_name = kwargs.get('step_name', 'unknown_step')

        # Prepare batch messages
        batch_images = []
        for data, file_path in zip(data_list, file_paths):
            # Convert to numpy
            np_data = data.cpu().numpy() if hasattr(data, 'cpu') else \
                      data.get() if hasattr(data, 'get') else np.asarray(data)

            # Create shared memory
            from multiprocessing import shared_memory
            shm_name = f"fiji_{id(data)}_{time.time_ns()}"
            shm = shared_memory.SharedMemory(create=True, size=np_data.nbytes, name=shm_name)
            shm_array = np.ndarray(np_data.shape, dtype=np_data.dtype, buffer=shm.buf)
            shm_array[:] = np_data[:]
            self._shared_memory_blocks[shm_name] = shm

            # Parse component metadata
            filename = os.path.basename(str(file_path))
            component_metadata = microscope_handler.parser.parse_filename(filename)

            batch_images.append({
                'path': str(file_path),
                'shape': np_data.shape,
                'dtype': str(np_data.dtype),
                'shm_name': shm_name,
                'component_metadata': component_metadata,
                'step_index': step_index,
                'step_name': step_name
            })

        # Extract component modes from display config
        from openhcs.constants import VariableComponents
        component_modes = {
            comp.value: display_config.get_dimension_mode(comp).value
            for comp in VariableComponents
        }

        # Send batch message
        message = {
            'type': 'batch',
            'images': batch_images,
            'display_config': {
                'lut': display_config.get_lut_name(),
                'component_modes': component_modes,
                'auto_contrast': display_config.auto_contrast if hasattr(display_config, 'auto_contrast') else True
            },
            'timestamp': time.time()
        }

        # Send non-blocking to prevent hanging if Fiji is slow to process
        import zmq
        try:
            publisher.send_json(message, flags=zmq.NOBLOCK)
            logger.debug(f"Streamed batch of {len(batch_images)} images to Fiji on port {fiji_port}")
        except zmq.Again:
            logger.warning(f"Fiji viewer busy, dropped batch of {len(batch_images)} images (port {fiji_port})")
            # Clean up shared memory for dropped images
            for img in batch_images:
                shm_name = img['shm_name']
                if shm_name in self._shared_memory_blocks:
                    try:
                        shm = self._shared_memory_blocks.pop(shm_name)
                        shm.close()
                        shm.unlink()
                    except Exception as e:
                        logger.warning(f"Failed to cleanup dropped shared memory {shm_name}: {e}")

    def cleanup(self) -> None:
        """Clean up ZMQ resources and shared memory blocks."""
        # Close shared memory blocks
        for shm_name, shm in self._shared_memory_blocks.items():
            try:
                shm.close()
                shm.unlink()
            except Exception as e:
                logger.warning(f"Failed to cleanup shared memory {shm_name}: {e}")
        self._shared_memory_blocks.clear()

        # Close ZMQ publishers
        for key, publisher in self._publishers.items():
            try:
                publisher.close()
            except Exception as e:
                logger.warning(f"Failed to close publisher {key}: {e}")
        self._publishers.clear()

        # Terminate ZMQ context
        if self._context:
            try:
                self._context.term()
            except Exception as e:
                logger.warning(f"Failed to terminate ZMQ context: {e}")
            self._context = None

        logger.debug("Fiji streaming backend cleaned up")
