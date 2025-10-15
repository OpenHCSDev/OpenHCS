"""
Napari streaming backend for real-time visualization during processing.

This module provides a storage backend that streams image data to a napari viewer
for real-time visualization during pipeline execution. Uses ZeroMQ for IPC
and shared memory for efficient data transfer.
"""

import logging
import time
from pathlib import Path
from typing import Any, List, Union
import os

import numpy as np

from openhcs.io.streaming import StreamingBackend
from openhcs.io.backend_registry import StorageBackendMeta
from openhcs.constants.constants import Backend

logger = logging.getLogger(__name__)


class NapariStreamingBackend(StreamingBackend, metaclass=StorageBackendMeta):
    """Napari streaming backend with automatic metaclass registration."""

    # Backend type from enum for registration
    _backend_type = Backend.NAPARI_STREAM.value
    """
    Napari streaming backend for real-time visualization.

    Streams image data to napari viewer using ZeroMQ.
    Connects to existing NapariStreamVisualizer process.
    Inherits from StreamingBackend - no file system operations.
    """

    def __init__(self):
        """Initialize the napari streaming backend."""
        self._publishers = {}  # Dictionary of publishers keyed by port
        self._context = None
        self._shared_memory_blocks = {}

    def _get_publisher(self, napari_host: str, napari_port: int):
        """Lazy initialization of ZeroMQ publisher for the given host:port."""
        key = f"{napari_host}:{napari_port}"
        if key not in self._publishers:
            try:
                import zmq
                if self._context is None:
                    self._context = zmq.Context()

                publisher = self._context.socket(zmq.PUB)
                # Set high water mark to allow more buffering (default is 1000)
                # This prevents message loss during viewer startup (slow joiner problem)
                publisher.setsockopt(zmq.SNDHWM, 10000)
                publisher.connect(f"tcp://{napari_host}:{napari_port}")
                logger.info(f"Napari streaming publisher connected to {napari_host}:{napari_port}")

                # Small delay to ensure socket is ready
                time.sleep(0.1)

                self._publishers[key] = publisher

            except ImportError:
                logger.error("ZeroMQ not available - napari streaming disabled")
                raise RuntimeError("ZeroMQ required for napari streaming")

        return self._publishers[key]



    def save(self, data: Any, file_path: Union[str, Path], **kwargs) -> None:
        """Stream single image to napari."""
        self.save_batch([data], [file_path], **kwargs)

    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """
        Stream multiple images to napari as a batch.

        Args:
            data_list: List of image data
            file_paths: List of path identifiers
            **kwargs: Additional metadata
        """


        if len(data_list) != len(file_paths):
            raise ValueError("data_list and file_paths must have the same length")

        try:
            napari_host = kwargs.get('napari_host', 'localhost')  # Default to localhost for backward compatibility
            napari_port = kwargs['napari_port']
            publisher = self._get_publisher(napari_host, napari_port)
            display_config = kwargs['display_config']
            microscope_handler = kwargs['microscope_handler']
            step_index = kwargs.get('step_index', 0)
            step_name = kwargs.get('step_name', 'unknown_step')
        except KeyError as e:
            raise

        # Prepare batch of images
        batch_images = []
        image_ids = []  # Track image IDs for queue tracker registration

        for data, file_path in zip(data_list, file_paths):
            # Generate unique ID for this image (for acknowledgment tracking)
            import uuid
            image_id = str(uuid.uuid4())
            image_ids.append(image_id)

            # Convert to numpy
            if hasattr(data, 'cpu'):
                np_data = data.cpu().numpy()
            elif hasattr(data, 'get'):
                np_data = data.get()
            else:
                np_data = np.asarray(data)

            # Create shared memory
            from multiprocessing import shared_memory
            shm_name = f"napari_{id(data)}_{time.time_ns()}"
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
                'step_name': step_name,
                'image_id': image_id  # Add image ID for acknowledgment tracking
            })

        # Build component modes for all dimensions (including multiprocessing axis)
        from openhcs.constants import AllComponents
        component_modes = {}
        for component in AllComponents:
            field_name = f"{component.value}_mode"
            mode = getattr(display_config, field_name)
            component_modes[component.value] = mode.value

        # Send batch message
        message = {
            'type': 'batch',
            'images': batch_images,
            'display_config': {
                'colormap': display_config.get_colormap_name(),
                'component_modes': component_modes,
                'variable_size_handling': display_config.variable_size_handling.value if hasattr(display_config, 'variable_size_handling') and display_config.variable_size_handling else None
            },
            'timestamp': time.time()
        }

        publisher.send_json(message)

        # Register sent images with queue tracker for acknowledgment tracking
        from openhcs.runtime.queue_tracker import GlobalQueueTrackerRegistry
        registry = GlobalQueueTrackerRegistry()
        tracker = registry.get_or_create_tracker(napari_port, 'napari')
        for image_id in image_ids:
            tracker.register_sent(image_id)

    # REMOVED: All file system methods (load, load_batch, exists, list_files, delete, etc.)
    # These are no longer inherited - clean interface!

    def cleanup_connections(self) -> None:
        """Clean up ZeroMQ connections without affecting shared memory or napari window."""
        # Close all publishers
        for port, publisher in self._publishers.items():
            try:
                publisher.close()
                logger.debug(f"Closed publisher for port {port}")
            except Exception as e:
                logger.warning(f"Failed to close publisher for port {port}: {e}")

        self._publishers.clear()

        if self._context is not None:
            self._context.term()
            self._context = None

        logger.debug("Napari streaming connections cleaned up")

    def cleanup(self) -> None:
        """Clean up shared memory blocks and close publisher.

        Note: This does NOT close the napari window - it should remain open
        for future test executions and user interaction.
        """
        # Clean up shared memory blocks
        for shm_name, shm in self._shared_memory_blocks.items():
            try:
                shm.close()
                shm.unlink()
            except Exception as e:
                logger.warning(f"Failed to cleanup shared memory {shm_name}: {e}")

        self._shared_memory_blocks.clear()

        # Clean up connections
        self.cleanup_connections()

        logger.debug("Napari streaming backend cleaned up (napari window remains open)")

    def __del__(self):
        """Cleanup on deletion."""
        self.cleanup()
