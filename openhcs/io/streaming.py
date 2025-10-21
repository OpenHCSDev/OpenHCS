"""
Streaming backend interfaces for OpenHCS.

This module provides abstract base classes for streaming data destinations
that send data to external systems without persistent storage capabilities.
"""

import logging
import time
import os
from pathlib import Path
from typing import Any, List, Union
import numpy as np

from openhcs.io.base import DataSink

logger = logging.getLogger(__name__)


class StreamingBackend(DataSink):
    """
    Abstract base class for ZeroMQ-based streaming backends.

    Provides common ZeroMQ publisher management, shared memory handling,
    and component metadata parsing for all streaming backends.

    Subclasses must define abstract class attributes:
    - VIEWER_TYPE: str (e.g., 'napari', 'fiji')
    - HOST_PARAM: str (e.g., 'napari_host', 'fiji_host')
    - PORT_PARAM: str (e.g., 'napari_port', 'fiji_port')
    - SHM_PREFIX: str (e.g., 'napari_', 'fiji_')

    Concrete implementations should use StorageBackendMeta for automatic registration.
    """

    # Abstract class attributes that subclasses must define
    VIEWER_TYPE: str = None
    HOST_PARAM: str = None
    PORT_PARAM: str = None
    SHM_PREFIX: str = None

    def __init__(self):
        """Initialize ZeroMQ and shared memory infrastructure."""
        self._publishers = {}
        self._context = None
        self._shared_memory_blocks = {}

    def _get_publisher(self, host: str, port: int):
        """
        Lazy initialization of ZeroMQ publisher (common for all streaming backends).

        Args:
            host: Host to connect to
            port: Port to connect to

        Returns:
            ZeroMQ publisher socket
        """
        key = f"{host}:{port}"
        if key not in self._publishers:
            try:
                import zmq
                if self._context is None:
                    self._context = zmq.Context()

                publisher = self._context.socket(zmq.PUB)
                publisher.setsockopt(zmq.SNDHWM, 10000)
                publisher.connect(f"tcp://{host}:{port}")
                logger.info(f"{self.VIEWER_TYPE} streaming publisher connected to {host}:{port}")
                time.sleep(0.1)
                self._publishers[key] = publisher

            except ImportError:
                logger.error("ZeroMQ not available - streaming disabled")
                raise RuntimeError("ZeroMQ required for streaming")

        return self._publishers[key]

    def _parse_component_metadata(self, file_path: Union[str, Path], microscope_handler,
                                  step_name: str, step_index: int) -> dict:
        """
        Parse component metadata from filename (common for all streaming backends).

        Args:
            file_path: Path to parse
            microscope_handler: Handler with parser
            step_name: Step name to add as virtual component
            step_index: Step index to add as virtual component

        Returns:
            Component metadata dict with virtual components added
        """
        filename = os.path.basename(str(file_path))
        component_metadata = microscope_handler.parser.parse_filename(filename)
        component_metadata['step_name'] = step_name
        component_metadata['step_index'] = step_index
        source_value = Path(file_path).parent.name
        component_metadata['source'] = source_value
        return component_metadata

    def _detect_data_type(self, data: Any):
        """
        Detect if data is ROI or image (common for all streaming backends).

        Args:
            data: Data to check

        Returns:
            StreamingDataType enum value
        """
        from openhcs.core.roi import ROI
        from openhcs.constants.streaming import StreamingDataType

        is_roi = isinstance(data, list) and len(data) > 0 and isinstance(data[0], ROI)
        return StreamingDataType.SHAPES if is_roi else StreamingDataType.IMAGE

    def _create_shared_memory(self, data: Any, file_path: Union[str, Path]) -> dict:
        """
        Create shared memory for image data (common for all streaming backends).

        Args:
            data: Image data to put in shared memory
            file_path: Path identifier

        Returns:
            Dict with shared memory metadata
        """
        # Convert to numpy
        np_data = data.cpu().numpy() if hasattr(data, 'cpu') else \
                  data.get() if hasattr(data, 'get') else np.asarray(data)

        # Create shared memory
        from multiprocessing import shared_memory, resource_tracker
        shm_name = f"{self.SHM_PREFIX}{id(data)}_{time.time_ns()}"
        shm = shared_memory.SharedMemory(create=True, size=np_data.nbytes, name=shm_name)

        # Unregister from resource tracker - we manage cleanup manually
        # This prevents resource tracker warnings when worker processes exit
        # before the viewer has unlinked the shared memory
        try:
            resource_tracker.unregister(shm._name, "shared_memory")
        except Exception:
            pass  # Ignore errors if already unregistered

        shm_array = np.ndarray(np_data.shape, dtype=np_data.dtype, buffer=shm.buf)
        shm_array[:] = np_data[:]
        self._shared_memory_blocks[shm_name] = shm

        return {
            'path': str(file_path),
            'shape': np_data.shape,
            'dtype': str(np_data.dtype),
            'shm_name': shm_name,
        }

    def _register_with_queue_tracker(self, port: int, image_ids: List[str]) -> None:
        """
        Register sent images with queue tracker (common for all streaming backends).

        Args:
            port: Port number for tracker lookup
            image_ids: List of image IDs to register
        """
        from openhcs.runtime.queue_tracker import GlobalQueueTrackerRegistry
        registry = GlobalQueueTrackerRegistry()
        tracker = registry.get_or_create_tracker(port, self.VIEWER_TYPE)
        for image_id in image_ids:
            tracker.register_sent(image_id)

    def save(self, data: Any, file_path: Union[str, Path], **kwargs) -> None:
        """
        Stream single item (common for all streaming backends).

        Args:
            data: Data to stream
            file_path: Path identifier
            **kwargs: Backend-specific arguments
        """
        if isinstance(data, str):
            return  # Ignore text data
        self.save_batch([data], [file_path], **kwargs)

    def cleanup(self) -> None:
        """
        Clean up shared memory and ZeroMQ resources (common for all streaming backends).
        """
        # Clean up shared memory blocks
        for shm_name, shm in self._shared_memory_blocks.items():
            try:
                shm.close()
                shm.unlink()
            except Exception as e:
                logger.warning(f"Failed to cleanup shared memory {shm_name}: {e}")
        self._shared_memory_blocks.clear()

        # Close publishers
        for key, publisher in self._publishers.items():
            try:
                publisher.close()
            except Exception as e:
                logger.warning(f"Failed to close publisher {key}: {e}")
        self._publishers.clear()

        # Terminate context
        if self._context:
            try:
                self._context.term()
            except Exception as e:
                logger.warning(f"Failed to terminate ZMQ context: {e}")
            self._context = None

        logger.debug(f"{self.VIEWER_TYPE} streaming backend cleaned up")
