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
from openhcs.runtime.zmq_base import get_zmq_transport_url
from openhcs.core.config import TransportMode

logger = logging.getLogger(__name__)


class StreamingBackend(DataSink):
    """
    Abstract base class for ZeroMQ-based streaming backends.

    Provides common ZeroMQ publisher management, shared memory handling,
    and component metadata parsing for all streaming backends.

    Subclasses must define abstract class attributes:
    - VIEWER_TYPE: str (e.g., 'napari', 'fiji')
    - SHM_PREFIX: str (e.g., 'napari_', 'fiji_')
    - _backend_type: str (e.g., 'napari_stream', 'fiji_stream')

    All streaming backends use generic 'host' and 'port' kwargs for polymorphism.

    Inherits from DataSink (which inherits from BackendBase for automatic registration).
    """

    # Abstract class attributes that subclasses must define
    VIEWER_TYPE: str = None
    SHM_PREFIX: str = None

    @property
    def requires_filesystem_validation(self) -> bool:
        """Streaming backends don't require filesystem validation."""
        return False

    def __init__(self):
        """Initialize ZeroMQ and shared memory infrastructure."""
        self._publishers = {}
        self._context = None
        self._shared_memory_blocks = {}

    def _get_publisher(self, host: str, port: int, transport_mode: TransportMode = TransportMode.IPC):
        """
        Lazy initialization of ZeroMQ publisher (common for all streaming backends).

        Uses REQ socket for Fiji (synchronous request/reply with blocking)
        and PUB socket for Napari (broadcast pattern).

        Args:
            host: Host to connect to (ignored for IPC mode)
            port: Port to connect to
            transport_mode: IPC or TCP transport

        Returns:
            ZeroMQ publisher socket
        """
        # Generate transport URL using centralized function
        url = get_zmq_transport_url(port, transport_mode, host)

        key = url  # Use URL as key instead of host:port
        if key not in self._publishers:
            try:
                import zmq
                if self._context is None:
                    self._context = zmq.Context()

                # Use REQ socket for Fiji (synchronous request/reply - worker blocks until Fiji acks)
                # Use PUB socket for Napari (broadcast pattern)
                socket_type = zmq.REQ if self.VIEWER_TYPE == 'fiji' else zmq.PUB
                publisher = self._context.socket(socket_type)

                if socket_type == zmq.PUB:
                    publisher.setsockopt(zmq.SNDHWM, 100000)  # Only for PUB sockets

                publisher.connect(url)
                socket_name = "REQ" if socket_type == zmq.REQ else "PUB"
                logger.info(f"{self.VIEWER_TYPE} streaming {socket_name} socket connected to {url}")
                time.sleep(0.1)
                self._publishers[key] = publisher

            except ImportError:
                logger.error("ZeroMQ not available - streaming disabled")
                raise RuntimeError("ZeroMQ required for streaming")

        return self._publishers[key]

    def _parse_component_metadata(self, file_path: Union[str, Path], microscope_handler,
                                  source: str) -> dict:
        """
        Parse component metadata from filename (common for all streaming backends).

        Args:
            file_path: Path to parse
            microscope_handler: Handler with parser
            source: Pre-built source value (step_name during execution, subdir when loading from disk)

        Returns:
            Component metadata dict with source added
        """
        filename = os.path.basename(str(file_path))
        component_metadata = microscope_handler.parser.parse_filename(filename)

        # Add pre-built source value directly
        component_metadata['source'] = source

        return component_metadata

    def _detect_data_type(self, data: Any):
        """
        Detect if data is ROI (shapes/points) or image (common for all streaming backends).

        Args:
            data: Data to check

        Returns:
            StreamingDataType enum value (IMAGE, SHAPES, or POINTS)
        """
        from openhcs.core.roi import ROI, PointShape
        from openhcs.constants.streaming import StreamingDataType

        is_roi = isinstance(data, list) and len(data) > 0 and isinstance(data[0], ROI)
        
        if not is_roi:
            return StreamingDataType.IMAGE
        
        # Check if all ROIs contain only PointShape objects (for points layer)
        all_points = all(
            roi.shapes and all(isinstance(shape, PointShape) for shape in roi.shapes)
            for roi in data
        )
        
        return StreamingDataType.POINTS if all_points else StreamingDataType.SHAPES

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

        # Create shared memory with hash-based naming to avoid "File name too long" errors
        # Hash the timestamp and object ID to create a short, unique name
        from multiprocessing import shared_memory, resource_tracker
        import hashlib
        timestamp = time.time_ns()
        obj_id = id(data)
        hash_input = f"{obj_id}_{timestamp}"
        hash_suffix = hashlib.md5(hash_input.encode()).hexdigest()[:8]
        shm_name = f"{self.SHM_PREFIX}{hash_suffix}"
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
        logger.info(f"🔥 CLEANUP: Starting cleanup for {self.VIEWER_TYPE}")

        # Clean up shared memory blocks
        logger.info(f"🔥 CLEANUP: About to clean {len(self._shared_memory_blocks)} shared memory blocks")
        for shm_name, shm in self._shared_memory_blocks.items():
            try:
                shm.close()
                shm.unlink()
            except Exception as e:
                logger.warning(f"Failed to cleanup shared memory {shm_name}: {e}")
        self._shared_memory_blocks.clear()
        logger.info(f"🔥 CLEANUP: Shared memory cleanup complete")

        # Close publishers
        logger.info(f"🔥 CLEANUP: About to close {len(self._publishers)} publishers")
        for key, publisher in self._publishers.items():
            try:
                logger.info(f"🔥 CLEANUP: Closing publisher {key}")
                publisher.close()
                logger.info(f"🔥 CLEANUP: Publisher {key} closed")
            except Exception as e:
                logger.warning(f"Failed to close publisher {key}: {e}")
        self._publishers.clear()
        logger.info(f"🔥 CLEANUP: Publishers cleanup complete")

        # Terminate context
        if self._context:
            try:
                logger.info(f"🔥 CLEANUP: About to terminate ZMQ context")
                self._context.term()
                logger.info(f"🔥 CLEANUP: ZMQ context terminated")
            except Exception as e:
                logger.warning(f"Failed to terminate ZMQ context: {e}")
            self._context = None

        logger.info(f"🔥 CLEANUP: {self.VIEWER_TYPE} streaming backend cleaned up")
