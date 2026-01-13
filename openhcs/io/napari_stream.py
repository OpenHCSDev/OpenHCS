"""
Napari streaming backend for real-time visualization during processing.

This module provides a storage backend that streams image data to a napari viewer
for real-time visualization during pipeline execution. Uses ZeroMQ for IPC
and shared memory for efficient data transfer.

SHARED MEMORY OWNERSHIP MODEL:
- Sender (Worker): Creates shared memory, sends reference via ZMQ, closes handle (does NOT unlink)
- Receiver (Napari Server): Attaches to shared memory, copies data, closes handle, unlinks
- Only receiver calls unlink() to prevent FileNotFoundError
- PUB/SUB socket pattern is non-blocking; receiver must copy data before sender closes handle
"""

import logging
from pathlib import Path
from typing import Any, List, Union

import zmq

from openhcs.constants.constants import Backend
from openhcs.constants.streaming import StreamingDataType
from openhcs.core.config import TransportMode
from openhcs.io.streaming import StreamingBackend
from openhcs.runtime.roi_converters import NapariROIConverter

logger = logging.getLogger(__name__)


class NapariStreamingBackend(StreamingBackend):
    """Napari streaming backend with automatic registration."""
    _backend_type = Backend.NAPARI_STREAM.value

    # Configure ABC attributes
    VIEWER_TYPE = 'napari'
    SHM_PREFIX = 'napari_'

    # __init__, _get_publisher, save, cleanup now inherited from ABC

    def _prepare_shapes_data(self, data: Any, file_path: Union[str, Path]) -> dict:
        """
        Prepare shapes data for transmission.

        Args:
            data: ROI list
            file_path: Path identifier

        Returns:
            Dict with shapes data
        """
        shapes_data = NapariROIConverter.rois_to_shapes(data)

        return {
            'path': str(file_path),
            'shapes': shapes_data,
        }

    def _prepare_batch_item(self, data: Any, file_path: Union[str, Path], data_type):
        if data_type in (StreamingDataType.SHAPES, StreamingDataType.POINTS):
            item_data = self._prepare_shapes_data(data, file_path)
            data_type_value = data_type.value
        else:
            item_data = self._create_shared_memory(data, file_path)
            data_type_value = data_type.value
        return item_data, data_type_value

    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """
        Stream multiple images or ROIs to napari as a batch.

        Args:
            data_list: List of image data or ROI lists
            file_paths: List of path identifiers
            **kwargs: Additional metadata
        """
        # Extract kwargs using generic polymorphic names
        host = kwargs.get('host', 'localhost')
        port = kwargs['port']
        transport_mode = kwargs.get('transport_mode', TransportMode.IPC)
        publisher = self._get_publisher(host, port, transport_mode)
        display_config = kwargs['display_config']
        microscope_handler = kwargs['microscope_handler']
        source = kwargs.get('source', 'unknown_source')  # Pre-built source value
        plate_path = kwargs.get('plate_path')
        display_payload_extra = {
            "colormap": display_config.get_colormap_name(),
            "variable_size_handling": display_config.variable_size_handling.value
            if hasattr(display_config, "variable_size_handling") and display_config.variable_size_handling
            else None,
        }

        message, batch_images, image_ids = self._build_batch_message(
            data_list,
            file_paths,
            microscope_handler,
            source,
            display_config,
            self._prepare_batch_item,
            plate_path=plate_path,
            display_payload_extra=display_payload_extra,
        )

        # Register sent images with queue tracker BEFORE sending
        # This prevents race condition with IPC mode where acks arrive before registration
        self._register_with_queue_tracker(port, image_ids, transport_mode=transport_mode)

        # Send non-blocking to prevent hanging if Napari is slow to process (matches Fiji pattern)
        send_succeeded = False
        try:
            publisher.send_json(message, flags=zmq.NOBLOCK)
            send_succeeded = True

        except zmq.Again:
            logger.warning(f"Napari viewer busy, dropped batch of {len(batch_images)} images (port {port})")

        except Exception as e:
            logger.error(f"Failed to send batch to Napari on port {port}: {e}", exc_info=True)
            raise  # Re-raise the exception so the pipeline knows it failed

        finally:
            # Unified cleanup: close our handle after successful send, close+unlink after failure
            self._cleanup_shared_memory_blocks(batch_images, unlink=not send_succeeded)

    # cleanup() now inherited from ABC

    def __del__(self):
        """Cleanup on deletion."""
        self.cleanup()
