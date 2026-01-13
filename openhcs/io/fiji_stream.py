"""
Fiji streaming backend for OpenHCS.

Streams image data to Fiji/ImageJ viewer using ZMQ for IPC.
Follows same architecture as Napari streaming for consistency.

SHARED MEMORY OWNERSHIP MODEL:
- Sender (Worker): Creates shared memory, sends reference via ZMQ, closes handle (does NOT unlink)
- Receiver (Fiji Server): Attaches to shared memory, copies data, closes handle, unlinks
- Only receiver calls unlink() to prevent FileNotFoundError
- REQ/REP socket pattern ensures receiver copies data before sender closes handle
"""

import logging
from pathlib import Path
from typing import Any, List, Union

from openhcs.constants.constants import Backend
from openhcs.constants.streaming import StreamingDataType
from openhcs.core.config import TransportMode
from openhcs.io.streaming import StreamingBackend
from openhcs.runtime.roi_converters import FijiROIConverter

logger = logging.getLogger(__name__)


class FijiStreamingBackend(StreamingBackend):
    """Fiji streaming backend with ZMQ publisher pattern (matches Napari architecture)."""
    _backend_type = Backend.FIJI_STREAM.value

    # Configure ABC attributes
    VIEWER_TYPE = 'fiji'
    SHM_PREFIX = 'fiji_'

    # __init__, _get_publisher, save, cleanup now inherited from ABC

    def _prepare_rois_data(self, data: Any, file_path: Union[str, Path]) -> dict:
        """
        Prepare ROIs data for transmission.

        Args:
            data: ROI list
            file_path: Path identifier

        Returns:
            Dict with ROI data
        """
        # Convert ROI objects to bytes, then base64 encode for transmission
        roi_bytes_list = FijiROIConverter.rois_to_imagej_bytes(data)
        rois_encoded = FijiROIConverter.encode_rois_for_transmission(roi_bytes_list)

        return {
            'path': str(file_path),
            'rois': rois_encoded,
        }

    def _prepare_batch_item(self, data: Any, file_path: Union[str, Path], data_type):
        logger.info(f"🔍 FIJI BACKEND: Detected data type: {data_type} for path: {file_path}")
        if data_type == StreamingDataType.SHAPES:
            logger.info(f"🔍 FIJI BACKEND: Preparing ROI data for {file_path}")
            item_data = self._prepare_rois_data(data, file_path)
            data_type_value = "rois"
            logger.info(f"🔍 FIJI BACKEND: ROI data prepared: {len(item_data.get('rois', []))} ROIs")
        else:
            logger.info(f"🔍 FIJI BACKEND: Preparing image data for {file_path}")
            item_data = self._create_shared_memory(data, file_path)
            data_type_value = "image"
        return item_data, data_type_value

    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """Stream batch of images or ROIs to Fiji via ZMQ."""

        logger.info(f"📦 FIJI BACKEND: save_batch called with {len(data_list)} items")

        # Extract kwargs using generic polymorphic names
        host = kwargs.get('host', 'localhost')
        port = kwargs['port']
        transport_mode = kwargs.get('transport_mode', TransportMode.IPC)
        publisher = self._get_publisher(host, port, transport_mode)
        display_config = kwargs['display_config']
        microscope_handler = kwargs['microscope_handler']
        source = kwargs.get('source', 'unknown_source')  # Pre-built source value
        images_dir = kwargs.get('images_dir')  # Source image subdirectory for ROI mapping
        plate_path = kwargs.get('plate_path')
        logger.info(f"🏷️  FIJI BACKEND: plate_path = {plate_path}")
        logger.info(f"🏷️  FIJI BACKEND: microscope_handler = {microscope_handler}")
        display_payload_extra = {
            "lut": display_config.get_lut_name(),
            "auto_contrast": display_config.auto_contrast if hasattr(display_config, "auto_contrast") else True,
        }
        message_extra = {
            "images_dir": images_dir,
        }

        message, batch_images, image_ids = self._build_batch_message(
            data_list,
            file_paths,
            microscope_handler,
            source,
            display_config,
            self._prepare_batch_item,
            plate_path=plate_path,
            component_names_kwargs={"log_prefix": "🏷️  FIJI BACKEND", "verbose": True},
            display_payload_extra=display_payload_extra,
            message_extra=message_extra,
        )

        logger.info(
            "🏷️  FIJI BACKEND: Final component_names_metadata: %s",
            message.get("component_names_metadata", {}),
        )

        for item in batch_images:
            logger.info(f"🔍 FIJI BACKEND: Added {item['data_type']} item to batch")

        # Log batch composition
        data_types = [item['data_type'] for item in batch_images]
        type_counts = {dt: data_types.count(dt) for dt in set(data_types)}
        logger.info(f"📤 FIJI BACKEND: Sending batch message with {len(batch_images)} items to port {port}: {type_counts}")

        # Register sent images with queue tracker BEFORE sending
        # This prevents race condition with IPC mode where acks arrive before registration
        self._register_with_queue_tracker(port, image_ids, transport_mode=transport_mode)

        # Send with REQ socket (BLOCKING - worker waits for Fiji to acknowledge)
        # Worker blocks until Fiji receives, copies data from shared memory, and sends ack
        # This guarantees no messages are lost and shared memory is only closed after Fiji is done
        logger.info(f"📤 FIJI BACKEND: Sending batch of {len(batch_images)} images to Fiji on port {port} (REQ/REP - blocking until ack)")
        publisher.send_json(message)  # Blocking send

        # Wait for acknowledgment from Fiji (REP socket)
        # Fiji will only reply after it has copied all data from shared memory
        ack_response = publisher.recv_json()
        logger.info(f"✅ FIJI BACKEND: Received ack from Fiji: {ack_response.get('status', 'unknown')}")

        # Clean up publisher's handles after successful send
        # Receiver will unlink the shared memory after copying the data
        self._cleanup_shared_memory_blocks(batch_images, unlink=False)

    # cleanup() now inherited from ABC

    def __del__(self):
        """Cleanup on deletion."""
        logger.info("🔥 FIJI __del__ called, about to call cleanup()")
        self.cleanup()
        logger.info("🔥 FIJI __del__ cleanup() returned")
