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
import time
from pathlib import Path
from typing import Any, Union, List
import os
import numpy as np

from openhcs.io.streaming import StreamingBackend
from openhcs.constants.constants import Backend
from openhcs.core.config import TransportMode

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
        from openhcs.runtime.roi_converters import FijiROIConverter

        # Convert ROI objects to bytes, then base64 encode for transmission
        roi_bytes_list = FijiROIConverter.rois_to_imagej_bytes(data)
        rois_encoded = FijiROIConverter.encode_rois_for_transmission(roi_bytes_list)

        return {
            'path': str(file_path),
            'rois': rois_encoded,
        }

    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """Stream batch of images or ROIs to Fiji via ZMQ."""
        from openhcs.constants.streaming import StreamingDataType

        if len(data_list) != len(file_paths):
            raise ValueError("data_list and file_paths must have same length")

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

        # Prepare batch messages
        batch_images = []
        image_ids = []

        for data, file_path in zip(data_list, file_paths):
            # Generate unique ID
            import uuid
            image_id = str(uuid.uuid4())
            image_ids.append(image_id)

            # Detect data type using ABC helper
            data_type = self._detect_data_type(data)
            logger.info(f"🔍 FIJI BACKEND: Detected data type: {data_type} for path: {file_path}")

            # Parse component metadata using ABC helper (ONCE for all types)
            component_metadata = self._parse_component_metadata(
                file_path, microscope_handler, source
            )

            # Prepare data based on type
            if data_type == StreamingDataType.SHAPES:  # ROIs for Fiji
                logger.info(f"🔍 FIJI BACKEND: Preparing ROI data for {file_path}")
                item_data = self._prepare_rois_data(data, file_path)
                data_type_str = 'rois'  # Fiji uses 'rois' not 'shapes'
                logger.info(f"🔍 FIJI BACKEND: ROI data prepared: {len(item_data.get('rois', []))} ROIs")
            else:  # IMAGE
                logger.info(f"🔍 FIJI BACKEND: Preparing image data for {file_path}")
                item_data = self._create_shared_memory(data, file_path)
                data_type_str = 'image'

            # Build batch item
            batch_images.append({
                **item_data,
                'data_type': data_type_str,
                'metadata': component_metadata,
                'image_id': image_id
            })
            logger.info(f"🔍 FIJI BACKEND: Added {data_type_str} item to batch")

        # Extract component modes for ALL components in component_order (including virtual components)
        component_modes = {}
        for comp_name in display_config.COMPONENT_ORDER:
            mode_field = f"{comp_name}_mode"
            if hasattr(display_config, mode_field):
                mode = getattr(display_config, mode_field)
                component_modes[comp_name] = mode.value

        # Try to get component name metadata (channels, wells, etc.) from microscope handler
        # This will be used for dimension labels in Fiji (e.g., "Ch1: DAPI" instead of "Channel 1")
        component_names_metadata = {}
        plate_path = kwargs.get('plate_path')
        logger.info(f"🏷️  FIJI BACKEND: plate_path = {plate_path}")
        logger.info(f"🏷️  FIJI BACKEND: microscope_handler = {microscope_handler}")
        if plate_path and microscope_handler:
            try:
                logger.info(f"🏷️  FIJI BACKEND: Attempting to get component metadata")
                # Get metadata for common components using metadata_handler methods
                for comp_name in ['channel', 'well', 'site']:
                    try:
                        method_name = f'get_{comp_name}_values'
                        if hasattr(microscope_handler.metadata_handler, method_name):
                            method = getattr(microscope_handler.metadata_handler, method_name)
                            metadata = method(plate_path)
                            logger.info(f"🏷️  FIJI BACKEND: Got {comp_name} metadata: {metadata}")
                            if metadata:
                                component_names_metadata[comp_name] = metadata
                        else:
                            logger.info(f"🏷️  FIJI BACKEND: No method {method_name} on metadata_handler")
                    except Exception as e:
                        logger.warning(f"Could not get {comp_name} metadata: {e}", exc_info=True)
                logger.info(f"🏷️  FIJI BACKEND: Final component_names_metadata: {component_names_metadata}")
            except Exception as e:
                logger.warning(f"Could not get component metadata: {e}", exc_info=True)
        else:
            if not plate_path:
                logger.warning(f"🏷️  FIJI BACKEND: No plate_path in kwargs")
            if not microscope_handler:
                logger.warning(f"🏷️  FIJI BACKEND: No microscope_handler")

        # Send batch message
        message = {
            'type': 'batch',
            'images': batch_images,
            'display_config': {
                'lut': display_config.get_lut_name(),
                'component_modes': component_modes,
                'component_order': display_config.COMPONENT_ORDER,
                'auto_contrast': display_config.auto_contrast if hasattr(display_config, 'auto_contrast') else True
            },
            'component_names_metadata': component_names_metadata,  # Add component names for dimension labels
            'images_dir': images_dir,  # Source image subdirectory for ROI->image mapping
            'timestamp': time.time()
        }

        # Log batch composition
        data_types = [item['data_type'] for item in batch_images]
        type_counts = {dt: data_types.count(dt) for dt in set(data_types)}
        logger.info(f"📤 FIJI BACKEND: Sending batch message with {len(batch_images)} items to port {port}: {type_counts}")

        # Register sent images with queue tracker BEFORE sending
        # This prevents race condition with IPC mode where acks arrive before registration
        self._register_with_queue_tracker(port, image_ids)

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
        for img in batch_images:
            shm_name = img.get('shm_name')  # ROI items don't have shm_name
            if shm_name and shm_name in self._shared_memory_blocks:
                try:
                    shm = self._shared_memory_blocks.pop(shm_name)
                    shm.close()  # Close our handle, but don't unlink - receiver will do that
                except Exception as e:
                    logger.warning(f"Failed to close shared memory handle {shm_name}: {e}")

    # cleanup() now inherited from ABC

    def __del__(self):
        """Cleanup on deletion."""
        import logging
        logger = logging.getLogger(__name__)
        logger.info("🔥 FIJI __del__ called, about to call cleanup()")
        self.cleanup()
        logger.info("🔥 FIJI __del__ cleanup() returned")
