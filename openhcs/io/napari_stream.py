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

    # Configure ABC attributes
    VIEWER_TYPE = 'napari'
    HOST_PARAM = 'napari_host'
    PORT_PARAM = 'napari_port'
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
        from openhcs.runtime.roi_converters import NapariROIConverter
        shapes_data = NapariROIConverter.rois_to_shapes(data)

        return {
            'path': str(file_path),
            'shapes': shapes_data,
        }

    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """
        Stream multiple images or ROIs to napari as a batch.

        Args:
            data_list: List of image data or ROI lists
            file_paths: List of path identifiers
            **kwargs: Additional metadata
        """
        from openhcs.constants.streaming import StreamingDataType

        if len(data_list) != len(file_paths):
            raise ValueError("data_list and file_paths must have the same length")

        logger.info(f"📦 NAPARI BACKEND: save_batch called with {len(data_list)} items")

        # Extract kwargs using class attributes
        host = kwargs.get(self.HOST_PARAM, 'localhost')
        port = kwargs[self.PORT_PARAM]
        publisher = self._get_publisher(host, port)
        display_config = kwargs['display_config']
        microscope_handler = kwargs['microscope_handler']
        source = kwargs.get('source', 'unknown_source')  # Pre-built source value

        logger.info(f"🔍 NAPARI BACKEND: Streaming to port {port}, source={source}")

        # Prepare batch of images/ROIs
        batch_images = []
        image_ids = []

        for data, file_path in zip(data_list, file_paths):
            # Generate unique ID
            import uuid
            image_id = str(uuid.uuid4())
            image_ids.append(image_id)

            # Detect data type using ABC helper
            data_type = self._detect_data_type(data)
            logger.info(f"🔍 NAPARI BACKEND: Detected data type: {data_type} for path: {file_path}")

            # Parse component metadata using ABC helper (ONCE for all types)
            component_metadata = self._parse_component_metadata(
                file_path, microscope_handler, source
            )

            # Prepare data based on type
            if data_type == StreamingDataType.SHAPES:
                logger.info(f"🔍 NAPARI BACKEND: Preparing shapes data for {file_path}")
                item_data = self._prepare_shapes_data(data, file_path)
                logger.info(f"🔍 NAPARI BACKEND: Shapes data prepared: {len(item_data.get('shapes', []))} shapes")
            else:  # IMAGE
                logger.info(f"🔍 NAPARI BACKEND: Preparing image data for {file_path}")
                item_data = self._create_shared_memory(data, file_path)

            # Build batch item
            batch_images.append({
                **item_data,
                'data_type': data_type.value,
                'metadata': component_metadata,
                'image_id': image_id
            })
            logger.info(f"🔍 NAPARI BACKEND: Added {data_type.value} item to batch")

        # Build component modes for ALL components in component_order (including virtual components)
        component_modes = {}
        for comp_name in display_config.COMPONENT_ORDER:
            mode_field = f"{comp_name}_mode"
            if hasattr(display_config, mode_field):
                mode = getattr(display_config, mode_field)
                component_modes[comp_name] = mode.value

        # Send batch message
        message = {
            'type': 'batch',
            'images': batch_images,
            'display_config': {
                'colormap': display_config.get_colormap_name(),
                'component_modes': component_modes,
                'component_order': display_config.COMPONENT_ORDER,
                'variable_size_handling': display_config.variable_size_handling.value if hasattr(display_config, 'variable_size_handling') and display_config.variable_size_handling else None
            },
            'timestamp': time.time()
        }

        # Log batch composition
        data_types = [item['data_type'] for item in batch_images]
        type_counts = {dt: data_types.count(dt) for dt in set(data_types)}
        logger.info(f"📤 NAPARI BACKEND: Sending batch message with {len(batch_images)} items to port {port}: {type_counts}")

        # Send non-blocking to prevent hanging if Napari is slow to process (matches Fiji pattern)
        import zmq
        try:
            publisher.send_json(message, flags=zmq.NOBLOCK)
            logger.info(f"✅ NAPARI BACKEND: Sent batch of {len(batch_images)} images to Napari on port {port}")

            # Register sent images with queue tracker using ABC helper
            self._register_with_queue_tracker(port, image_ids)
            logger.info(f"📊 NAPARI BACKEND: Registered {len(image_ids)} image IDs with queue tracker for port {port}")

            # Clean up backend's shared memory handles after successful send (like Fiji pattern)
            # Viewer will unlink after copying the data
            for img in batch_images:
                shm_name = img.get('shm_name')  # ROI items don't have shm_name
                if shm_name and shm_name in self._shared_memory_blocks:
                    try:
                        shm = self._shared_memory_blocks.pop(shm_name)
                        shm.close()  # Close our handle, but don't unlink - viewer will do that
                    except Exception as e:
                        logger.warning(f"Failed to close shared memory handle {shm_name}: {e}")

        except zmq.Again:
            logger.warning(f"Napari viewer busy, dropped batch of {len(batch_images)} images (port {port})")
            # Clean up shared memory for dropped images (both close and unlink since receiver never got them)
            for img in batch_images:
                shm_name = img.get('shm_name')  # ROI items don't have shm_name
                if shm_name and shm_name in self._shared_memory_blocks:
                    try:
                        shm = self._shared_memory_blocks.pop(shm_name)
                        shm.close()
                        shm.unlink()
                    except Exception as e:
                        logger.warning(f"Failed to cleanup dropped shared memory {shm_name}: {e}")

        except Exception as e:
            logger.error(f"❌ NAPARI BACKEND: Failed to send batch to Napari on port {port}: {e}", exc_info=True)
            # Clean up shared memory for failed send (both close and unlink since receiver never got them)
            for img in batch_images:
                shm_name = img.get('shm_name')  # ROI items don't have shm_name
                if shm_name and shm_name in self._shared_memory_blocks:
                    try:
                        shm = self._shared_memory_blocks.pop(shm_name)
                        shm.close()
                        shm.unlink()
                    except Exception as cleanup_error:
                        logger.warning(f"Failed to cleanup shared memory after error {shm_name}: {cleanup_error}")
            raise  # Re-raise the exception so the pipeline knows it failed

    # cleanup() now inherited from ABC

    def __del__(self):
        """Cleanup on deletion."""
        import logging
        logger = logging.getLogger(__name__)
        logger.info("🔥 NAPARI __del__ called, about to call cleanup()")
        self.cleanup()
        logger.info("🔥 NAPARI __del__ cleanup() returned")
