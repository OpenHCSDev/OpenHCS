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
import time
from pathlib import Path
from typing import Any, List, Union
import os

from openhcs.core.config import TransportMode

import numpy as np

from openhcs.io.streaming import StreamingBackend
from openhcs.constants.constants import Backend

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

        # Extract kwargs using generic polymorphic names
        host = kwargs.get('host', 'localhost')
        port = kwargs['port']
        transport_mode = kwargs.get('transport_mode', TransportMode.IPC)
        publisher = self._get_publisher(host, port, transport_mode)
        display_config = kwargs['display_config']
        microscope_handler = kwargs['microscope_handler']
        source = kwargs.get('source', 'unknown_source')  # Pre-built source value

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

            # Parse component metadata using ABC helper (ONCE for all types)
            component_metadata = self._parse_component_metadata(
                file_path, microscope_handler, source
            )

            # Prepare data based on type
            if data_type == StreamingDataType.SHAPES or data_type == StreamingDataType.POINTS:
                # Both shapes and points use the same converter (it marks them appropriately)
                item_data = self._prepare_shapes_data(data, file_path)
            else:  # IMAGE
                item_data = self._create_shared_memory(data, file_path)

            # Build batch item
            batch_images.append({
                **item_data,
                'data_type': data_type.value,
                'metadata': component_metadata,
                'image_id': image_id
            })

        # Build component modes for ALL components in component_order (including virtual components)
        component_modes = {}
        for comp_name in display_config.COMPONENT_ORDER:
            mode_field = f"{comp_name}_mode"
            if hasattr(display_config, mode_field):
                mode = getattr(display_config, mode_field)
                component_modes[comp_name] = mode.value

        # Try to get component name metadata (channels, wells, etc.) from microscope handler
        # This will be used for dimension labels in napari (e.g., "Ch1: DAPI" instead of "Channel 1")
        component_names_metadata = {}
        plate_path = kwargs.get('plate_path')
        if plate_path and microscope_handler:
            try:
                # Get metadata for common components using metadata_handler methods
                for comp_name in ['channel', 'well', 'site']:
                    try:
                        method_name = f'get_{comp_name}_values'
                        if hasattr(microscope_handler.metadata_handler, method_name):
                            method = getattr(microscope_handler.metadata_handler, method_name)
                            metadata = method(plate_path)
                            if metadata:
                                component_names_metadata[comp_name] = metadata
                    except Exception as e:
                        logger.debug(f"Could not get {comp_name} metadata: {e}")
            except Exception as e:
                logger.debug(f"Could not get component metadata: {e}")
        
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
            'component_names_metadata': component_names_metadata,  # Add component names for dimension labels
            'timestamp': time.time()
        }

        # Register sent images with queue tracker BEFORE sending
        # This prevents race condition with IPC mode where acks arrive before registration
        self._register_with_queue_tracker(port, image_ids)

        # Send non-blocking to prevent hanging if Napari is slow to process (matches Fiji pattern)
        import zmq
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
            self._cleanup_shared_memory(batch_images, unlink=not send_succeeded)

    def _cleanup_shared_memory(self, batch_images, unlink=False):
        """Clean up shared memory blocks for a batch of images.

        Args:
            batch_images: List of image dictionaries with optional 'shm_name' keys
            unlink: If True, both close and unlink. If False, only close (viewer will unlink)
        """
        for img in batch_images:
            shm_name = img.get('shm_name')  # ROI items don't have shm_name
            if shm_name and shm_name in self._shared_memory_blocks:
                try:
                    shm = self._shared_memory_blocks.pop(shm_name)
                    shm.close()
                    if unlink:
                        shm.unlink()
                except Exception as e:
                    logger.warning(f"Failed to cleanup shared memory {shm_name}: {e}")

    # cleanup() now inherited from ABC

    def __del__(self):
        """Cleanup on deletion."""
        self.cleanup()
