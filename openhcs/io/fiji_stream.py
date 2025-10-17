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
        """Stream single image or ROIs to Fiji."""
        from openhcs.core.roi import ROI

        # Streaming backend only handles images and ROIs, not text data
        if isinstance(data, str):
            # Silently ignore text data (JSON, CSV, etc.) - streaming backends don't handle this
            return

        # Explicit type dispatch for ROI data
        if isinstance(data, list) and len(data) > 0 and isinstance(data[0], ROI):
            # ROI data - stream as ROIs
            images_dir = kwargs.pop('images_dir', None)
            self._save_rois(data, Path(file_path), images_dir=images_dir, **kwargs)
            return

        # Image data - stream as image
        self.save_batch([data], [file_path], **kwargs)

    def save_batch(self, data_list: List[Any], file_paths: List[Union[str, Path]], **kwargs) -> None:
        """Stream batch of images to Fiji via ZMQ."""
        if len(data_list) != len(file_paths):
            raise ValueError("data_list and file_paths must have same length")

        logger.info(f"📦 FIJI BACKEND: save_batch called with {len(data_list)} images")

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
        image_ids = []  # Track image IDs for queue tracker registration

        for data, file_path in zip(data_list, file_paths):
            # Generate unique ID for this image (for acknowledgment tracking)
            import uuid
            image_id = str(uuid.uuid4())
            image_ids.append(image_id)

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

            # Parse component metadata from filename
            filename = os.path.basename(str(file_path))
            component_metadata = microscope_handler.parser.parse_filename(filename)

            # Add virtual components
            from pathlib import Path
            component_metadata['step_name'] = step_name
            component_metadata['step_index'] = step_index
            component_metadata['source'] = Path(file_path).parent.name

            batch_images.append({
                'path': str(file_path),
                'shape': np_data.shape,
                'dtype': str(np_data.dtype),
                'shm_name': shm_name,
                'component_metadata': component_metadata,
                'image_id': image_id  # Add image ID for acknowledgment tracking
            })

        # Extract component modes for ALL components in component_order (including virtual components)
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
                'lut': display_config.get_lut_name(),
                'component_modes': component_modes,
                'component_order': display_config.COMPONENT_ORDER,
                'auto_contrast': display_config.auto_contrast if hasattr(display_config, 'auto_contrast') else True
            },
            'timestamp': time.time()
        }

        logger.info(f"📤 FIJI BACKEND: Sending batch message with {len(batch_images)} images to port {fiji_port}")

        # Send non-blocking to prevent hanging if Fiji is slow to process
        import zmq
        try:
            publisher.send_json(message, flags=zmq.NOBLOCK)
            logger.info(f"✅ FIJI BACKEND: Sent batch of {len(batch_images)} images to Fiji on port {fiji_port}")

            # Register sent images with queue tracker for acknowledgment tracking
            from openhcs.runtime.queue_tracker import GlobalQueueTrackerRegistry
            registry = GlobalQueueTrackerRegistry()
            tracker = registry.get_or_create_tracker(fiji_port, 'fiji')
            for image_id in image_ids:
                tracker.register_sent(image_id)

            # Clean up publisher's handles after successful send
            # Receiver will unlink the shared memory after copying the data
            for img in batch_images:
                shm_name = img['shm_name']
                if shm_name in self._shared_memory_blocks:
                    try:
                        shm = self._shared_memory_blocks.pop(shm_name)
                        shm.close()  # Close our handle, but don't unlink - receiver will do that
                    except Exception as e:
                        logger.warning(f"Failed to close shared memory handle {shm_name}: {e}")

        except zmq.Again:
            logger.warning(f"Fiji viewer busy, dropped batch of {len(batch_images)} images (port {fiji_port})")
            # Clean up shared memory for dropped images (both close and unlink since receiver never got them)
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

    def _save_rois(self, rois: List, output_path: Path, images_dir: str = None, **kwargs) -> str:
        """Stream ROIs to Fiji ROI Manager.

        Args:
            rois: List of ROI objects
            output_path: Output_path (used to extract metadata, not for actual saving)
            images_dir: Images directory path (unused for fiji streaming)
            **kwargs: Must contain fiji_port

        Returns:
            String describing where ROIs were sent
        """
        from openhcs.core.roi import PolygonShape, EllipseShape, PointShape
        import base64

        try:
            fiji_host = kwargs.get('fiji_host', 'localhost')
            fiji_port = kwargs['fiji_port']
            publisher = self._get_publisher(fiji_host, fiji_port)
        except KeyError:
            raise ValueError("fiji_port required for streaming ROIs to Fiji")

        # Convert ROIs to ImageJ ROI format
        try:
            from roifile import ImagejRoi
        except ImportError:
            logger.error("roifile library required for Fiji ROI streaming")
            raise RuntimeError("roifile library not available")

        # Extract descriptive prefix from output_path (e.g., "A01_w1_segmentation_masks_step7_rois.json" -> "A01_w1_segmentation_masks_step7_rois")
        roi_prefix = output_path.stem  # Remove .json extension

        roi_bytes_list = []

        for roi in rois:
            for shape in roi.shapes:
                if isinstance(shape, PolygonShape):
                    # Convert polygon to ImageJ ROI
                    # roifile expects (x, y) coordinates, but we have (y, x)
                    coords_xy = shape.coordinates[:, [1, 0]]  # Swap columns
                    ij_roi = ImagejRoi.frompoints(coords_xy)

                    # Set ROI name with descriptive prefix
                    if 'label' in roi.metadata:
                        ij_roi.name = f"{roi_prefix}_ROI_{roi.metadata['label']}"
                    else:
                        ij_roi.name = f"{roi_prefix}_ROI"

                    roi_bytes_list.append(ij_roi.tobytes())

                elif isinstance(shape, EllipseShape):
                    # ImageJ ellipse ROI
                    # Create as oval using bounding box
                    left = shape.center_x - shape.radius_x
                    top = shape.center_y - shape.radius_y
                    width = 2 * shape.radius_x
                    height = 2 * shape.radius_y

                    ij_roi = ImagejRoi.fromroi(
                        roitype=ImagejRoi.OVAL,
                        left=left,
                        top=top,
                        right=left + width,
                        bottom=top + height
                    )

                    if 'label' in roi.metadata:
                        ij_roi.name = f"{roi_prefix}_ROI_{roi.metadata['label']}"
                    else:
                        ij_roi.name = f"{roi_prefix}_ROI"

                    roi_bytes_list.append(ij_roi.tobytes())

                elif isinstance(shape, PointShape):
                    # ImageJ point ROI
                    ij_roi = ImagejRoi.frompoints(np.array([[shape.x, shape.y]]))

                    if 'label' in roi.metadata:
                        ij_roi.name = f"{roi_prefix}_ROI_{roi.metadata['label']}"
                    else:
                        ij_roi.name = f"{roi_prefix}_ROI"

                    roi_bytes_list.append(ij_roi.tobytes())

        # Encode ROI bytes as base64 for JSON transmission
        encoded_rois = [base64.b64encode(roi_bytes).decode('utf-8') for roi_bytes in roi_bytes_list]

        # Send ROIs message
        message = {
            'type': 'rois',
            'rois': encoded_rois,
            'timestamp': time.time()
        }

        import zmq
        try:
            publisher.send_json(message, flags=zmq.NOBLOCK)
            result_msg = f"Streamed {len(rois)} ROIs to Fiji (port {fiji_port})"
            logger.info(result_msg)
            return result_msg
        except zmq.Again:
            logger.warning(f"Fiji viewer busy, dropped {len(rois)} ROIs (port {fiji_port})")
            return f"Failed to stream ROIs (Fiji busy)"
