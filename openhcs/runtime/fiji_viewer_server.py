"""
Fiji viewer server for OpenHCS.

ZMQ-based server that receives images from FijiStreamingBackend and displays them
via PyImageJ. Inherits from ZMQServer ABC for ping/pong handshake and dual-channel pattern.
"""

import logging
import time
from typing import Dict, Any, List

from openhcs.runtime.zmq_base import ZMQServer, SHARED_ACK_PORT
from openhcs.runtime.zmq_messages import ImageAck

logger = logging.getLogger(__name__)


class FijiViewerServer(ZMQServer):
    """
    ZMQ server for Fiji viewer that receives images from clients.
    
    Inherits from ZMQServer ABC to get ping/pong, port management, etc.
    Uses SUB socket to receive images from pipeline clients.
    Displays images via PyImageJ.
    """
    
    def __init__(self, port: int, viewer_title: str, display_config, log_file_path: str = None):
        """
        Initialize Fiji viewer server.

        Args:
            port: Data port for receiving images (control port will be port + 1000)
            viewer_title: Title for the Fiji viewer window
            display_config: FijiDisplayConfig with LUT, dimension modes, etc.
            log_file_path: Path to log file (for client discovery)
        """
        import zmq

        # Initialize with SUB socket for receiving images
        super().__init__(port, host='*', log_file_path=log_file_path, data_socket_type=zmq.SUB)

        self.viewer_title = viewer_title
        self.display_config = display_config
        self.ij = None  # PyImageJ instance
        self.hyperstacks = {}  # Track hyperstacks by (step_name, well) key
        self.hyperstack_metadata = {}  # Track original image metadata for each hyperstack
        self._shutdown_requested = False

        # Create PUSH socket for sending acknowledgments to shared ack port
        self.ack_socket = None
        self._setup_ack_socket()

    def _setup_ack_socket(self):
        """Setup PUSH socket for sending acknowledgments."""
        import zmq
        try:
            context = zmq.Context.instance()
            self.ack_socket = context.socket(zmq.PUSH)
            self.ack_socket.connect(f"tcp://localhost:{SHARED_ACK_PORT}")
            logger.info(f"🔬 FIJI SERVER: Connected ack socket to port {SHARED_ACK_PORT}")
        except Exception as e:
            logger.warning(f"🔬 FIJI SERVER: Failed to setup ack socket: {e}")
            self.ack_socket = None

    def _send_ack(self, image_id: str, status: str = 'success', error: str = None):
        """Send acknowledgment that an image was processed.

        Args:
            image_id: UUID of the processed image
            status: 'success' or 'error'
            error: Error message if status='error'
        """
        if not self.ack_socket:
            return

        try:
            ack = ImageAck(
                image_id=image_id,
                viewer_port=self.port,
                viewer_type='fiji',
                status=status,
                timestamp=time.time(),
                error=error
            )
            self.ack_socket.send_json(ack.to_dict())
            logger.debug(f"🔬 FIJI SERVER: Sent ack for image {image_id}")
        except Exception as e:
            logger.warning(f"🔬 FIJI SERVER: Failed to send ack for {image_id}: {e}")
    
    def start(self):
        """Start server and initialize PyImageJ."""
        super().start()

        # Initialize PyImageJ in this process
        try:
            import imagej
            logger.info("🔬 FIJI SERVER: Initializing PyImageJ...")
            self.ij = imagej.init(mode='interactive')

            # Show Fiji UI so users can interact with images and menus
            self.ij.ui().showUI()
            logger.info("🔬 FIJI SERVER: PyImageJ initialized and UI shown")
        except ImportError:
            raise ImportError("PyImageJ not available. Install with: pip install 'openhcs[viz]'")
    
    def handle_control_message(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle control messages beyond ping/pong.

        Supported message types:
        - shutdown: Graceful shutdown (closes viewer)
        - force_shutdown: Force shutdown (same as shutdown for Fiji)
        """
        msg_type = message.get('type')

        if msg_type == 'shutdown' or msg_type == 'force_shutdown':
            logger.info(f"🔬 FIJI SERVER: {msg_type} requested, will close after sending acknowledgment")
            # Set shutdown flag but don't call stop() yet - let the response be sent first
            self._shutdown_requested = True
            return {
                'type': 'shutdown_ack',
                'status': 'success',
                'message': 'Fiji viewer shutting down'
            }

        return {'status': 'ok'}
    
    def handle_data_message(self, message: Dict[str, Any]):
        """Handle incoming image data - called by process_messages()."""
        pass
    
    def process_image_message(self, message: bytes):
        """
        Process incoming image data message.

        Builds 5D hyperstacks organized by (step_name, well).
        Each hyperstack has dimensions organized as: channels, slices (z), frames (time).
        Sites are treated as additional channels.

        Args:
            message: Raw ZMQ message containing image data
        """
        import json

        # Parse JSON message
        data = json.loads(message.decode('utf-8'))

        # Check if this is a batch message
        if data.get('type') == 'batch':
            images = data.get('images', [])
            display_config_dict = data.get('display_config', {})

            logger.info(f"📨 FIJI SERVER: Received batch message with {len(images)} images")

            if not images:
                return

            # Get step name from first image
            step_name = images[0].get('step_name', 'unknown_step')

            # Process ALL images together - let _add_images_to_hyperstack group by window
            # Don't group by well here - that causes sequential processing!
            self._add_images_to_hyperstack(step_name, images, display_config_dict)
        else:
            # Single image message (fallback)
            self._add_images_to_hyperstack(
                data.get('step_name', 'unknown_step'),
                [data],
                data.get('display_config', {})
            )

    def _add_slices_to_existing_hyperstack(self, existing_imp, new_images: List[Dict[str, Any]],
                                             window_key: str, channel_components: List[str],
                                             slice_components: List[str], frame_components: List[str],
                                             display_config_dict: Dict[str, Any]):
        """
        Incrementally add new slices to an existing hyperstack WITHOUT rebuilding.

        This avoids the expensive min/max recalculation that happens when rebuilding.
        """
        import numpy as np
        from multiprocessing import shared_memory
        import scyjava as sj

        # Import ImageJ classes
        ShortProcessor = sj.jimport('ij.process.ShortProcessor')

        # Get existing metadata
        existing_images = self.hyperstack_metadata[window_key]

        # Build lookup of existing images by coordinates
        existing_lookup = {}
        for img_data in existing_images:
            meta = img_data['metadata']
            c_key = tuple(meta.get(comp, 1) for comp in channel_components)
            z_key = tuple(meta.get(comp, 1) for comp in slice_components)
            t_key = tuple(meta.get(comp, 1) for comp in frame_components)
            existing_lookup[(c_key, z_key, t_key)] = img_data

        # Get existing stack and dimensions
        stack = existing_imp.getStack()
        old_nChannels = existing_imp.getNChannels()
        old_nSlices = existing_imp.getNSlices()
        old_nFrames = existing_imp.getNFrames()

        # Collect dimension values from existing images
        existing_channel_values = self._collect_dimension_values(existing_images, channel_components)
        existing_slice_values = self._collect_dimension_values(existing_images, slice_components)
        existing_frame_values = self._collect_dimension_values(existing_images, frame_components)

        # Process new images and check if dimensions changed
        new_coords_added = []
        for img_data in new_images:
            meta = img_data['metadata']
            c_key = tuple(meta.get(comp, 1) for comp in channel_components)
            z_key = tuple(meta.get(comp, 1) for comp in slice_components)
            t_key = tuple(meta.get(comp, 1) for comp in frame_components)

            coord = (c_key, z_key, t_key)

            # Check if this is a new coordinate or replacement
            if coord not in existing_lookup:
                new_coords_added.append(coord)

            # Update lookup (new images override existing at same coordinates)
            existing_lookup[coord] = img_data

        # ImageJ hyperstacks have fixed dimensions - we need to rebuild when adding new slices
        # But we can preserve display ranges to avoid expensive min/max recalculation
        all_images = list(existing_lookup.values())

        logger.info(f"🔬 FIJI SERVER: 🔄 REBUILDING: Merging {len(new_images)} new images into '{window_key}' (total: {len(all_images)} images, existing had {len(existing_images)})")

        # Store display range before rebuilding
        display_ranges = []
        if old_nChannels > 0:
            for c in range(1, old_nChannels + 1):
                try:
                    existing_imp.setC(c)
                    display_ranges.append((existing_imp.getDisplayRangeMin(), existing_imp.getDisplayRangeMax()))
                except Exception as e:
                    logger.warning(f"Failed to get display range for channel {c}: {e}")
                    # Use default range if we can't get it
                    display_ranges.append((0, 255))

        # Close old hyperstack
        existing_imp.close()

        # Build new hyperstack with all images (old + new)
        # Pass is_new=False and preserved_display_ranges to avoid recalculation
        self._build_new_hyperstack(
            all_images, window_key, channel_components, slice_components,
            frame_components, display_config_dict, is_new=False,
            preserved_display_ranges=display_ranges
        )

    def _add_images_to_hyperstack(self, step_name: str, images: List[Dict[str, Any]],
                                    display_config_dict: Dict[str, Any]):
        """
        Add images to ImageJ hyperstacks using configurable dimension mapping.

        Uses FijiDimensionMode to map OpenHCS dimensions to ImageJ hyperstack dimensions:
        - WINDOW: Create separate windows
        - CHANNEL: Map to ImageJ Channel dimension (C)
        - SLICE: Map to ImageJ Slice dimension (Z)
        - FRAME: Map to ImageJ Frame dimension (T)

        Args:
            step_name: Name of the processing step
            images: List of image info dicts with metadata and shared memory names
            display_config_dict: Display configuration with component_modes
        """
        import numpy as np
        from multiprocessing import shared_memory

        # Load all images from shared memory
        image_data_list = []
        for image_info in images:
            shm_name = image_info.get('shm_name')
            shape = tuple(image_info.get('shape'))
            dtype = np.dtype(image_info.get('dtype'))
            component_metadata = image_info.get('component_metadata', {})
            image_id = image_info.get('image_id')  # UUID for acknowledgment

            try:
                shm = shared_memory.SharedMemory(name=shm_name)
                np_data = np.ndarray(shape, dtype=dtype, buffer=shm.buf).copy()
                shm.close()
                shm.unlink()  # Clean up shared memory

                image_data_list.append({
                    'data': np_data,
                    'metadata': component_metadata,
                    'image_id': image_id  # Preserve image_id for ack
                })
            except Exception as e:
                logger.error(f"🔬 FIJI SERVER: Failed to read shared memory {shm_name}: {e}")
                # Send error ack
                if image_id:
                    self._send_ack(image_id, status='error', error=f"Failed to read shared memory: {e}")
                continue

        if not image_data_list:
            return

        # Get component modes from display config
        component_modes = display_config_dict.get('component_modes', {})

        logger.info(f"🎛️  FIJI SERVER: Component modes from display config: {component_modes}")

        # Organize dimensions by their mode
        window_components = []  # Components that create separate windows
        channel_components = []  # Components mapped to ImageJ Channels
        slice_components = []  # Components mapped to ImageJ Slices
        frame_components = []  # Components mapped to ImageJ Frames

        for comp_name in ['well', 'site', 'channel', 'z_index', 'timepoint']:
            mode = component_modes.get(comp_name, 'channel')  # Default to channel

            if mode == 'window':
                window_components.append(comp_name)
            elif mode == 'channel':
                channel_components.append(comp_name)
            elif mode == 'slice':
                slice_components.append(comp_name)
            elif mode == 'frame':
                frame_components.append(comp_name)

        logger.info(f"🗂️  FIJI SERVER: Dimension mapping:")
        logger.info(f"  WINDOW: {window_components}")
        logger.info(f"  CHANNEL: {channel_components}")
        logger.info(f"  SLICE: {slice_components}")
        logger.info(f"  FRAME: {frame_components}")

        # Group images by window components
        # Components in WINDOW mode create separate windows
        # Components in CHANNEL/SLICE/FRAME modes are combined into the same hyperstack
        windows = {}
        for img_data in image_data_list:
            meta = img_data['metadata']

            # Build window key from step name and window components
            # This now includes well only if it's in WINDOW mode
            window_key_parts = [step_name]
            for comp in window_components:
                if comp in meta:
                    window_key_parts.append(f"{comp}={meta[comp]}")
            window_key = "_".join(window_key_parts)

            if window_key not in windows:
                windows[window_key] = []
            windows[window_key].append(img_data)

        # Build hyperstack for each window
        for window_key, window_images in windows.items():
            self._build_single_hyperstack(
                window_key, window_images, display_config_dict,
                channel_components, slice_components, frame_components
            )

    def _build_single_hyperstack(self, window_key: str, images: List[Dict[str, Any]],
                                  display_config_dict: Dict[str, Any],
                                  channel_components: List[str],
                                  slice_components: List[str],
                                  frame_components: List[str]):
        """
        Build or update a single ImageJ hyperstack from images.

        If a hyperstack already exists for this window_key, merge new images into it.
        Otherwise, create a new hyperstack.

        Args:
            window_key: Unique key for this window
            images: List of image data dicts (new images to add)
            display_config_dict: Display configuration
            channel_components: Components mapped to Channel dimension
            slice_components: Components mapped to Slice dimension
            frame_components: Components mapped to Frame dimension
        """
        import scyjava as sj

        # Import ImageJ classes using scyjava
        ImageStack = sj.jimport('ij.ImageStack')
        ImagePlus = sj.jimport('ij.ImagePlus')
        CompositeImage = sj.jimport('ij.CompositeImage')
        ShortProcessor = sj.jimport('ij.process.ShortProcessor')

        # Check if we have an existing hyperstack to merge into
        existing_imp = self.hyperstacks.get(window_key)
        is_new_hyperstack = existing_imp is None

        if not is_new_hyperstack:
            # INCREMENTAL UPDATE: Add only new slices to existing hyperstack
            logger.info(f"🔬 FIJI SERVER: ⚡ BATCH UPDATE: Adding {len(images)} new images to existing hyperstack '{window_key}'")
            self._add_slices_to_existing_hyperstack(
                existing_imp, images, window_key,
                channel_components, slice_components, frame_components,
                display_config_dict
            )
            return

        # NEW HYPERSTACK: Build from scratch
        logger.info(f"🔬 FIJI SERVER: ✨ NEW HYPERSTACK: Creating '{window_key}' with {len(images)} images")
        self._build_new_hyperstack(
            images, window_key, channel_components, slice_components,
            frame_components, display_config_dict, is_new=True
        )

    def _build_new_hyperstack(self, all_images: List[Dict[str, Any]], window_key: str,
                               channel_components: List[str], slice_components: List[str],
                               frame_components: List[str], display_config_dict: Dict[str, Any],
                               is_new: bool, preserved_display_ranges: List[tuple] = None):
        """
        Build a new hyperstack from scratch.

        Args:
            all_images: List of all images to include
            window_key: Window identifier
            channel_components: Components mapped to channel dimension
            slice_components: Components mapped to slice dimension
            frame_components: Components mapped to frame dimension
            display_config_dict: Display configuration
            is_new: True if this is a brand new hyperstack, False if rebuilding existing
            preserved_display_ranges: List of (min, max) tuples per channel to preserve
        """
        import numpy as np
        from multiprocessing import shared_memory
        import scyjava as sj

        # Import ImageJ classes
        ImageStack = sj.jimport('ij.ImageStack')
        ImagePlus = sj.jimport('ij.ImagePlus')
        CompositeImage = sj.jimport('ij.CompositeImage')
        ShortProcessor = sj.jimport('ij.process.ShortProcessor')

        # Collect unique values for each dimension (from all images)
        channel_values = self._collect_dimension_values(all_images, channel_components)
        slice_values = self._collect_dimension_values(all_images, slice_components)
        frame_values = self._collect_dimension_values(all_images, frame_components)

        nChannels = len(channel_values)
        nSlices = len(slice_values)
        nFrames = len(frame_values)

        logger.info(f"🔬 FIJI SERVER: Building hyperstack '{window_key}': "
                   f"{nChannels}C x {nSlices}Z x {nFrames}T")
        logger.info(f"  Channel components: {channel_components}")
        logger.info(f"  Slice components: {slice_components}")
        logger.info(f"  Frame components: {frame_components}")

        # Images should already have 'data' key (loaded from shared memory earlier)
        if not all_images:
            logger.error(f"🔬 FIJI SERVER: No images provided for '{window_key}'")
            return

        # Get spatial dimensions
        first_img = all_images[0]['data']
        height, width = first_img.shape[-2:]

        # Create ImageStack
        stack = ImageStack(width, height)

        # Build lookup dict (new images override existing at same coordinates)
        image_lookup = {}
        for img_data in all_images:
            meta = img_data['metadata']
            c_key = tuple(meta.get(comp, 1) for comp in channel_components)
            z_key = tuple(meta.get(comp, 1) for comp in slice_components)
            t_key = tuple(meta.get(comp, 1) for comp in frame_components)
            image_lookup[(c_key, z_key, t_key)] = img_data['data']

        # Add slices in ImageJ CZT order
        for t_key in frame_values:
            for z_key in slice_values:
                for c_key in channel_values:
                    key = (c_key, z_key, t_key)

                    if key in image_lookup:
                        np_data = image_lookup[key]

                        # Handle 3D data (take middle slice)
                        if np_data.ndim == 3:
                            np_data = np_data[np_data.shape[0] // 2]

                        # Convert to ImageProcessor
                        temp_imp = self.ij.py.to_imageplus(np_data)
                        processor = temp_imp.getProcessor()

                        # Build label
                        label_parts = []
                        if channel_components:
                            label_parts.append(f"C{c_key}")
                        if slice_components:
                            label_parts.append(f"Z{z_key}")
                        if frame_components:
                            label_parts.append(f"T{t_key}")
                        label = "_".join(label_parts) if label_parts else "slice"

                        stack.addSlice(label, processor)
                    else:
                        # Add blank slice if missing
                        blank = ShortProcessor(width, height)
                        stack.addSlice("BLANK", blank)

        # Create ImagePlus
        imp = ImagePlus(window_key, stack)

        # Set hyperstack dimensions
        imp.setDimensions(nChannels, nSlices, nFrames)

        # Convert to CompositeImage if multiple channels
        if nChannels > 1:
            comp = CompositeImage(imp, CompositeImage.COMPOSITE)
            comp.setTitle(window_key)
            imp = comp

        # Apply LUT and display settings
        lut_name = display_config_dict.get('lut', 'Grays')
        auto_contrast = display_config_dict.get('auto_contrast', True)

        if is_new:
            # Brand new hyperstack - apply LUT and auto-contrast
            if lut_name not in ['Grays', 'grays'] and nChannels == 1:
                try:
                    self.ij.IJ.run(imp, lut_name, "")
                except Exception as e:
                    logger.warning(f"🔬 FIJI SERVER: Failed to apply LUT {lut_name}: {e}")

            if auto_contrast:
                try:
                    # Only run expensive "Enhance Contrast" on brand new hyperstacks
                    # This recalculates min/max across ALL slices, which gets slower as stack grows
                    self.ij.IJ.run(imp, "Enhance Contrast", "saturated=0.35")
                    logger.debug(f"🔬 FIJI SERVER: Applied auto-contrast to new hyperstack '{window_key}'")
                except Exception as e:
                    logger.warning(f"🔬 FIJI SERVER: Failed to apply auto-contrast: {e}")

            # Show new hyperstack
            imp.show()
            self.hyperstacks[window_key] = imp

        else:
            # Rebuilt hyperstack - restore preserved display ranges BEFORE showing
            # This prevents ImageJ from auto-calculating display range
            if preserved_display_ranges:
                try:
                    for c in range(1, min(nChannels, len(preserved_display_ranges)) + 1):
                        min_val, max_val = preserved_display_ranges[c - 1]
                        imp.setC(c)
                        imp.setDisplayRange(min_val, max_val)

                    logger.debug(f"🔬 FIJI SERVER: Restored preserved display ranges for '{window_key}'")
                except Exception as e:
                    logger.warning(f"🔬 FIJI SERVER: Failed to restore display ranges: {e}")

            # Close old hyperstack and show new one
            # Display ranges are already set, so show() won't recalculate
            if window_key in self.hyperstacks:
                old_imp = self.hyperstacks[window_key]
                old_imp.close()

            imp.show()
            self.hyperstacks[window_key] = imp

        # Store metadata for future merging
        self.hyperstack_metadata[window_key] = all_images

        logger.info(f"🔬 FIJI SERVER: Displayed hyperstack '{window_key}' with {stack.getSize()} slices ({len(all_images)} unique images)")

        # Send acknowledgments for all successfully displayed images
        for img_data in all_images:
            image_id = img_data.get('image_id')
            if image_id:
                self._send_ack(image_id, status='success')

    def _collect_dimension_values(self, images: List[Dict[str, Any]], components: List[str]) -> List[tuple]:
        """
        Collect unique dimension value tuples from images.

        Args:
            images: List of image data dicts
            components: List of component names to collect

        Returns:
            Sorted list of unique value tuples
        """
        if not components:
            return [()]  # Single value if no components

        values = set()
        for img_data in images:
            meta = img_data['metadata']
            value_tuple = tuple(meta.get(comp, 1) for comp in components)
            values.add(value_tuple)

        return sorted(values)



    
    def request_shutdown(self):
        """Request graceful shutdown."""
        self._shutdown_requested = True
        self.stop()


def _fiji_viewer_server_process(port: int, viewer_title: str, display_config, log_file_path: str = None):
    """
    Fiji viewer server process function.
    
    Runs in separate process to manage Fiji instance and handle incoming image data.
    
    Args:
        port: ZMQ port to listen on
        viewer_title: Title for the Fiji viewer window
        display_config: FijiDisplayConfig instance
        log_file_path: Path to log file (for client discovery via ping/pong)
    """
    try:
        import zmq
        
        # Create ZMQ server instance (inherits from ZMQServer ABC)
        server = FijiViewerServer(port, viewer_title, display_config, log_file_path)
        
        # Start the server (binds sockets, initializes PyImageJ)
        server.start()
        
        logger.info(f"🔬 FIJI SERVER: Server started on port {port}, control port {port + 1000}")
        logger.info("🔬 FIJI SERVER: Waiting for images...")
        
        # Message processing loop
        while not server._shutdown_requested:
            # Process control messages (ping/pong handled by ABC)
            server.process_messages()
            
            # Process data messages (images) if ready
            if server._ready:
                # Process multiple messages per iteration for better throughput
                for _ in range(10):
                    try:
                        message = server.data_socket.recv(zmq.NOBLOCK)
                        server.process_image_message(message)
                    except zmq.Again:
                        break
            
            time.sleep(0.01)  # 10ms sleep to prevent busy-waiting
        
        logger.info("🔬 FIJI SERVER: Shutting down...")
        server.stop()
        
    except Exception as e:
        logger.error(f"🔬 FIJI SERVER: Error: {e}")
        import traceback
        traceback.print_exc()
    finally:
        logger.info("🔬 FIJI SERVER: Process terminated")

