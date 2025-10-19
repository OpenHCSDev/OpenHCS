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
from openhcs.constants.streaming import StreamingDataType

logger = logging.getLogger(__name__)


# Registry mapping data types to handler methods
_FIJI_ITEM_HANDLERS = {}

def register_fiji_handler(data_type: StreamingDataType):
    """Decorator to register handler for a data type."""
    def decorator(func):
        _FIJI_ITEM_HANDLERS[data_type] = func
        return func
    return decorator


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
        self.window_key_to_group_id = {}  # Map window_key strings to integer group IDs
        self._next_group_id = 1  # Counter for assigning group IDs
        self.window_dimension_values = {}  # Store dimension values (channel/slice/frame) per window

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

        msg_type = data.get('type')

        # Check message type
        if msg_type == 'batch':
            items = data.get('images', [])
            display_config_dict = data.get('display_config', {})
            images_dir = data.get('images_dir')

            logger.info(f"📨 FIJI SERVER: Received batch message with {len(items)} items")

            if not items:
                return

            # Process all items through unified pipeline
            self._process_items_from_batch(items, display_config_dict, images_dir)

        else:
            # Single image message (fallback)
            self._process_items_from_batch(
                [data],
                data.get('display_config', {}),
                data.get('images_dir')
            )

    def _process_items_from_batch(self, items: List[Dict[str, Any]], display_config_dict: Dict[str, Any], images_dir: str = None):
        """
        Unified processing for all item types (images, ROIs, future types).

        Uses polymorphic dispatch via registry to handle type-specific operations
        while sharing common component organization and coordinate mapping logic.

        Args:
            items: List of items (mixed types allowed)
            display_config_dict: Display configuration with component_modes
            images_dir: Source image subdirectory (for mapping ROI source to image source)
        """
        if not items:
            return

        # STEP 1: SHARED - Get component modes and order
        component_modes = display_config_dict.get('component_modes', {})
        component_order = display_config_dict['component_order']

        logger.info(f"🎛️  FIJI SERVER: Component modes: {component_modes}")
        logger.info(f"🎛️  FIJI SERVER: Component order: {component_order}")

        # STEP 2: SHARED - Collect unique values for ALL items (all types together)
        component_unique_values = {}
        for comp_name in component_order:
            unique_vals = set()
            for item in items:
                meta = item.get('metadata', {})
                if comp_name in meta:
                    unique_vals.add(meta[comp_name])
            component_unique_values[comp_name] = unique_vals

        logger.info(f"🔍 FIJI SERVER: Component cardinality: {[(c, len(v)) for c, v in component_unique_values.items()]}")

        # STEP 3: SHARED - Organize components by mode using component_modes directly
        # For Fiji, we don't use cardinality filtering - component_modes define the mapping
        # This ensures consistent CZT coordinate mapping regardless of batch size
        result = {
            'window': [],
            'channel': [],
            'slice': [],
            'frame': []
        }

        for comp_name in component_order:
            mode = component_modes[comp_name]
            result[mode].append(comp_name)

        organized = result

        window_components = organized['window']
        channel_components = organized['channel']
        slice_components = organized['slice']
        frame_components = organized['frame']

        logger.info(f"🗂️  FIJI SERVER: Dimension mapping:")
        logger.info(f"  WINDOW: {window_components}")
        logger.info(f"  CHANNEL: {channel_components}")
        logger.info(f"  SLICE: {slice_components}")
        logger.info(f"  FRAME: {frame_components}")

        # STEP 4: SHARED - Group items by window components
        windows = {}
        for item in items:
            meta = item.get('metadata', {})
            data_type_str = item.get('data_type')

            # Build window key from window components
            # For ROIs: normalize source to match image hyperstack using images_dir
            window_key_parts = []
            for comp in window_components:
                if comp in meta:
                    value = meta[comp]
                    # Normalize source ONLY for ROIs: use images_dir (maps 'images_results' -> 'images')
                    if comp == 'source' and images_dir and data_type_str == 'rois':
                        from pathlib import Path
                        value = Path(images_dir).name  # Extract subdirectory name from full path
                    window_key_parts.append(f"{comp}_{value}")
            window_key = "_".join(window_key_parts) if window_key_parts else "default_window"

            if window_key not in windows:
                windows[window_key] = []
            windows[window_key].append(item)

        # STEP 5: Process each window group
        for window_key, window_items in windows.items():
            self._process_window_group(
                window_key, window_items, display_config_dict,
                channel_components, slice_components, frame_components
            )

    def _process_window_group(self, window_key: str, items: List[Dict[str, Any]],
                              display_config_dict: Dict[str, Any],
                              channel_components: List[str],
                              slice_components: List[str],
                              frame_components: List[str]):
        """
        Process all items for a single window group.

        Builds shared coordinate space, then dispatches to type-specific handlers.

        Args:
            window_key: Window identifier
            items: All items for this window (mixed types)
            display_config_dict: Display configuration
            channel_components: Components mapped to Channel dimension
            slice_components: Components mapped to Slice dimension
            frame_components: Components mapped to Frame dimension
        """
        # STEP 1: SHARED - Collect dimension values from ALL items (all types)
        # For images: collect from current batch and store for future ROI batches
        # For ROIs: reuse stored values from corresponding image hyperstack

        # Check if we have stored dimension values for this window (from previous image batch)
        if window_key in self.window_dimension_values:
            # Reuse stored values (for ROIs matching existing hyperstack)
            stored = self.window_dimension_values[window_key]
            channel_values = stored['channel']
            slice_values = stored['slice']
            frame_values = stored['frame']
            logger.info(f"🔬 FIJI SERVER: Reusing stored dimension values for window '{window_key}'")
        else:
            # Collect from current batch (for new hyperstacks)
            channel_values = self._collect_dimension_values_from_items(
                items, channel_components
            )
            slice_values = self._collect_dimension_values_from_items(
                items, slice_components
            )
            frame_values = self._collect_dimension_values_from_items(
                items, frame_components
            )

            # Store for future batches (ROIs)
            self.window_dimension_values[window_key] = {
                'channel': channel_values,
                'slice': slice_values,
                'frame': frame_values
            }
            logger.info(f"🔬 FIJI SERVER: Stored dimension values for window '{window_key}'")

        # STEP 2: Group items by data_type (convert string to enum)
        items_by_type = {}
        for item in items:
            data_type_str = item.get('data_type')

            # Convert string to StreamingDataType enum
            if data_type_str == 'image':
                data_type = StreamingDataType.IMAGE
            elif data_type_str == 'rois':
                data_type = StreamingDataType.ROIS
            else:
                logger.warning(f"🔬 FIJI SERVER: Unknown data type string: {data_type_str}")
                continue

            if data_type not in items_by_type:
                items_by_type[data_type] = []
            items_by_type[data_type].append(item)

        # STEP 3: POLYMORPHIC DISPATCH - Call handler for each type
        for data_type, type_items in items_by_type.items():
            handler = _FIJI_ITEM_HANDLERS.get(data_type)

            if handler is None:
                logger.warning(f"🔬 FIJI SERVER: No handler registered for type {data_type}")
                continue

            # Call handler with shared coordinate space
            handler(
                self, window_key, type_items, display_config_dict,
                channel_components, slice_components, frame_components,
                channel_values, slice_values, frame_values
            )

    def _collect_dimension_values_from_items(self, items: List[Dict[str, Any]],
                                             component_list: List[str]) -> List[tuple]:
        """
        Collect unique dimension values from items for coordinate mapping.

        Args:
            items: List of items (any type)
            component_list: List of component names for this dimension

        Returns:
            Sorted list of unique tuples of component values
        """
        if not component_list:
            return [()]

        unique_values = set()
        for item in items:
            meta = item.get('metadata', {})

            # Build tuple of values for this dimension (fail loud if missing)
            value_tuple = tuple(meta[comp] for comp in component_list)
            unique_values.add(value_tuple)

        return sorted(unique_values)

    def _get_dimension_index(self, metadata: Dict[str, Any],
                             component_list: List[str],
                             dimension_values: List[tuple]) -> int:
        """
        Get index in dimension_values for metadata components.

        Maps component metadata values to coordinate space index.

        Args:
            metadata: Component metadata dict
            component_list: List of component names for this dimension
            dimension_values: Sorted list of unique value tuples for this dimension

        Returns:
            Index (0-based) or -1 if not found
        """
        # Build key from metadata (empty tuple if no components, fail loud if missing)
        key = tuple(metadata[comp] for comp in component_list) if component_list else ()

        try:
            return dimension_values.index(key)
        except ValueError:
            logger.warning(f"🔬 FIJI SERVER: Dimension value {key} not found in {dimension_values}")
            return -1

    def _add_slices_to_existing_hyperstack(self, existing_imp, new_images: List[Dict[str, Any]],
                                             window_key: str, channel_components: List[str],
                                             slice_components: List[str], frame_components: List[str],
                                             display_config_dict: Dict[str, Any],
                                             channel_values: List[tuple] = None,
                                             slice_values: List[tuple] = None,
                                             frame_values: List[tuple] = None):
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
            c_key = tuple(meta[comp] for comp in channel_components) if channel_components else ()
            z_key = tuple(meta[comp] for comp in slice_components) if slice_components else ()
            t_key = tuple(meta[comp] for comp in frame_components) if frame_components else ()
            existing_lookup[(c_key, z_key, t_key)] = img_data

        # Get existing stack and dimensions
        stack = existing_imp.getStack()
        old_nChannels = existing_imp.getNChannels()
        old_nSlices = existing_imp.getNSlices()
        old_nFrames = existing_imp.getNFrames()

        # Collect dimension values from existing images
        existing_channel_values = self.collect_dimension_values(existing_images, channel_components)
        existing_slice_values = self.collect_dimension_values(existing_images, slice_components)
        existing_frame_values = self.collect_dimension_values(existing_images, frame_components)

        # Process new images and check if dimensions changed
        new_coords_added = []
        for img_data in new_images:
            meta = img_data['metadata']
            c_key = tuple(meta[comp] for comp in channel_components) if channel_components else ()
            z_key = tuple(meta[comp] for comp in slice_components) if slice_components else ()
            t_key = tuple(meta[comp] for comp in frame_components) if frame_components else ()

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
        # Pass dimension values to use shared coordinate space
        self._build_new_hyperstack(
            all_images, window_key, channel_components, slice_components,
            frame_components, display_config_dict, is_new=False,
            preserved_display_ranges=display_ranges,
            channel_values=channel_values, slice_values=slice_values, frame_values=frame_values
        )

    def _build_single_hyperstack(self, window_key: str, images: List[Dict[str, Any]],
                                  display_config_dict: Dict[str, Any],
                                  channel_components: List[str],
                                  slice_components: List[str],
                                  frame_components: List[str],
                                  channel_values: List[tuple] = None,
                                  slice_values: List[tuple] = None,
                                  frame_values: List[tuple] = None):
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
            channel_values: Pre-computed channel dimension values (optional, for shared coordinate space)
            slice_values: Pre-computed slice dimension values (optional, for shared coordinate space)
            frame_values: Pre-computed frame dimension values (optional, for shared coordinate space)
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
                display_config_dict,
                channel_values=channel_values, slice_values=slice_values, frame_values=frame_values
            )
            return

        # NEW HYPERSTACK: Build from scratch
        logger.info(f"🔬 FIJI SERVER: ✨ NEW HYPERSTACK: Creating '{window_key}' with {len(images)} images")
        self._build_new_hyperstack(
            images, window_key, channel_components, slice_components,
            frame_components, display_config_dict, is_new=True,
            channel_values=channel_values, slice_values=slice_values, frame_values=frame_values
        )

    def _build_image_lookup(self, images, channel_components, slice_components, frame_components):
        """Build coordinate lookup dict from images.

        Returns:
            Dict mapping (c_key, z_key, t_key) to image data
        """
        image_lookup = {}
        for img_data in images:
            meta = img_data['metadata']
            c_key = tuple(meta[comp] for comp in channel_components) if channel_components else ()
            z_key = tuple(meta[comp] for comp in slice_components) if slice_components else ()
            t_key = tuple(meta[comp] for comp in frame_components) if frame_components else ()
            image_lookup[(c_key, z_key, t_key)] = img_data['data']
        return image_lookup

    def _create_imagestack_from_images(self, image_lookup, channel_values, slice_values, frame_values,
                                        width, height, channel_components, slice_components, frame_components):
        """Create ImageJ ImageStack from image lookup dict.

        Returns:
            ImageJ ImageStack object
        """
        import scyjava as sj
        ImageStack = sj.jimport('ij.ImageStack')
        ShortProcessor = sj.jimport('ij.process.ShortProcessor')

        stack = ImageStack(width, height)

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
                            c_str = "_".join(str(v) for v in c_key) if isinstance(c_key, tuple) else str(c_key)
                            label_parts.append(f"C{c_str}")
                        if slice_components:
                            z_str = "_".join(str(v) for v in z_key) if isinstance(z_key, tuple) else str(z_key)
                            label_parts.append(f"Z{z_str}")
                        if frame_components:
                            t_str = "_".join(str(v) for v in t_key) if isinstance(t_key, tuple) else str(t_key)
                            label_parts.append(f"T{t_str}")
                        label = "_".join(label_parts) if label_parts else "slice"

                        stack.addSlice(label, processor)
                    else:
                        # Add blank slice if missing
                        blank = ShortProcessor(width, height)
                        stack.addSlice("BLANK", blank)

        return stack

    def _convert_to_hyperstack(self, imp, nChannels, nSlices, nFrames, window_key):
        """Convert ImagePlus to HyperStack with proper dimensions.

        Returns:
            ImagePlus or CompositeImage
        """
        import scyjava as sj

        # Set hyperstack dimensions
        imp.setDimensions(nChannels, nSlices, nFrames)

        # Convert to HyperStack to enable proper Z/T slider behavior
        if nSlices > 1 or nFrames > 1 or nChannels > 1:
            HyperStackConverter = sj.jimport('ij.plugin.HyperStackConverter')
            imp = HyperStackConverter.toHyperStack(imp, nChannels, nSlices, nFrames, "xyczt", "Composite")
            imp.setTitle(window_key)

        # Convert to CompositeImage if multiple channels
        if nChannels > 1:
            CompositeImage = sj.jimport('ij.CompositeImage')
            if not isinstance(imp, CompositeImage):
                comp = CompositeImage(imp, CompositeImage.COMPOSITE)
                comp.setTitle(window_key)
                imp = comp

        return imp

    def _apply_display_settings(self, imp, lut_name, auto_contrast, nChannels, preserved_ranges=None):
        """Apply LUT and display settings to ImagePlus.

        Args:
            imp: ImagePlus to modify
            lut_name: LUT name to apply
            auto_contrast: Whether to apply auto-contrast
            nChannels: Number of channels
            preserved_ranges: Optional list of (min, max) tuples per channel
        """
        if preserved_ranges:
            # Restore preserved display ranges
            for c in range(1, min(nChannels, len(preserved_ranges)) + 1):
                min_val, max_val = preserved_ranges[c - 1]
                imp.setC(c)
                imp.setDisplayRange(min_val, max_val)
        else:
            # Apply LUT and auto-contrast for new hyperstacks
            if lut_name not in ['Grays', 'grays'] and nChannels == 1:
                try:
                    self.ij.IJ.run(imp, lut_name, "")
                except Exception as e:
                    logger.warning(f"🔬 FIJI SERVER: Failed to apply LUT {lut_name}: {e}")

            if auto_contrast:
                try:
                    self.ij.IJ.run(imp, "Enhance Contrast", "saturated=0.35")
                except Exception as e:
                    logger.warning(f"🔬 FIJI SERVER: Failed to apply auto-contrast: {e}")

    def _build_new_hyperstack(self, all_images: List[Dict[str, Any]], window_key: str,
                               channel_components: List[str], slice_components: List[str],
                               frame_components: List[str], display_config_dict: Dict[str, Any],
                               is_new: bool, preserved_display_ranges: List[tuple] = None,
                               channel_values: List[tuple] = None,
                               slice_values: List[tuple] = None,
                               frame_values: List[tuple] = None):
        """Build a new hyperstack from scratch."""
        import scyjava as sj

        # Collect dimension values (use provided values if available, otherwise compute)
        if channel_values is None:
            channel_values = self.collect_dimension_values(all_images, channel_components)
        if slice_values is None:
            slice_values = self.collect_dimension_values(all_images, slice_components)
        if frame_values is None:
            frame_values = self.collect_dimension_values(all_images, frame_components)

        nChannels = len(channel_values)
        nSlices = len(slice_values)
        nFrames = len(frame_values)

        logger.info(f"🔬 FIJI SERVER: Building hyperstack '{window_key}': {nChannels}C x {nSlices}Z x {nFrames}T")

        if not all_images:
            logger.error(f"🔬 FIJI SERVER: No images provided for '{window_key}'")
            return

        # Get spatial dimensions
        first_img = all_images[0]['data']
        height, width = first_img.shape[-2:]

        # Build image lookup
        image_lookup = self._build_image_lookup(all_images, channel_components, slice_components, frame_components)

        # Create ImageStack
        stack = self._create_imagestack_from_images(
            image_lookup, channel_values, slice_values, frame_values,
            width, height, channel_components, slice_components, frame_components
        )

        # Create ImagePlus
        ImagePlus = sj.jimport('ij.ImagePlus')
        imp = ImagePlus(window_key, stack)

        # Convert to hyperstack
        imp = self._convert_to_hyperstack(imp, nChannels, nSlices, nFrames, window_key)

        # Apply display settings
        lut_name = display_config_dict.get('lut', 'Grays')
        auto_contrast = display_config_dict.get('auto_contrast', True)
        self._apply_display_settings(
            imp, lut_name, auto_contrast, nChannels,
            preserved_ranges=None if is_new else preserved_display_ranges
        )

        # Close old hyperstack if rebuilding
        if window_key in self.hyperstacks:
            self.hyperstacks[window_key].close()

        # Show and store
        imp.show()
        self.hyperstacks[window_key] = imp
        self.hyperstack_metadata[window_key] = all_images

        logger.info(f"🔬 FIJI SERVER: Displayed hyperstack '{window_key}' with {stack.getSize()} slices")

        # Send acknowledgments
        for img_data in all_images:
            if image_id := img_data.get('image_id'):
                self._send_ack(image_id, status='success')

    def request_shutdown(self):
        """Request graceful shutdown."""
        self._shutdown_requested = True
        self.stop()


@register_fiji_handler(StreamingDataType.IMAGE)
def _handle_images_for_window(self, window_key: str, items: List[Dict[str, Any]],
                               display_config_dict: Dict[str, Any],
                               channel_components: List[str],
                               slice_components: List[str],
                               frame_components: List[str],
                               channel_values: List[tuple],
                               slice_values: List[tuple],
                               frame_values: List[tuple]):
    """
    Handle images for a window group.

    Builds or updates ImageJ hyperstack using shared coordinate space.
    """
    # Load images from shared memory
    image_data_list = self.load_images_from_shared_memory(items, error_callback=self._send_ack)

    if not image_data_list:
        return

    # Delegate to existing hyperstack building logic
    # Pass dimension values so it uses shared coordinate space
    self._build_single_hyperstack(
        window_key, image_data_list, display_config_dict,
        channel_components, slice_components, frame_components,
        channel_values, slice_values, frame_values
    )


@register_fiji_handler(StreamingDataType.ROIS)
def _handle_rois_for_window(self, window_key: str, items: List[Dict[str, Any]],
                             display_config_dict: Dict[str, Any],
                             channel_components: List[str],
                             slice_components: List[str],
                             frame_components: List[str],
                             channel_values: List[tuple],
                             slice_values: List[tuple],
                             frame_values: List[tuple]):
    """
    Handle ROIs for a window group.

    Adds ROIs to ROI Manager with proper CZT positioning using shared coordinate space.
    ROIs are grouped by window_key to associate with corresponding hyperstack.
    """
    from openhcs.runtime.roi_converters import FijiROIConverter
    import scyjava as sj

    RoiManager = sj.jimport('ij.plugin.frame.RoiManager')
    rm = RoiManager.getInstance()
    if rm is None:
        rm = RoiManager()

    # Get or assign integer group ID for this window
    if window_key not in self.window_key_to_group_id:
        self.window_key_to_group_id[window_key] = self._next_group_id
        self._next_group_id += 1

    group_id = self.window_key_to_group_id[window_key]

    total_rois_added = 0

    for roi_item in items:
        rois_encoded = roi_item.get('rois', [])
        if not rois_encoded:
            if image_id := roi_item.get('image_id'):
                self._send_ack(image_id, status='success')
            continue

        meta = roi_item.get('metadata', {})
        file_path = roi_item.get('path', 'unknown')

        logger.info(f"🔬 FIJI SERVER: ROI metadata: {meta}")
        logger.info(f"🔬 FIJI SERVER: Channel components: {channel_components}, values: {channel_values}")
        logger.info(f"🔬 FIJI SERVER: Slice components: {slice_components}, values: {slice_values}")
        logger.info(f"🔬 FIJI SERVER: Frame components: {frame_components}, values: {frame_values}")

        # Map metadata to CZT indices using SHARED coordinate space
        c_index = self._get_dimension_index(meta, channel_components, channel_values)
        z_index = self._get_dimension_index(meta, slice_components, slice_values)
        t_index = self._get_dimension_index(meta, frame_components, frame_values)

        # Convert to 1-indexed for ImageJ (0 means "all")
        c_value = c_index + 1 if c_index >= 0 else 1
        z_value = z_index + 1 if z_index >= 0 else 1
        t_value = t_index + 1 if t_index >= 0 else 1

        logger.info(f"🔬 FIJI SERVER: ROI '{file_path}' position: C={c_value}, Z={z_value}, T={t_value} (from indices {c_index}, {z_index}, {t_index})")

        # Decode and add ROIs
        roi_bytes_list = FijiROIConverter.decode_rois_from_transmission(rois_encoded)

        # Extract base name from path for ROI naming
        from pathlib import Path
        base_name = Path(file_path).stem  # Get filename without extension

        for roi_idx, roi_bytes in enumerate(roi_bytes_list):
            java_roi = FijiROIConverter.bytes_to_java_roi(roi_bytes, sj)

            # Set ROI name using file path and index
            roi_name = f"{base_name}_{roi_idx:04d}"
            java_roi.setName(roi_name)

            # Set hyperstack position (same coordinate space as images!)
            java_roi.setPosition(c_value, z_value, t_value)

            # Set group ID (associates ROIs with hyperstack window)
            java_roi.setGroup(group_id)

            rm.addRoi(java_roi)
            total_rois_added += 1

        if image_id := roi_item.get('image_id'):
            self._send_ack(image_id, status='success')

    if not rm.isVisible():
        rm.setVisible(True)

    logger.info(f"🔬 FIJI SERVER: Added {total_rois_added} ROIs to group {group_id} ('{window_key}') with shared coordinate space")


# Make handlers instance methods by binding them to the class
FijiViewerServer._handle_images_for_window = _handle_images_for_window
FijiViewerServer._handle_rois_for_window = _handle_rois_for_window


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

