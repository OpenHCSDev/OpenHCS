"""
Fiji viewer server for OpenHCS.

ZMQ-based server that receives images from FijiStreamingBackend and displays them
via PyImageJ. Inherits from ZMQServer ABC for ping/pong handshake and dual-channel pattern.
"""

import logging
import time
import threading
from typing import Dict, Any, List

from openhcs.runtime.zmq_base import ZMQServer, SHARED_ACK_PORT, get_zmq_transport_url
from openhcs.runtime.zmq_messages import ImageAck
from openhcs.constants.streaming import StreamingDataType
from openhcs.core.config import TransportMode

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

    _server_type = 'fiji'  # Registration key for AutoRegisterMeta

    # Debouncing configuration
    DEBOUNCE_DELAY_MS = 500  # Collect items for 500ms before processing
    MAX_DEBOUNCE_WAIT_MS = 2000  # Maximum wait time before forcing batch processing

    def __init__(self, port: int, viewer_title: str, display_config, log_file_path: str = None, transport_mode: TransportMode = TransportMode.IPC):
        """
        Initialize Fiji viewer server.

        Args:
            port: Data port for receiving images (control port will be port + 1000)
            viewer_title: Title for the Fiji viewer window
            display_config: FijiDisplayConfig with LUT, dimension modes, etc.
            log_file_path: Path to log file (for client discovery)
            transport_mode: ZMQ transport mode (IPC or TCP)
        """
        import zmq

        # Initialize with REP socket for receiving images (synchronous request/reply)
        # REP socket forces workers to wait for acknowledgment before closing shared memory
        super().__init__(port, host='*', log_file_path=log_file_path, data_socket_type=zmq.REP, transport_mode=transport_mode)

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

        # Debouncing for batched processing
        self._pending_items = []  # Queue of copied items waiting to be processed
        self._pending_display_config = None  # Display config for pending batch
        self._pending_images_dir = None  # Images dir for pending batch
        self._pending_component_names_metadata = {}  # Component names metadata for dimension labels
        self._debounce_timer = None  # Timer for debounced processing
        self._debounce_lock = threading.Lock()  # Lock for pending queue
        self._debounce_delay = self.DEBOUNCE_DELAY_MS / 1000.0  # Convert ms to seconds
        self._max_debounce_wait = self.MAX_DEBOUNCE_WAIT_MS / 1000.0  # Convert ms to seconds
        self._first_message_time = None  # Track when first message in batch arrived

        # Lock for hyperstack operations to prevent concurrent batch processing from
        # overwriting each other's hyperstacks (race condition in fast sequential mode)
        self._hyperstack_lock = threading.Lock()

    def _setup_ack_socket(self):
        """Setup PUSH socket for sending acknowledgments."""
        import zmq
        try:
            ack_url = get_zmq_transport_url(SHARED_ACK_PORT, self.transport_mode, 'localhost')

            context = zmq.Context.instance()
            self.ack_socket = context.socket(zmq.PUSH)
            self.ack_socket.connect(ack_url)
            logger.info(f"🔬 FIJI SERVER: Connected ack socket to {ack_url}")
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
    
    def _wait_for_swing_ui_ready(self, timeout: float = 5.0) -> bool:
        """Wait for Java Swing UI to be fully initialized.

        This is critical for IPC mode where messages arrive very fast.
        RoiManager and other Swing components require the EDT to be ready.

        Args:
            timeout: Maximum time to wait in seconds

        Returns:
            True if UI is ready, False if timeout
        """
        import time
        import scyjava as sj

        start_time = time.time()
        while time.time() - start_time < timeout:
            try:
                # Try to access UIManager and verify UIDefaults are populated
                # This is critical because RoiManager needs JList UI components
                UIManager = sj.jimport('javax.swing.UIManager')
                look_and_feel = UIManager.getLookAndFeel()

                if look_and_feel is not None:
                    # Additional check: verify UIDefaults has JList UI class
                    # This is what RoiManager needs (it contains a JList)
                    ui_defaults = UIManager.getDefaults()
                    list_ui = ui_defaults.get("ListUI")

                    if list_ui is not None:
                        logger.info("🔬 FIJI SERVER: Java Swing UI is ready (UIDefaults populated)")
                        return True
                    else:
                        logger.debug("🔬 FIJI SERVER: Waiting for UIDefaults to populate...")

            except Exception as e:
                logger.debug(f"🔬 FIJI SERVER: Waiting for Swing UI: {e}")
            time.sleep(0.1)

        logger.warning("🔬 FIJI SERVER: Timeout waiting for Swing UI initialization")
        return False

    def start(self):
        """Start server and initialize PyImageJ."""
        super().start()

        # Initialize PyImageJ in this process
        try:
            import imagej
            logger.info("🔬 FIJI SERVER: Initializing PyImageJ...")

            # Try interactive mode first, fall back to headless mode on macOS
            try:
                self.ij = imagej.init(mode='interactive')
                # Show Fiji UI so users can interact with images and menus
                self.ij.ui().showUI()
                logger.info("🔬 FIJI SERVER: PyImageJ initialized in interactive mode with UI shown")

                # Wait for Java Swing UI to be fully initialized
                # This is critical for IPC mode where messages arrive very fast
                # RoiManager creation requires the Swing event dispatch thread to be ready
                if not self._wait_for_swing_ui_ready(timeout=5.0):
                    logger.warning("🔬 FIJI SERVER: Swing UI may not be fully initialized, proceeding anyway")

            except OSError as e:
                if "Cannot enable interactive mode" in str(e):
                    logger.warning("🔬 FIJI SERVER: Interactive mode failed (likely macOS), using headless mode")
                    self.ij = imagej.init(mode='headless')
                    logger.info("🔬 FIJI SERVER: PyImageJ initialized in headless mode")
                else:
                    raise
        except ImportError:
            raise ImportError("PyImageJ not available. Install with: pip install 'openhcs[viz]'")
    
    def _create_pong_response(self) -> Dict[str, Any]:
        """Override to add Fiji-specific fields and memory usage."""
        response = super()._create_pong_response()
        response['viewer'] = 'fiji'
        response['openhcs'] = True
        response['server'] = 'FijiViewerServer'

        # Add memory usage
        try:
            import psutil
            import os
            process = psutil.Process(os.getpid())
            response['memory_mb'] = process.memory_info().rss / 1024 / 1024
            response['cpu_percent'] = process.cpu_percent(interval=0)
        except Exception:
            pass

        return response

    def handle_control_message(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle control messages beyond ping/pong.

        Supported message types:
        - shutdown: Graceful shutdown (closes viewer)
        - force_shutdown: Force shutdown (same as shutdown for Fiji)
        - clear_state: Clear accumulated dimension values and hyperstack metadata (for new pipeline runs)
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

        elif msg_type == 'clear_state':
            # Clear accumulated dimension values to prevent accumulation across runs
            # Keep hyperstacks and metadata so images at same coordinates get replaced (not accumulated)
            logger.info(f"🔬 FIJI SERVER: Clearing dimension values (had {len(self.window_dimension_values)} windows)")

            # Clear only dimension values - this prevents dimension accumulation
            # while allowing image replacement at same coordinates
            self.window_dimension_values.clear()
            # Note: self.hyperstacks and self.hyperstack_metadata are NOT cleared
            # This allows the rebuild logic to replace images at same CZT coordinates

            return {
                'type': 'clear_state_ack',
                'status': 'success',
                'message': 'Dimension values cleared'
            }

        return {'status': 'ok'}
    
    def handle_data_message(self, message: Dict[str, Any]):
        """Handle incoming image data - called by process_messages()."""
        pass

    def _copy_items_from_shared_memory(self, items: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """
        Copy data from shared memory to local memory for all items.

        This MUST be called before sending ack to worker, so worker doesn't close shared memory.

        Args:
            items: List of items with shared memory references

        Returns:
            List of items with copied data (shared memory replaced with numpy arrays)
        """
        import numpy as np
        from multiprocessing import shared_memory

        copied_items = []
        for item in items:
            copied_item = item.copy()

            # Only copy shared memory for image items (not ROIs)
            if item.get('data_type') == 'image' and 'shm_name' in item:
                shm_name = item['shm_name']
                shape = tuple(item['shape'])
                dtype = np.dtype(item['dtype'])

                try:
                    # Attach to shared memory and copy data
                    shm = shared_memory.SharedMemory(name=shm_name)
                    np_data = np.ndarray(shape, dtype=dtype, buffer=shm.buf).copy()
                    shm.close()
                    shm.unlink()  # Clean up shared memory

                    # Replace shared memory reference with actual data
                    copied_item['data'] = np_data
                    del copied_item['shm_name']  # No longer needed
                    del copied_item['shape']  # No longer needed
                    del copied_item['dtype']  # No longer needed

                    logger.debug(f"📋 FIJI SERVER: Copied image data from shared memory {shm_name}")

                except Exception as e:
                    logger.error(f"📋 FIJI SERVER: Failed to copy from shared memory {shm_name}: {e}")
                    # Send error ack for this image
                    image_id = item.get('image_id')
                    if image_id:
                        self._send_ack(image_id, status='error', error=str(e))
                    continue

            copied_items.append(copied_item)

        return copied_items

    def _queue_for_debounced_processing(self, items: List[Dict[str, Any]], display_config_dict: Dict[str, Any], images_dir: str, component_names_metadata: Dict[str, Any] = None):
        """
        Queue items for debounced batch processing.

        Collects items for DEBOUNCE_DELAY_MS before processing to batch multiple images together.
        This improves hyperstack building efficiency.

        Args:
            items: List of items with copied data
            display_config_dict: Display configuration
            images_dir: Source image subdirectory
            component_names_metadata: Component name mappings for dimension labels
        """
        with self._debounce_lock:
            # Add items to pending queue
            self._pending_items.extend(items)
            self._pending_display_config = display_config_dict
            self._pending_images_dir = images_dir
            self._pending_component_names_metadata = component_names_metadata or {}

            # Track first message time for max wait enforcement
            if self._first_message_time is None:
                self._first_message_time = time.time()

            # Cancel existing timer if any
            if self._debounce_timer is not None:
                self._debounce_timer.cancel()

            # Check if we've exceeded max wait time
            elapsed = time.time() - self._first_message_time
            if elapsed >= self._max_debounce_wait:
                # Process immediately, don't wait any longer
                logger.info(f"⏱️  FIJI SERVER: Max debounce wait ({self._max_debounce_wait}s) exceeded, processing {len(self._pending_items)} items immediately")
                self._process_pending_batch()
            else:
                # Start new debounce timer
                remaining_wait = min(self._debounce_delay, self._max_debounce_wait - elapsed)
                logger.debug(f"⏱️  FIJI SERVER: Debouncing {len(self._pending_items)} items for {remaining_wait:.3f}s")
                self._debounce_timer = threading.Timer(remaining_wait, self._process_pending_batch)
                self._debounce_timer.start()

    def _process_pending_batch(self):
        """Process all pending items as a batch (called by debounce timer)."""
        with self._debounce_lock:
            if not self._pending_items:
                return

            items = self._pending_items
            display_config_dict = self._pending_display_config
            images_dir = self._pending_images_dir
            component_names_metadata = self._pending_component_names_metadata

            # Clear pending queue
            self._pending_items = []
            self._pending_display_config = None
            self._pending_images_dir = None
            self._pending_component_names_metadata = {}
            self._debounce_timer = None
            self._first_message_time = None

            logger.info(f"🔄 FIJI SERVER: Processing debounced batch of {len(items)} items")

        # Process batch (outside lock to avoid blocking new messages)
        try:
            self._process_items_from_batch(items, display_config_dict, images_dir, component_names_metadata)
        except Exception as e:
            logger.error(f"🔄 FIJI SERVER: Error processing debounced batch: {e}", exc_info=True)

    def process_image_message(self, message: bytes) -> dict:
        """
        Process incoming image data message with debouncing.

        IMMEDIATELY copies data from shared memory and queues for debounced processing.
        This allows worker to close shared memory quickly while Fiji batches processing.

        Args:
            message: Raw ZMQ message containing image data

        Returns:
            Acknowledgment dict with status
        """
        import json

        try:
            # Parse JSON message
            data = json.loads(message.decode('utf-8'))

            msg_type = data.get('type')

            # Check message type
            if msg_type == 'batch':
                items = data.get('images', [])
                display_config_dict = data.get('display_config', {})
                images_dir = data.get('images_dir')
                component_names_metadata = data.get('component_names_metadata', {})

                logger.info(f"📨 FIJI SERVER: Received batch message with {len(items)} items")

                if not items:
                    return {'status': 'success', 'message': 'Empty batch'}

                # CRITICAL: Copy data from shared memory IMMEDIATELY
                # This must happen before we send ack, so worker doesn't close shared memory
                copied_items = self._copy_items_from_shared_memory(items)

                # Queue copied items for debounced processing
                self._queue_for_debounced_processing(copied_items, display_config_dict, images_dir, component_names_metadata)

            else:
                # Single image message (fallback)
                copied_items = self._copy_items_from_shared_memory([data])
                self._queue_for_debounced_processing(
                    copied_items,
                    data.get('display_config', {}),
                    data.get('images_dir')
                )

            return {'status': 'success', 'message': 'Data copied, queued for processing'}

        except Exception as e:
            logger.error(f"📨 FIJI SERVER: Error processing message: {e}", exc_info=True)
            return {'status': 'error', 'message': str(e)}

    def _process_items_from_batch(self, items: List[Dict[str, Any]], display_config_dict: Dict[str, Any], images_dir: str = None, component_names_metadata: Dict[str, Any] = None):
        """
        Unified processing for all item types (images, ROIs, future types).

        Uses polymorphic dispatch via registry to handle type-specific operations
        while sharing common component organization and coordinate mapping logic.

        Args:
            items: List of items (mixed types allowed)
            display_config_dict: Display configuration with component_modes
            images_dir: Source image subdirectory (for mapping ROI source to image source)
            component_names_metadata: Component name mappings for dimension labels (e.g., channel names)
        """
        if not items:
            return
        
        # Default to empty dict if not provided
        if component_names_metadata is None:
            component_names_metadata = {}

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
            # Note: 'source' now represents step_name during pipeline execution,
            # so images and ROIs from the same step automatically have matching source values
            window_key_parts = []
            for comp in window_components:
                if comp in meta:
                    value = meta[comp]
                    # Legacy ROI normalization: only needed when loading from disk (image viewer context)
                    # During pipeline execution, source=step_name for both images and ROIs, so they match
                    if comp == 'source' and images_dir and data_type_str == 'rois':
                        # Check if source looks like a subdirectory (not a step name)
                        # Step names don't contain path separators or end with '_results'
                        if '_results' in str(value) or '/' in str(value):
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
                channel_components, slice_components, frame_components,
                component_names_metadata
            )

    def _process_window_group(self, window_key: str, items: List[Dict[str, Any]],
                              display_config_dict: Dict[str, Any],
                              channel_components: List[str],
                              slice_components: List[str],
                              frame_components: List[str],
                              component_names_metadata: Dict[str, Any] = None):
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
            component_names_metadata: Component name mappings for dimension labels
        """
        # Lock to prevent concurrent batches from overwriting each other's hyperstacks
        # (race condition in fast sequential mode where multiple debounce timers fire)
        with self._hyperstack_lock:
            self._process_window_group_locked(window_key, items, display_config_dict,
                                              channel_components, slice_components, frame_components,
                                              component_names_metadata)

    def _process_window_group_locked(self, window_key: str, items: List[Dict[str, Any]],
                                     display_config_dict: Dict[str, Any],
                                     channel_components: List[str],
                                     slice_components: List[str],
                                     frame_components: List[str],
                                     component_names_metadata: Dict[str, Any] = None):
        """
        Process window group with hyperstack lock held.

        This is the actual implementation, called by _process_window_group with lock held.
        """
        # STEP 1: SHARED - Collect dimension values from ALL items (all types)
        # For images: collect from current batch and MERGE with stored values to expand dimensions
        # For ROIs: reuse stored values from corresponding image hyperstack

        # Collect dimension values from current batch
        current_channel_values = self._collect_dimension_values_from_items(
            items, channel_components
        )
        current_slice_values = self._collect_dimension_values_from_items(
            items, slice_components
        )
        current_frame_values = self._collect_dimension_values_from_items(
            items, frame_components
        )

        # Check if we have stored dimension values for this window (from previous batches)
        if window_key in self.window_dimension_values:
            # Merge stored values with current values to expand dimensions
            stored = self.window_dimension_values[window_key]

            # Merge: combine stored and current, preserving order and uniqueness
            channel_values = self._merge_dimension_values(stored['channel'], current_channel_values)
            slice_values = self._merge_dimension_values(stored['slice'], current_slice_values)
            frame_values = self._merge_dimension_values(stored['frame'], current_frame_values)

            # Log if dimensions expanded
            if (len(channel_values) > len(stored['channel']) or
                len(slice_values) > len(stored['slice']) or
                len(frame_values) > len(stored['frame'])):
                logger.info(f"🔬 FIJI SERVER: Expanded dimensions for window '{window_key}': "
                           f"{len(stored['channel'])}→{len(channel_values)}C, "
                           f"{len(stored['slice'])}→{len(slice_values)}Z, "
                           f"{len(stored['frame'])}→{len(frame_values)}T")
            else:
                logger.info(f"🔬 FIJI SERVER: Reusing stored dimension values for window '{window_key}'")
        else:
            # First batch for this window - use current values
            channel_values = current_channel_values
            slice_values = current_slice_values
            frame_values = current_frame_values
            logger.info(f"🔬 FIJI SERVER: First batch for window '{window_key}': "
                       f"{len(channel_values)}C x {len(slice_values)}Z x {len(frame_values)}T")

        # Store merged values for future batches
        self.window_dimension_values[window_key] = {
            'channel': channel_values,
            'slice': slice_values,
            'frame': frame_values
        }

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
                channel_values, slice_values, frame_values,
                component_names_metadata
            )

    def _merge_dimension_values(self, stored_values: List[tuple],
                                 new_values: List[tuple]) -> List[tuple]:
        """
        Merge stored and new dimension values, preserving order and uniqueness.

        Args:
            stored_values: Previously stored dimension values
            new_values: New dimension values from current batch

        Returns:
            Merged list of unique dimension values, sorted
        """
        # Combine and deduplicate
        merged = set(stored_values) | set(new_values)

        # Sort with custom key that handles mixed types (int/str) in tuples
        # Convert each element to (type_priority, str_value) for comparison
        # This ensures consistent ordering even with mixed types
        def sort_key(value_tuple):
            return tuple(
                (0 if isinstance(v, (int, float)) else 1, str(v))
                for v in value_tuple
            )

        return sorted(merged, key=sort_key)

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

        # Sort with custom key that handles mixed types (int/str) in tuples
        # Convert each element to (type_priority, str_value) for comparison
        def sort_key(value_tuple):
            return tuple(
                (0 if isinstance(v, (int, float)) else 1, str(v))
                for v in value_tuple
            )

        return sorted(unique_values, key=sort_key)

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
                                  frame_values: List[tuple] = None,
                                  component_names_metadata: Dict[str, Any] = None):
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
            channel_values=channel_values, slice_values=slice_values, frame_values=frame_values,
            component_names_metadata=component_names_metadata
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

    def _create_dimension_label_overlay(self, imp, channel_components: List[str], slice_components: List[str],
                                       frame_components: List[str], channel_values: List[tuple],
                                       slice_values: List[tuple], frame_values: List[tuple],
                                       component_names_metadata: Dict[str, Any]):
        """
        Create a text overlay showing current dimension labels (like napari's text_overlay).
        
        This creates an actual on-screen text overlay that updates when dimensions change,
        matching napari's behavior.
        
        Args:
            imp: ImagePlus instance
            channel_components: Components mapped to Channel dimension
            slice_components: Components mapped to Slice dimension  
            frame_components: Components mapped to Frame dimension
            channel_values: Channel dimension values
            slice_values: Slice dimension values
            frame_values: Frame dimension values
            component_names_metadata: Dict mapping component names to {id: name} dicts
        """
        import scyjava as sj
        
        try:
            logger.info(f"🏷️  FIJI SERVER: Creating dimension label overlay")
            
            # Component abbreviation mapping
            COMPONENT_ABBREV = {
                "channel": "Ch",
                "z_index": "Z",
                "timepoint": "T",
                "site": "Site",
                "well": "Well"
            }

            # Build label text showing actual component names and values
            label_parts = []

            def add_component_label(comp_name, comp_value):
                """Helper to add a component label with metadata if available."""
                if comp_name in component_names_metadata:
                    metadata_dict = component_names_metadata[comp_name]
                    metadata_name = metadata_dict.get(str(comp_value))
                    if metadata_name and str(metadata_name).lower() != 'none':
                        # Show metadata name (e.g., "Brightfield", "DAPI")
                        label_parts.append(metadata_name)
                    else:
                        # No metadata - use abbreviated component name + index
                        abbrev = COMPONENT_ABBREV.get(comp_name, comp_name)
                        label_parts.append(f"{abbrev} {comp_value}")
                else:
                    # No metadata - use abbreviated component name + index
                    abbrev = COMPONENT_ABBREV.get(comp_name, comp_name)
                    label_parts.append(f"{abbrev} {comp_value}")
            
            # Channel dimension - show actual channel component values
            if channel_components and channel_values:
                current_channel = imp.getChannel()  # 1-indexed
                if 0 < current_channel <= len(channel_values):
                    channel_tuple = channel_values[current_channel - 1]
                    for comp_idx, comp_name in enumerate(channel_components):
                        comp_value = channel_tuple[comp_idx]
                        add_component_label(comp_name, comp_value)
            
            # Slice dimension - show actual slice component values
            if slice_components and slice_values:
                current_slice = imp.getSlice()  # 1-indexed
                if 0 < current_slice <= len(slice_values):
                    slice_tuple = slice_values[current_slice - 1]
                    for comp_idx, comp_name in enumerate(slice_components):
                        comp_value = slice_tuple[comp_idx]
                        add_component_label(comp_name, comp_value)
            
            # Frame dimension - show actual frame component values (well, site, timepoint, etc.)
            if frame_components and frame_values:
                current_frame = imp.getFrame()  # 1-indexed
                if 0 < current_frame <= len(frame_values):
                    frame_tuple = frame_values[current_frame - 1]
                    for comp_idx, comp_name in enumerate(frame_components):
                        comp_value = frame_tuple[comp_idx]
                        add_component_label(comp_name, comp_value)
            
            if not label_parts:
                logger.info(f"🏷️  FIJI SERVER: No dimensions to label (no channels/slices/frames)")
                # Still create a test overlay to verify the mechanism works
                label_parts = ["TEST OVERLAY"]
            
            label_text = " | ".join(label_parts)
            logger.info(f"🏷️  FIJI SERVER: Creating overlay with text: '{label_text}'")
            
            # Create text overlay using ImageJ Overlay API
            TextRoi = sj.jimport('ij.gui.TextRoi')
            Overlay = sj.jimport('ij.gui.Overlay')
            Font = sj.jimport('java.awt.Font')
            Color = sj.jimport('java.awt.Color')
            
            # Position text in top-left corner
            x = 10
            y = 20
            
            # Create text ROI with white fill color
            text_roi = TextRoi(x, y, label_text)
            text_roi.setFont(Font("SansSerif", Font.BOLD, 16))
            
            # Set fill color to white (this is what shows)
            text_roi.setFillColor(Color.WHITE)
            # Set stroke (outline) color to black for contrast
            text_roi.setStrokeColor(Color.BLACK)
            text_roi.setStrokeWidth(2.0)
            
            # Create or get overlay
            overlay = imp.getOverlay()
            if overlay is None:
                overlay = Overlay()
            
            # Clear any existing overlays first
            overlay.clear()
            
            # Add text ROI to overlay
            overlay.add(text_roi)
            imp.setOverlay(overlay)
            
            logger.info(f"🏷️  FIJI SERVER: Text overlay created successfully with white text")
            
            # Add listener to update overlay when hyperstack position changes
            self._add_dimension_change_listener(imp, channel_components, slice_components, frame_components,
                                               channel_values, slice_values, frame_values,
                                               component_names_metadata)
            
        except Exception as e:
            logger.error(f"🏷️  FIJI SERVER: Failed to create dimension label overlay: {e}", exc_info=True)
    
    def _add_dimension_change_listener(self, imp, channel_components: List[str], slice_components: List[str],
                                      frame_components: List[str], channel_values: List[tuple],
                                      slice_values: List[tuple], frame_values: List[tuple],
                                      component_names_metadata: Dict[str, Any]):
        """
        Add a listener to update the text overlay when hyperstack position changes.
        
        Uses AdjustmentListener on the StackWindow scrollbars to detect dimension changes.
        Based on ImageJ source: ij.gui.StackWindow implements AdjustmentListener for its scrollbars.
        """
        import scyjava as sj
        import jpype
        
        try:
            # Component abbreviation mapping
            COMPONENT_ABBREV = {
                "channel": "Ch",
                "z_index": "Z",
                "timepoint": "T",
                "site": "Site",
                "well": "Well"
            }

            # Helper function to build label text from current position
            def build_label_text():
                label_parts = []

                def add_component_label(comp_name, comp_value):
                    """Helper to add a component label with metadata if available."""
                    if comp_name in component_names_metadata:
                        metadata_dict = component_names_metadata[comp_name]
                        metadata_name = metadata_dict.get(str(comp_value))
                        if metadata_name and str(metadata_name).lower() != 'none':
                            # Use metadata name (e.g., "DAPI")
                            label_parts.append(metadata_name)
                        else:
                            # No metadata - use abbreviated component name + index
                            abbrev = COMPONENT_ABBREV.get(comp_name, comp_name)
                            label_parts.append(f"{abbrev} {comp_value}")
                    else:
                        # No metadata - use abbreviated component name + index
                        abbrev = COMPONENT_ABBREV.get(comp_name, comp_name)
                        label_parts.append(f"{abbrev} {comp_value}")

                # Channel
                if channel_components and channel_values:
                    current_channel = imp.getChannel()
                    if 0 < current_channel <= len(channel_values):
                        channel_tuple = channel_values[current_channel - 1]
                        for comp_idx, comp_name in enumerate(channel_components):
                            add_component_label(comp_name, channel_tuple[comp_idx])

                # Slice
                if slice_components and slice_values:
                    current_slice = imp.getSlice()
                    if 0 < current_slice <= len(slice_values):
                        slice_tuple = slice_values[current_slice - 1]
                        for comp_idx, comp_name in enumerate(slice_components):
                            add_component_label(comp_name, slice_tuple[comp_idx])

                # Frame
                if frame_components and frame_values:
                    current_frame = imp.getFrame()
                    if 0 < current_frame <= len(frame_values):
                        frame_tuple = frame_values[current_frame - 1]
                        for comp_idx, comp_name in enumerate(frame_components):
                            add_component_label(comp_name, frame_tuple[comp_idx])

                return " | ".join(label_parts) if label_parts else "TEST OVERLAY"
            
            # Helper function to update overlay text
            def update_overlay():
                try:
                    label_text = build_label_text()
                    logger.info(f"🔄 FIJI SERVER: Updating overlay text to: '{label_text}'")

                    TextRoi = sj.jimport('ij.gui.TextRoi')
                    Overlay = sj.jimport('ij.gui.Overlay')
                    Font = sj.jimport('java.awt.Font')
                    Color = sj.jimport('java.awt.Color')

                    text_roi = TextRoi(10, 20, label_text)
                    text_roi.setFont(Font("SansSerif", Font.BOLD, 16))
                    text_roi.setFillColor(Color.WHITE)
                    text_roi.setStrokeColor(Color.BLACK)
                    text_roi.setStrokeWidth(2.0)

                    overlay = Overlay()
                    overlay.add(text_roi)
                    imp.setOverlay(overlay)
                    # Force canvas repaint - this triggers the overlay redraw
                    canvas = imp.getCanvas()
                    if canvas is not None:
                        canvas.repaint()
                    logger.info(f"🔄 FIJI SERVER: Overlay updated successfully")
                except Exception as e:
                    logger.error(f"🔄 FIJI SERVER: Error updating overlay: {e}", exc_info=True)
            
            # Get the StackWindow and add AdjustmentListener to its scrollbars
            window = imp.getWindow()
            if window is not None:
                try:
                    # Define listener class using jpype @JImplements decorator
                    @jpype.JImplements('java.awt.event.AdjustmentListener')
                    class DimensionScrollbarListener:
                        @jpype.JOverride
                        def adjustmentValueChanged(self, event):
                            # Called when user scrolls through C/Z/T dimensions
                            update_overlay()
                    
                    listener = DimensionScrollbarListener()

                    # StackWindow has cSelector, zSelector, tSelector scrollbars
                    # ImageJ only creates scrollbars when that dimension > 1
                    # Note: hasattr() doesn't work with JPype Java fields, must access directly
                    added = []

                    logger.info(f"🏷️  FIJI SERVER: Window type: {type(window).__name__}")
                    logger.info(f"🏷️  FIJI SERVER: Hyperstack: {imp.getNChannels()}C x {imp.getNSlices()}Z x {imp.getNFrames()}T")

                    # Scrollbars are AWT components, not fields
                    # Find all ScrollbarWithLabel components and attach listeners
                    import scyjava as sj
                    try:
                        components = window.getComponents()
                        logger.info(f"🏷️  FIJI SERVER: Window has {len(components)} components")

                        scrollbar_count = 0
                        for i, comp in enumerate(components):
                            comp_type = type(comp).__name__
                            logger.info(f"🏷️  FIJI SERVER:   Component {i}: {comp_type}")

                            # ScrollbarWithLabel is the hyperstack dimension scrollbar
                            if 'ScrollbarWithLabel' in comp_type:
                                try:
                                    # Just attach listener to all scrollbars
                                    # The update_overlay() function will read current position from imp
                                    comp.addAdjustmentListener(listener)
                                    scrollbar_count += 1
                                    added.append(f'scrollbar_{i}')
                                    logger.info(f"🏷️  FIJI SERVER:     Added listener to scrollbar {i}")
                                except Exception as e:
                                    logger.warning(f"🏷️  FIJI SERVER:     Could not attach listener: {e}")

                        logger.info(f"🏷️  FIJI SERVER: Attached listeners to {scrollbar_count} scrollbars")
                    except Exception as e:
                        logger.warning(f"🏷️  FIJI SERVER: Could not enumerate components: {e}")

                    if added:
                        logger.info(f"🏷️  FIJI SERVER: Added scrollbar listeners for: {', '.join(added)}")
                    else:
                        logger.warning(f"🏷️  FIJI SERVER: No scrollbars found to attach listener (not a hyperstack?)")
                    
                except Exception as e:
                    logger.warning(f"Could not add scrollbar listeners: {e}", exc_info=True)
            else:
                logger.warning(f"🏷️  FIJI SERVER: No window found, cannot add listeners")
            
        except Exception as e:
            logger.error(f"🏷️  FIJI SERVER: Failed to add dimension change listener: {e}", exc_info=True)
    
    def _set_dimension_labels(self, imp, channel_components: List[str], slice_components: List[str],
                              frame_components: List[str], channel_values: List[tuple],
                              slice_values: List[tuple], frame_values: List[tuple],
                              component_names_metadata: Dict[str, Any]):
        """
        Set dimension labels on ImagePlus using component metadata.
        
        Sets both:
        1. ImageJ property metadata (for channel selector UI)
        2. Text overlay (for on-screen display like napari)
        
        Args:
            imp: ImagePlus instance
            channel_components: Components mapped to Channel dimension
            slice_components: Components mapped to Slice dimension  
            frame_components: Components mapped to Frame dimension
            channel_values: Channel dimension values
            slice_values: Slice dimension values
            frame_values: Frame dimension values
            component_names_metadata: Dict mapping component names to {id: name} dicts
        """
        try:
            logger.info(f"🏷️  FIJI SERVER: _set_dimension_labels called with {len(channel_values) if channel_values else 0} channels")
            logger.info(f"🏷️  FIJI SERVER: channel_components = {channel_components}")
            logger.info(f"🏷️  FIJI SERVER: component_names_metadata = {component_names_metadata}")
            
            # Set channel labels
            if channel_components and channel_values:
                logger.info(f"🏷️  FIJI SERVER: Setting labels for {len(channel_values)} channels")
                for idx, channel_tuple in enumerate(channel_values, start=1):
                    # Build label from component metadata
                    label_parts = []
                    for comp_idx, comp_name in enumerate(channel_components):
                        comp_value = str(channel_tuple[comp_idx])
                        # Try to get metadata name for this component value
                        if comp_name in component_names_metadata:
                            metadata_dict = component_names_metadata[comp_name]
                            metadata_name = metadata_dict.get(comp_value)
                            logger.debug(f"🏷️  Found metadata for {comp_name}[{comp_value}]: {metadata_name}")
                            if metadata_name and str(metadata_name).lower() != 'none':
                                # Use metadata name (e.g., "DAPI")
                                label_parts.append(metadata_name)
                            else:
                                # No metadata - use abbreviated component name + index
                                if comp_name == "channel":
                                    label_parts.append(f"Ch {comp_value}")
                                elif comp_name == "z_index":
                                    label_parts.append(f"Z {comp_value}")
                                elif comp_name == "timepoint":
                                    label_parts.append(f"T {comp_value}")
                                elif comp_name == "site":
                                    label_parts.append(f"Site {comp_value}")
                                else:
                                    label_parts.append(f"{comp_name} {comp_value}")
                        else:
                            # No metadata - use abbreviated component name + index
                            if comp_name == "channel":
                                label_parts.append(f"Ch {comp_value}")
                            elif comp_name == "z_index":
                                label_parts.append(f"Z {comp_value}")
                            elif comp_name == "timepoint":
                                label_parts.append(f"T {comp_value}")
                            elif comp_name == "site":
                                label_parts.append(f"Site {comp_value}")
                            else:
                                label_parts.append(f"{comp_name} {comp_value}")

                    # Set the label property (ImageJ uses "Label1", "Label2", etc. for channels)
                    label = " | ".join(label_parts) if label_parts else f"Ch{idx}"
                    imp.setProperty(f"Label{idx}", label)
                    logger.info(f"🏷️  FIJI SERVER: Set channel {idx} label: '{label}' (property key: 'Label{idx}')")
                    
                    # Verify the property was set
                    verified_label = imp.getProperty(f"Label{idx}")
                    logger.info(f"🏷️  FIJI SERVER: Verified channel {idx} label: '{verified_label}'")
            
            # Note: ImageJ doesn't have built-in properties for slice/frame labels like it does for channels
            # Those would require custom overlays or other visualization methods
            
        except Exception as e:
            logger.warning(f"Failed to set dimension labels: {e}", exc_info=True)

    def _build_new_hyperstack(self, all_images: List[Dict[str, Any]], window_key: str,
                               channel_components: List[str], slice_components: List[str],
                               frame_components: List[str], display_config_dict: Dict[str, Any],
                               is_new: bool, preserved_display_ranges: List[tuple] = None,
                               channel_values: List[tuple] = None,
                               slice_values: List[tuple] = None,
                               frame_values: List[tuple] = None,
                               component_names_metadata: Dict[str, Any] = None):
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

        # Set dimension labels from metadata (e.g., channel names like "DAPI", "GFP")
        logger.info(f"🏷️  FIJI SERVER: component_names_metadata = {component_names_metadata}")
        
        # Note: Text overlay will be created AFTER imp.show() so the window exists for listeners
        
        title_suffix = ""
        if component_names_metadata:
            logger.info(f"🏷️  FIJI SERVER: Setting dimension labels for {window_key}")
            # Set property metadata for channel selector UI
            self._set_dimension_labels(imp, channel_components, slice_components, frame_components,
                                      channel_values, slice_values, frame_values,
                                      component_names_metadata)
            
            # For single-channel images, add channel name to window title since no slider appears
            if nChannels == 1 and channel_components and channel_values:
                first_comp = channel_components[0]
                # channel_values is a list of tuples, e.g., [(1,)]
                first_value_tuple = channel_values[0]
                first_value_str = str(first_value_tuple[0])
                
                if first_comp in component_names_metadata:
                    comp_metadata = component_names_metadata[first_comp]
                    if first_value_str in comp_metadata:
                        channel_name = comp_metadata[first_value_str]
                        if channel_name and str(channel_name).lower() != 'none':
                            title_suffix = f" [{channel_name}]"
                            logger.info(f"🏷️  FIJI SERVER: Adding channel name to window title: {title_suffix}")
        else:
            logger.info(f"🏷️  FIJI SERVER: No component_names_metadata available for {window_key}")
        
        # Update window title with suffix if present
        if title_suffix:
            imp.setTitle(f"{window_key}{title_suffix}")

        # Apply display settings
        lut_name = display_config_dict.get('lut', 'Grays')
        auto_contrast = display_config_dict.get('auto_contrast', True)
        # Only apply auto-contrast for NEW hyperstacks; for updates, use preserved ranges
        # This avoids expensive O(n²) recalculation when adding slices incrementally
        self._apply_display_settings(
            imp, lut_name, auto_contrast if is_new else False, nChannels,
            preserved_ranges=None if is_new else preserved_display_ranges
        )

        # Close old hyperstack if rebuilding
        if window_key in self.hyperstacks:
            self.hyperstacks[window_key].close()

        # Store BEFORE showing to prevent race condition where next batch arrives
        # before hyperstack is registered, causing duplicate window creation
        self.hyperstacks[window_key] = imp
        self.hyperstack_metadata[window_key] = all_images

        # Show after storing (imp.show() may be async on Swing thread)
        imp.show()

        logger.info(f"🔬 FIJI SERVER: Displayed hyperstack '{window_key}' with {stack.getSize()} slices")

        # NOW create text overlay AFTER window exists (so listeners can be attached)
        logger.info(f"🏷️  FIJI SERVER: Creating dimension label overlay for {window_key}")
        self._create_dimension_label_overlay(imp, channel_components, slice_components, frame_components,
                                            channel_values, slice_values, frame_values,
                                            component_names_metadata or {})

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
                               frame_values: List[tuple],
                               component_names_metadata: Dict[str, Any] = None):
    """
    Handle images for a window group.

    Builds or updates ImageJ hyperstack using shared coordinate space.
    """
    # Items may already have 'data' (from debounced processing) or 'shm_name' (direct processing)
    # Convert to standard format expected by hyperstack builder
    image_data_list = []
    for item in items:
        if 'data' in item:
            # Already copied from shared memory (debounced path)
            image_data_list.append({
                'data': item['data'],
                'metadata': item.get('metadata', {}),
                'image_id': item.get('image_id')
            })
        elif 'shm_name' in item:
            # Need to load from shared memory (direct path - shouldn't happen with debouncing)
            loaded = self.load_images_from_shared_memory([item], error_callback=self._send_ack)
            image_data_list.extend(loaded)

    if not image_data_list:
        return

    # Delegate to existing hyperstack building logic
    # Pass dimension values so it uses shared coordinate space
    self._build_single_hyperstack(
        window_key, image_data_list, display_config_dict,
        channel_components, slice_components, frame_components,
        channel_values, slice_values, frame_values,
        component_names_metadata
    )


@register_fiji_handler(StreamingDataType.ROIS)
def _handle_rois_for_window(self, window_key: str, items: List[Dict[str, Any]],
                             display_config_dict: Dict[str, Any],
                             channel_components: List[str],
                             slice_components: List[str],
                             frame_components: List[str],
                             channel_values: List[tuple],
                             slice_values: List[tuple],
                             frame_values: List[tuple],
                             component_names_metadata: Dict[str, Any] = None):
    """
    Handle ROIs for a window group.

    Adds ROIs to ROI Manager with proper CZT positioning using shared coordinate space.
    ROIs are grouped by window_key to associate with corresponding hyperstack.
    """
    from openhcs.runtime.roi_converters import FijiROIConverter
    import scyjava as sj

    # Get or create RoiManager - MUST be done on EDT to avoid Swing threading issues
    RoiManager = sj.jimport('ij.plugin.frame.RoiManager')

    # Try to get existing instance first (doesn't require EDT)
    rm = RoiManager.getInstance()

    # If no instance exists, create one on EDT
    if rm is None:
        # Import JPype only when needed (not at module level to avoid import errors in OMERO tests)
        try:
            from jpype import JImplements, JOverride
        except ImportError:
            # Fallback: create RoiManager directly (may cause EDT issues with IPC mode)
            logger.warning("JPype not available, creating RoiManager without EDT safety (may fail with IPC mode)")
            rm = RoiManager()
        else:
            SwingUtilities = sj.jimport('javax.swing.SwingUtilities')

            # Use a holder to get the RoiManager out of the Runnable
            rm_holder = [None]

            # Create a Java Runnable using JPype's JImplements decorator
            # Note: Decorators are evaluated at class definition time, but since this is
            # inside an if block that only executes when rm is None, it's safe
            @JImplements('java.lang.Runnable')
            class CreateRoiManagerRunnable:
                @JOverride
                def run(self):
                    rm_holder[0] = RoiManager()

            # Execute on EDT and wait
            SwingUtilities.invokeAndWait(CreateRoiManagerRunnable())
            rm = rm_holder[0]

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


def _fiji_viewer_server_process(port: int, viewer_title: str, display_config, log_file_path: str = None, transport_mode: TransportMode = TransportMode.IPC):
    """
    Fiji viewer server process function.

    Runs in separate process to manage Fiji instance and handle incoming image data.

    Args:
        port: ZMQ port to listen on
        viewer_title: Title for the Fiji viewer window
        display_config: FijiDisplayConfig instance
        log_file_path: Path to log file (for client discovery via ping/pong)
        transport_mode: ZMQ transport mode (IPC or TCP)
    """
    try:
        import zmq

        # Create ZMQ server instance (inherits from ZMQServer ABC)
        server = FijiViewerServer(port, viewer_title, display_config, log_file_path, transport_mode)
        
        # Start the server (binds sockets, initializes PyImageJ)
        server.start()
        
        logger.info(f"🔬 FIJI SERVER: Server started on port {port}, control port {port + 1000}")
        logger.info("🔬 FIJI SERVER: Waiting for images...")

        # Message processing loop
        # REP socket requires sending reply after each receive (synchronous request/reply)
        while not server._shutdown_requested:
            # Process control messages (ping/pong handled by ABC)
            server.process_messages()

            # Process data messages (images) if ready
            if server._ready:
                # REP socket is synchronous - process one message at a time
                # Worker blocks until we send reply, ensuring no shared memory race conditions
                try:
                    message = server.data_socket.recv(zmq.NOBLOCK)

                    # Process the message and get acknowledgment
                    ack_response = server.process_image_message(message)

                    # Send acknowledgment back to worker (REP socket requires reply)
                    # Worker will only close shared memory after receiving this
                    server.data_socket.send_json(ack_response)
                    logger.info(f"🔬 FIJI SERVER: Sent ack to worker: {ack_response['status']}")

                except zmq.Again:
                    # No messages available
                    pass

            time.sleep(0.001)  # 1ms sleep - faster polling for multiprocessing
        
        logger.info("🔬 FIJI SERVER: Shutting down...")
        server.stop()
        
    except Exception as e:
        logger.error(f"🔬 FIJI SERVER: Error: {e}")
        import traceback
        traceback.print_exc()
    finally:
        logger.info("🔬 FIJI SERVER: Process terminated")

