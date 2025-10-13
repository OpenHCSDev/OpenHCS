"""
Fiji viewer server for OpenHCS.

ZMQ-based server that receives images from FijiStreamingBackend and displays them
via PyImageJ. Inherits from ZMQServer ABC for ping/pong handshake and dual-channel pattern.
"""

import logging
import time
from typing import Dict, Any, Optional
from pathlib import Path

from openhcs.runtime.zmq_base import ZMQServer

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
        self.images = {}  # Track displayed images by layer name
        self.component_groups = {}  # Track component groupings
        self._shutdown_requested = False
    
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
            logger.info(f"🔬 FIJI SERVER: PyImageJ initialized and UI shown")
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
            logger.info(f"🔬 FIJI SERVER: {msg_type} requested, closing viewer")
            self.request_shutdown()
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
        
        Args:
            message: Raw ZMQ message containing image data
        """
        import json
        import numpy as np
        from multiprocessing import shared_memory
        
        # Parse JSON message
        data = json.loads(message.decode('utf-8'))
        
        # Check if this is a batch message
        if data.get('type') == 'batch':
            images = data.get('images', [])
            display_config_dict = data.get('display_config', {})
            
            for image_info in images:
                self._process_single_image(image_info, display_config_dict)
        else:
            self._process_single_image(data, data.get('display_config', {}))
    
    def _process_single_image(self, image_info: Dict[str, Any], display_config_dict: Dict[str, Any]):
        """Process and display a single image via PyImageJ."""
        import numpy as np
        from multiprocessing import shared_memory

        # Extract image data from shared memory
        shm_name = image_info.get('shm_name')
        shape = tuple(image_info.get('shape'))
        dtype = np.dtype(image_info.get('dtype'))

        try:
            shm = shared_memory.SharedMemory(name=shm_name)
            np_data = np.ndarray(shape, dtype=dtype, buffer=shm.buf).copy()
            shm.close()
        except Exception as e:
            logger.error(f"🔬 FIJI SERVER: Failed to read shared memory {shm_name}: {e}")
            return

        # Extract metadata
        component_metadata = image_info.get('component_metadata', {})
        step_name = image_info.get('step_name', 'unknown')
        path = image_info.get('path', 'unknown')

        # Build stack name and slice label from component metadata
        stack_name, slice_label = self._build_stack_name_and_label(component_metadata, step_name, display_config_dict)

        # Apply display config
        lut_name = display_config_dict.get('lut', 'gray')
        auto_contrast = display_config_dict.get('auto_contrast', True)

        # Convert to ImageJ format and display
        try:
            # Check if stack already exists
            if stack_name in self.images:
                # Add to existing stack
                existing_imp = self.images[stack_name]
                stack = existing_imp.getStack()

                # Convert numpy to ImageProcessor for this slice
                new_imp = self.ij.py.to_imageplus(np_data)
                new_processor = new_imp.getProcessor()

                # Add slice to existing stack
                stack.addSlice(slice_label or f"slice_{stack.getSize() + 1}", new_processor)

                # Update the ImagePlus with the new stack
                existing_imp.setStack(stack)
                existing_imp.updateAndDraw()

                logger.debug(f"🔬 FIJI SERVER: Added slice to {stack_name} (slice: {slice_label}, total: {stack.getSize()})")
            else:
                # Create new stack
                imp = self.ij.py.to_imageplus(np_data)
                imp.setTitle(stack_name)

                # Apply LUT if not gray
                if lut_name.lower() != 'gray' and lut_name.lower() != 'grays':
                    try:
                        self.ij.IJ.run(imp, lut_name, "")
                        logger.debug(f"🔬 FIJI SERVER: Applied LUT {lut_name} to {stack_name}")
                    except Exception as e:
                        logger.warning(f"🔬 FIJI SERVER: Failed to apply LUT {lut_name}: {e}")

                # Apply auto-contrast
                if auto_contrast:
                    try:
                        self.ij.IJ.run(imp, "Enhance Contrast", "saturated=0.35")
                        logger.debug(f"🔬 FIJI SERVER: Applied auto-contrast to {stack_name}")
                    except Exception as e:
                        logger.warning(f"🔬 FIJI SERVER: Failed to apply auto-contrast: {e}")

                # Set slice label if provided
                if slice_label:
                    imp.getStack().setSliceLabel(slice_label, 1)

                # Show the image
                imp.show()

                # Store reference
                self.images[stack_name] = imp
                logger.debug(f"🔬 FIJI SERVER: Created new stack {stack_name} (slice: {slice_label})")

        except Exception as e:
            logger.error(f"🔬 FIJI SERVER: Failed to display image {stack_name}: {e}")
    
    def _build_stack_name_and_label(self, component_metadata: Dict[str, Any], step_name: str,
                                      display_config_dict: Dict[str, Any]) -> tuple:
        """
        Build stack name and slice label based on dimension modes.

        Images with same stack name will be grouped together.
        Slice label identifies individual slices within a stack.

        Returns:
            (stack_name, slice_label)
        """
        component_modes = display_config_dict.get('component_modes', {})

        # Components that should be stacked (mode='stack')
        stack_components = []
        # Components that should be sliced (mode='slice')
        slice_components = []

        for key in ['well', 'site', 'channel', 'z_index', 'timepoint']:
            if key in component_metadata:
                value = component_metadata[key]
                mode = component_modes.get(key, 'stack')  # Default to stack

                if mode == 'stack':
                    # STACK mode: different values of this component go into SAME window as different slices
                    # So this component should be in the slice_label (varies within window)
                    slice_components.append(f"{key}={value}")
                else:  # mode == 'slice'
                    # SLICE mode: different values of this component go into SEPARATE windows
                    # So this component should be in the stack_name (defines which window)
                    stack_components.append(f"{key}={value}")

        # Build stack name from step + slice_mode components (these define separate windows)
        stack_parts = [step_name] + stack_components
        stack_name = "_".join(stack_parts) if stack_parts else step_name

        # Build slice label from stack_mode components (these vary within the same window)
        slice_label = "_".join(slice_components) if slice_components else None

        return stack_name, slice_label
    
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
        logger.info(f"🔬 FIJI SERVER: Waiting for images...")
        
        # Message processing loop
        message_count = 0
        loop_count = 0
        while not server._shutdown_requested:
            loop_count += 1
            if loop_count % 1000 == 0:
                logger.debug(f"🔬 FIJI SERVER: Loop iteration {loop_count}, received {message_count} messages")

            # Process control messages (ping/pong handled by ABC)
            server.process_messages()

            # Process data messages (images) if ready
            if server._ready:
                # Process multiple messages per iteration for better throughput
                for _ in range(10):
                    try:
                        message = server.data_socket.recv(zmq.NOBLOCK)
                        message_count += 1
                        logger.info(f"🔬 FIJI SERVER: Received message #{message_count}")
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

