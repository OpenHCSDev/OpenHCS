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
        self.hyperstacks = {}  # Track hyperstacks by (step_name, well) key
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

            if not images:
                return

            # Group images by (step_name, well) for hyperstack creation
            step_name = images[0].get('step_name', 'unknown_step')
            images_by_well = {}

            for image_info in images:
                component_metadata = image_info.get('component_metadata', {})
                well = component_metadata.get('well', 'unknown_well')

                if well not in images_by_well:
                    images_by_well[well] = []
                images_by_well[well].append(image_info)

            # Process each well's images into a hyperstack
            for well, well_images in images_by_well.items():
                self._add_images_to_hyperstack(step_name, well, well_images, display_config_dict)
        else:
            # Single image message (fallback)
            self._add_images_to_hyperstack(
                data.get('step_name', 'unknown_step'),
                data.get('component_metadata', {}).get('well', 'unknown_well'),
                [data],
                data.get('display_config', {})
            )

    def _add_images_to_hyperstack(self, step_name: str, well: str, images: List[Dict[str, Any]],
                                    display_config_dict: Dict[str, Any]):
        """
        Add images to a 5D hyperstack for the given step and well.

        ImageJ hyperstack dimensions:
        - Channels: site * channel (combined)
        - Slices: z_index
        - Frames: timepoint

        Args:
            step_name: Name of the processing step
            well: Well identifier
            images: List of image info dicts with metadata and shared memory names
            display_config_dict: Display configuration (LUT, auto-contrast, etc.)
        """
        import numpy as np
        from multiprocessing import shared_memory

        hyperstack_key = (step_name, well)

        # Load all images from shared memory
        image_data_list = []
        for image_info in images:
            shm_name = image_info.get('shm_name')
            shape = tuple(image_info.get('shape'))
            dtype = np.dtype(image_info.get('dtype'))
            component_metadata = image_info.get('component_metadata', {})

            try:
                shm = shared_memory.SharedMemory(name=shm_name)
                np_data = np.ndarray(shape, dtype=dtype, buffer=shm.buf).copy()
                shm.close()
                shm.unlink()  # Clean up shared memory

                image_data_list.append({
                    'data': np_data,
                    'metadata': component_metadata
                })
            except Exception as e:
                logger.error(f"🔬 FIJI SERVER: Failed to read shared memory {shm_name}: {e}")
                continue

        if not image_data_list:
            return

        # Organize images by dimensions (site, channel, z_index, timepoint)
        # Build dimension indices
        sites = sorted(set(img['metadata'].get('site', 1) for img in image_data_list))
        channels = sorted(set(img['metadata'].get('channel', 1) for img in image_data_list))
        z_indices = sorted(set(img['metadata'].get('z_index', 1) for img in image_data_list))
        timepoints = sorted(set(img['metadata'].get('timepoint', 1) for img in image_data_list))

        # Map values to indices
        site_map = {v: i for i, v in enumerate(sites)}
        channel_map = {v: i for i, v in enumerate(channels)}
        z_map = {v: i for i, v in enumerate(z_indices)}
        time_map = {v: i for i, v in enumerate(timepoints)}

        # ImageJ hyperstack dimensions
        nChannels = len(sites) * len(channels)  # Combine site and channel
        nSlices = len(z_indices)
        nFrames = len(timepoints)

        logger.info(f"🔬 FIJI SERVER: Building hyperstack for {step_name}/{well}: "
                   f"{nChannels}C x {nSlices}Z x {nFrames}T "
                   f"(sites={len(sites)}, channels={len(channels)})")

        # Create ImageStack and add all images in the correct order
        # ImageJ expects: C1Z1T1, C2Z1T1, ..., C1Z2T1, C2Z2T1, ..., C1Z1T2, ...
        from ij import ImageStack

        first_img = image_data_list[0]['data']
        height, width = first_img.shape[-2:]  # Get spatial dimensions

        stack = ImageStack(width, height)

        # Build lookup dict for fast access
        image_lookup = {}
        for img_data in image_data_list:
            meta = img_data['metadata']
            key = (
                meta.get('site', 1),
                meta.get('channel', 1),
                meta.get('z_index', 1),
                meta.get('timepoint', 1)
            )
            image_lookup[key] = img_data['data']

        # Add slices in ImageJ order: iterate T, then Z, then C
        for t_val in timepoints:
            for z_val in z_indices:
                for site_val in sites:
                    for ch_val in channels:
                        key = (site_val, ch_val, z_val, t_val)

                        if key in image_lookup:
                            np_data = image_lookup[key]

                            # Handle 3D data (take middle slice if needed)
                            if np_data.ndim == 3:
                                np_data = np_data[np_data.shape[0] // 2]

                            # Convert to ImageProcessor
                            temp_imp = self.ij.py.to_imageplus(np_data)
                            processor = temp_imp.getProcessor()

                            # Build label
                            label = f"S{site_val}_C{ch_val}_Z{z_val}_T{t_val}"
                            stack.addSlice(label, processor)
                        else:
                            # Add blank slice if missing
                            logger.warning(f"🔬 FIJI SERVER: Missing image for {key}, adding blank slice")
                            from ij.process import ShortProcessor
                            blank = ShortProcessor(width, height)
                            stack.addSlice(f"BLANK_{key}", blank)

        # Create ImagePlus from stack
        from ij import ImagePlus
        title = f"{step_name}_{well}"
        imp = ImagePlus(title, stack)

        # Set hyperstack dimensions
        imp.setDimensions(nChannels, nSlices, nFrames)

        # Convert to CompositeImage if multiple channels
        if nChannels > 1:
            from ij import CompositeImage
            comp = CompositeImage(imp, CompositeImage.COMPOSITE)
            comp.setTitle(title)
            imp = comp

        # Apply LUT and auto-contrast
        lut_name = display_config_dict.get('lut', 'gray')
        auto_contrast = display_config_dict.get('auto_contrast', True)

        if lut_name.lower() not in ['gray', 'grays'] and nChannels == 1:
            try:
                self.ij.IJ.run(imp, lut_name, "")
            except Exception as e:
                logger.warning(f"🔬 FIJI SERVER: Failed to apply LUT {lut_name}: {e}")

        if auto_contrast:
            try:
                self.ij.IJ.run(imp, "Enhance Contrast", "saturated=0.35")
            except Exception as e:
                logger.warning(f"🔬 FIJI SERVER: Failed to apply auto-contrast: {e}")

        # Show or update
        if hyperstack_key in self.hyperstacks:
            # Close old one
            old_imp = self.hyperstacks[hyperstack_key]
            old_imp.close()

        imp.show()
        self.hyperstacks[hyperstack_key] = imp

        logger.info(f"🔬 FIJI SERVER: Displayed hyperstack {title} with {stack.getSize()} slices")

    
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

