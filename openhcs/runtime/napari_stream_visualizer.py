"""
Napari-based real-time visualization module for OpenHCS.

This module provides the NapariStreamVisualizer class for real-time
visualization of tensors during pipeline execution.

Doctrinal Clauses:
- Clause 65 — No Fallback Logic
- Clause 66 — Immutability After Construction
- Clause 88 — No Inferred Capabilities
- Clause 368 — Visualization Must Be Observer-Only
"""

import logging
import multiprocessing
import os
import subprocess
import sys
import threading
import time
import zmq
import numpy as np
from typing import Any, Dict, Optional

from openhcs.io.filemanager import FileManager
from openhcs.utils.import_utils import optional_import
from openhcs.constants.constants import DEFAULT_NAPARI_STREAM_PORT
from openhcs.runtime.zmq_base import ZMQServer, SHARED_ACK_PORT
from openhcs.runtime.zmq_messages import ImageAck

# Optional napari import - this module should only be imported if napari is available
napari = optional_import("napari")
if napari is None:
    raise ImportError(
        "napari is required for NapariStreamVisualizer. "
        "Install it with: pip install 'openhcs[viz]' or pip install napari"
    )


logger = logging.getLogger(__name__)

# Global process management for napari viewer
_global_viewer_process: Optional[multiprocessing.Process] = None
_global_viewer_port: Optional[int] = None
_global_process_lock = threading.Lock()


def _cleanup_global_viewer() -> None:
    """
    Clean up global napari viewer process for test mode.

    This forcibly terminates the napari viewer process to allow pytest to exit.
    Should only be called in test mode.
    """
    global _global_viewer_process

    with _global_process_lock:
        if _global_viewer_process and _global_viewer_process.is_alive():
            logger.info("🔬 VISUALIZER: Terminating napari viewer for test cleanup")
            _global_viewer_process.terminate()
            _global_viewer_process.join(timeout=3)

            if _global_viewer_process.is_alive():
                logger.warning("🔬 VISUALIZER: Force killing napari viewer process")
                _global_viewer_process.kill()
                _global_viewer_process.join(timeout=1)

            _global_viewer_process = None


def _parse_component_info_from_path(path_str: str):
    """
    Fallback component parsing from path (used when component metadata unavailable).

    Args:
        path_str: Path string like 'step_name/A01/s1_c2_z3.tif'

    Returns:
        Dict with basic component info extracted from filename
    """
    try:
        import os
        import re
        filename = os.path.basename(path_str)

        # Basic regex for common patterns
        pattern = r'(?:s(\d+))?(?:_c(\d+))?(?:_z(\d+))?'
        match = re.search(pattern, filename)

        components = {}
        if match:
            site, channel, z_index = match.groups()
            if site:
                components['site'] = site
            if channel:
                components['channel'] = channel
            if z_index:
                components['z_index'] = z_index

        return components
    except Exception:
        return {}


def _handle_component_aware_display(viewer, layers, component_groups, image_data, path,
                                   colormap, display_config, replace_layers, component_metadata=None):
    """
    Handle component-aware display following OpenHCS stacking patterns.

    Creates separate layers for each step and well, with proper component-based stacking.
    Each step gets its own layer. Each well gets its own layer. Components marked as
    SLICE create separate layers, components marked as STACK are stacked together.
    """
    try:
        # Use component metadata from ZMQ message - fail loud if not available
        if not component_metadata:
            raise ValueError(f"No component metadata available for path: {path}")
        component_info = component_metadata

        # Get step information from component metadata
        step_index = component_info.get('step_index', 0)
        step_name = component_info.get('step_name', 'unknown_step')

        # Create step prefix for layer naming
        step_prefix = f"step_{step_index:02d}_{step_name}"

        # Get well identifier (configurable: slice vs stack)
        well_id = component_info.get('well', 'unknown_well')

        # Build component_modes from config (dict or object), default to channel=slice, others=stack
        component_modes = None
        if isinstance(display_config, dict):
            cm = display_config.get('component_modes') or display_config.get('componentModes')
            if isinstance(cm, dict) and cm:
                component_modes = cm
        if component_modes is None:
            # Handle object-like config (NapariDisplayConfig)
            component_modes = {}
            for component in ['site', 'channel', 'z_index', 'well']:
                mode_field = f"{component}_mode"
                if hasattr(display_config, mode_field):
                    mode_value = getattr(display_config, mode_field)
                    component_modes[component] = getattr(mode_value, 'value', str(mode_value))
                else:
                    component_modes[component] = 'slice' if component == 'channel' else 'stack'

        # Create layer grouping key: step_prefix + well + slice_components
        # CRITICAL: Always include well_id to prevent cross-contamination between wells
        # in multiprocessing scenarios. The display mode affects visualization, not grouping.
        layer_key_parts = [step_prefix, well_id]

        # Add slice components to layer key (these create separate layers)
        for component_name, mode in component_modes.items():
            if mode == 'slice' and component_name in component_info and component_name != 'well':
                layer_key_parts.append(f"{component_name}_{component_info[component_name]}")

        layer_key = "_".join(layer_key_parts)

        # Reconcile cached layer/group state with live napari viewer after possible manual deletions
        try:
            current_layer_names = {l.name for l in viewer.layers}
            if layer_key not in current_layer_names:
                # Drop any stale references so we will recreate the layer
                layers.pop(layer_key, None)
                component_groups.pop(layer_key, None)
                logger.debug(f"🔬 NAPARI PROCESS: Reconciling state — '{layer_key}' not in viewer; purged stale caches")
        except Exception:
            # Fail-loud elsewhere; reconciliation is best-effort and must not mask display
            pass

        # Initialize layer group if needed
        if layer_key not in component_groups:
            component_groups[layer_key] = []

        # Add image to layer group
        component_groups[layer_key].append({
            'data': image_data,
            'components': component_info,
            'path': str(path)
        })

        # Get all images for this layer
        layer_images = component_groups[layer_key]

        # Determine if we should stack or use single image
        stack_components = [comp for comp, mode in component_modes.items()
                          if mode == 'stack' and comp in component_info]

        if len(layer_images) == 1:
            # Single image - add directly
            layer_name = layer_key

            # Check if layer exists in actual napari viewer
            existing_layer = None
            for layer in viewer.layers:
                if layer.name == layer_name:
                    existing_layer = layer
                    break

            if existing_layer is not None:
                # Update existing layer
                existing_layer.data = image_data
                layers[layer_name] = existing_layer
                logger.info(f"🔬 NAPARI PROCESS: Updated existing layer {layer_name}")
            else:
                # Create new layer - this should always work for new names
                logger.info(f"🔬 NAPARI PROCESS: Creating new layer {layer_name}, viewer has {len(viewer.layers)} existing layers")
                logger.info(f"🔬 NAPARI PROCESS: Existing layer names: {[layer.name for layer in viewer.layers]}")
                logger.info(f"🔬 NAPARI PROCESS: Image data shape: {image_data.shape}, dtype: {image_data.dtype}")
                logger.info(f"🔬 NAPARI PROCESS: Viewer type: {type(viewer)}")
                try:
                    new_layer = viewer.add_image(image_data, name=layer_name, colormap=colormap)
                    layers[layer_name] = new_layer
                    logger.info(f"🔬 NAPARI PROCESS: Successfully created new layer {layer_name}")
                    logger.info(f"🔬 NAPARI PROCESS: Viewer now has {len(viewer.layers)} layers")
                except Exception as e:
                    logger.error(f"🔬 NAPARI PROCESS: FAILED to create layer {layer_name}: {e}")
                    logger.error(f"🔬 NAPARI PROCESS: Exception type: {type(e)}")
                    import traceback
                    logger.error(f"🔬 NAPARI PROCESS: Traceback: {traceback.format_exc()}")
                    raise
        else:
            # Multiple images - create multi-dimensional array for napari
            try:
                # Check if all images have the same shape
                first_shape = layer_images[0]['data'].shape
                all_same_shape = all(img['data'].shape == first_shape for img in layer_images)

                if not all_same_shape:
                    # Images have different shapes - handle based on config
                    # Get variable size handling mode from config
                    from openhcs.core.config import NapariVariableSizeHandling
                    variable_size_mode = NapariVariableSizeHandling.SEPARATE_LAYERS  # Default

                    if isinstance(display_config, dict):
                        mode_str = display_config.get('variable_size_handling')
                        if mode_str:
                            try:
                                variable_size_mode = NapariVariableSizeHandling(mode_str)
                            except (ValueError, KeyError):
                                pass
                    elif hasattr(display_config, 'variable_size_handling'):
                        mode_value = display_config.variable_size_handling
                        if mode_value is not None:
                            variable_size_mode = mode_value

                    if variable_size_mode == NapariVariableSizeHandling.PAD_TO_MAX:
                        # Pad images to max size
                        logger.info(f"🔬 NAPARI PROCESS: Images in layer {layer_key} have different shapes - padding to max size")

                        # Find max dimensions
                        max_shape = list(first_shape)
                        for img_info in layer_images:
                            img_shape = img_info['data'].shape
                            for i, dim in enumerate(img_shape):
                                max_shape[i] = max(max_shape[i], dim)
                        max_shape = tuple(max_shape)

                        # Pad all images to max shape
                        padded_images = []
                        for img_info in layer_images:
                            img_data = img_info['data']
                            if img_data.shape != max_shape:
                                # Calculate padding for each dimension
                                pad_width = []
                                for i, (current_dim, max_dim) in enumerate(zip(img_data.shape, max_shape)):
                                    pad_before = 0
                                    pad_after = max_dim - current_dim
                                    pad_width.append((pad_before, pad_after))

                                # Pad with zeros
                                padded_data = np.pad(img_data, pad_width, mode='constant', constant_values=0)
                                img_info['data'] = padded_data
                                logger.debug(f"🔬 NAPARI PROCESS: Padded image from {img_data.shape} to {padded_data.shape}")

                        # Continue with normal stacking logic below (all images now have same shape)

                    else:  # SEPARATE_LAYERS mode
                        # Create separate layers per well
                        logger.warning(f"🔬 NAPARI PROCESS: Images in layer {layer_key} have different shapes - creating separate layers per well")

                        # Group by well and create separate layers
                        wells_in_layer = {}
                        for img_info in layer_images:
                            well = img_info['components'].get('well', 'unknown_well')
                            if well not in wells_in_layer:
                                wells_in_layer[well] = []
                            wells_in_layer[well].append(img_info)

                        # Create a layer for each well
                        for well, well_images in wells_in_layer.items():
                            well_layer_name = f"{layer_key}_{well}"

                            # If only one image for this well, add directly
                            if len(well_images) == 1:
                                well_image_data = well_images[0]['data']
                            else:
                                # Stack images for this well (they should have same shape within a well)
                                well_image_stack = [img['data'] for img in well_images]
                                from openhcs.core.memory.stack_utils import stack_slices
                                well_image_data = stack_slices(well_image_stack, memory_type='numpy', gpu_id=0)

                            # Check if layer exists
                            existing_layer = None
                            for layer in viewer.layers:
                                if layer.name == well_layer_name:
                                    existing_layer = layer
                                    break

                            if existing_layer is not None:
                                existing_layer.data = well_image_data
                                layers[well_layer_name] = existing_layer
                                logger.info(f"🔬 NAPARI PROCESS: Updated well-specific layer {well_layer_name} (shape: {well_image_data.shape})")
                            else:
                                new_layer = viewer.add_image(well_image_data, name=well_layer_name, colormap=colormap)
                                layers[well_layer_name] = new_layer
                                logger.info(f"🔬 NAPARI PROCESS: Created well-specific layer {well_layer_name} (shape: {well_image_data.shape})")

                        # Skip the normal stacking logic below
                        return

                # All images have same shape - proceed with normal stacking
                # Sort images by stack components for consistent ordering
                if stack_components:
                    def sort_key(img_info):
                        return tuple(img_info['components'].get(comp, 0) for comp in stack_components)
                    layer_images.sort(key=sort_key)

                # Group images by stack component values to create proper dimensions
                if len(stack_components) == 1:
                    # Single stack component - simple 3D stack
                    image_stack = [img['data'] for img in layer_images]
                    from openhcs.core.memory.stack_utils import stack_slices
                    stacked_data = stack_slices(image_stack, memory_type='numpy', gpu_id=0)
                else:
                    # Multiple stack components - create multi-dimensional array
                    # Get unique values for each stack component
                    component_values = {}
                    for comp in stack_components:
                        values = sorted(set(img['components'].get(comp, 0) for img in layer_images))
                        component_values[comp] = values

                    # Create multi-dimensional array
                    # Shape: (comp1_size, comp2_size, ..., height, width)
                    shape_dims = [len(component_values[comp]) for comp in stack_components]
                    first_img = layer_images[0]['data']
                    full_shape = tuple(shape_dims + list(first_img.shape))
                    stacked_data = np.zeros(full_shape, dtype=first_img.dtype)

                    # Fill the multi-dimensional array
                    for img_info in layer_images:
                        # Get indices for this image
                        indices = []
                        for comp in stack_components:
                            comp_value = img_info['components'].get(comp, 0)
                            comp_index = component_values[comp].index(comp_value)
                            indices.append(comp_index)

                        # Place image in the correct position
                        stacked_data[tuple(indices)] = img_info['data']

                # Update or create stack layer
                layer_name = layer_key

                # Check if layer exists in actual napari viewer
                existing_layer = None
                for layer in viewer.layers:
                    if layer.name == layer_name:
                        existing_layer = layer
                        break

                if existing_layer is not None:
                    # Update existing layer
                    existing_layer.data = stacked_data
                    layers[layer_name] = existing_layer
                    logger.info(f"🔬 NAPARI PROCESS: Updated existing stack layer {layer_name} (shape: {stacked_data.shape})")
                else:
                    # Create new layer - this should always work for new names
                    logger.info(f"🔬 NAPARI PROCESS: Creating new stack layer {layer_name}, viewer has {len(viewer.layers)} existing layers")
                    try:
                        new_layer = viewer.add_image(stacked_data, name=layer_name, colormap=colormap)
                        layers[layer_name] = new_layer
                        logger.info(f"🔬 NAPARI PROCESS: Successfully created new stack layer {layer_name} (shape: {stacked_data.shape})")
                    except Exception as e:
                        logger.error(f"🔬 NAPARI PROCESS: FAILED to create stack layer {layer_name}: {e}")
                        import traceback
                        logger.error(f"🔬 NAPARI PROCESS: Traceback: {traceback.format_exc()}")
                        raise

            except Exception as e:
                logger.error(f"🔬 NAPARI PROCESS: Failed to create stack for layer {layer_key}: {e}")
                import traceback
                logger.error(f"🔬 NAPARI PROCESS: Traceback: {traceback.format_exc()}")
                raise

    except Exception as e:
        import traceback
        logger.error(f"🔬 NAPARI PROCESS: Component-aware display failed for {path}: {e}")
        logger.error(f"🔬 NAPARI PROCESS: Component-aware display traceback: {traceback.format_exc()}")
        raise  # Fail loud - no fallback


class NapariViewerServer(ZMQServer):
    """
    ZMQ server for Napari viewer that receives images from clients.

    Inherits from ZMQServer ABC to get ping/pong, port management, etc.
    Uses SUB socket to receive images from pipeline clients.
    """

    def __init__(self, port: int, viewer_title: str, replace_layers: bool = False, log_file_path: str = None):
        """
        Initialize Napari viewer server.

        Args:
            port: Data port for receiving images (control port will be port + 1000)
            viewer_title: Title for the napari viewer window
            replace_layers: If True, replace existing layers; if False, add new layers
            log_file_path: Path to log file (for client discovery)
        """
        import zmq

        # Initialize with SUB socket for receiving images
        super().__init__(port, host='*', log_file_path=log_file_path, data_socket_type=zmq.SUB)

        self.viewer_title = viewer_title
        self.replace_layers = replace_layers
        self.viewer = None
        self.layers = {}
        self.component_groups = {}

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
            logger.info(f"🔬 NAPARI SERVER: Connected ack socket to port {SHARED_ACK_PORT}")
        except Exception as e:
            logger.warning(f"🔬 NAPARI SERVER: Failed to setup ack socket: {e}")
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
                viewer_type='napari',
                status=status,
                timestamp=time.time(),
                error=error
            )
            self.ack_socket.send_json(ack.to_dict())
            logger.debug(f"🔬 NAPARI SERVER: Sent ack for image {image_id}")
        except Exception as e:
            logger.warning(f"🔬 NAPARI SERVER: Failed to send ack for {image_id}: {e}")

    def _create_pong_response(self) -> Dict[str, Any]:
        """Override to add Napari-specific fields."""
        response = super()._create_pong_response()
        response['viewer'] = 'napari'
        response['openhcs'] = True
        response['server'] = 'NapariViewer'
        return response

    def handle_control_message(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle control messages beyond ping/pong.

        Supported message types:
        - shutdown: Graceful shutdown (closes viewer)
        - force_shutdown: Force shutdown (same as shutdown for Napari)
        """
        msg_type = message.get('type')

        if msg_type == 'shutdown' or msg_type == 'force_shutdown':
            logger.info(f"🔬 NAPARI SERVER: {msg_type} requested, closing viewer")
            self.request_shutdown()

            # Schedule viewer close on Qt event loop to trigger application exit
            # This must be done after sending the response, so we use QTimer.singleShot
            if self.viewer is not None:
                from qtpy import QtCore
                QtCore.QTimer.singleShot(100, self.viewer.close)

            return {
                'type': 'shutdown_ack',
                'status': 'success',
                'message': 'Napari viewer shutting down'
            }

        # Unknown message type
        return {'status': 'ok'}

    def handle_data_message(self, message: Dict[str, Any]):
        """Handle incoming image data - called by process_messages()."""
        # This will be called from the Qt timer
        pass

    def process_image_message(self, message: bytes):
        """
        Process incoming image data message.

        Args:
            message: Raw ZMQ message containing image data
        """
        import json

        # Parse JSON message
        data = json.loads(message.decode('utf-8'))

        # Check if this is a batch message
        if data.get('type') == 'batch':
            # Handle batch of images
            images = data.get('images', [])
            display_config_dict = data.get('display_config')

            for image_info in images:
                self._process_single_image(image_info, display_config_dict)
        else:
            # Handle single image
            self._process_single_image(data, data.get('display_config'))

    def _process_single_image(self, image_info: Dict[str, Any], display_config_dict: Dict[str, Any]):
        """Process a single image and display in Napari."""
        import numpy as np

        path = image_info.get('path', 'unknown')
        image_id = image_info.get('image_id')  # UUID for acknowledgment
        shape = image_info.get('shape')
        dtype = image_info.get('dtype')
        shm_name = image_info.get('shm_name')
        direct_data = image_info.get('data')
        component_metadata = image_info.get('component_metadata', {})

        # Add step information to component metadata
        component_metadata['step_index'] = image_info.get('step_index', 0)
        component_metadata['step_name'] = image_info.get('step_name', 'unknown_step')

        try:
            # Load image data
            if shm_name:
                from multiprocessing import shared_memory
                shm = shared_memory.SharedMemory(name=shm_name)
                image_data = np.ndarray(shape, dtype=dtype, buffer=shm.buf).copy()
                shm.close()
            elif direct_data:
                image_data = np.array(direct_data, dtype=dtype).reshape(shape)
            else:
                logger.warning("🔬 NAPARI PROCESS: No image data in message")
                if image_id:
                    self._send_ack(image_id, status='error', error='No image data in message')
                return

            # Extract colormap
            colormap = 'viridis'
            if display_config_dict and 'colormap' in display_config_dict:
                colormap = display_config_dict['colormap']

            # Component-aware layer management
            _handle_component_aware_display(
                self.viewer, self.layers, self.component_groups, image_data, path,
                colormap, display_config_dict or {}, self.replace_layers, component_metadata
            )

            # Send acknowledgment that image was successfully displayed
            if image_id:
                self._send_ack(image_id, status='success')

        except Exception as e:
            logger.error(f"🔬 NAPARI PROCESS: Failed to process image {path}: {e}")
            if image_id:
                self._send_ack(image_id, status='error', error=str(e))
            raise  # Fail loud


def _napari_viewer_process(port: int, viewer_title: str, replace_layers: bool = False, log_file_path: str = None):
    """
    Napari viewer process entry point. Runs in a separate process.
    Listens for ZeroMQ messages with image data to display.

    Args:
        port: ZMQ port to listen on
        viewer_title: Title for the napari viewer window
        replace_layers: If True, replace existing layers; if False, add new layers with unique names
        log_file_path: Path to log file (for client discovery via ping/pong)
    """
    try:
        import zmq
        import napari

        # Create ZMQ server instance (inherits from ZMQServer ABC)
        server = NapariViewerServer(port, viewer_title, replace_layers, log_file_path)

        # Start the server (binds sockets)
        server.start()

        # Create napari viewer in this process (main thread)
        viewer = napari.Viewer(title=viewer_title, show=True)
        server.viewer = viewer

        # Initialize layers dictionary with existing layers (for reconnection scenarios)
        for layer in viewer.layers:
            server.layers[layer.name] = layer

        logger.info(f"🔬 NAPARI PROCESS: Viewer started on data port {port}, control port {server.control_port}")

        # Add cleanup handler for when viewer is closed
        def cleanup_and_exit():
            logger.info("🔬 NAPARI PROCESS: Viewer closed, cleaning up and exiting...")
            try:
                server.stop()
            except:
                pass
            sys.exit(0)

        # Connect the viewer close event to cleanup
        viewer.window.qt_viewer.destroyed.connect(cleanup_and_exit)

        # Use proper Qt event loop integration
        import sys
        from qtpy import QtWidgets, QtCore

        # Ensure Qt platform is properly set for detached processes
        import os
        if 'QT_QPA_PLATFORM' not in os.environ:
            os.environ['QT_QPA_PLATFORM'] = 'xcb'

        # Disable shared memory for X11 (helps with display issues in detached processes)
        os.environ['QT_X11_NO_MITSHM'] = '1'

        # Get the Qt application
        app = QtWidgets.QApplication.instance()
        if app is None:
            app = QtWidgets.QApplication(sys.argv)

        # Ensure the application DOES quit when the napari window closes
        app.setQuitOnLastWindowClosed(True)

        # Set up a QTimer for message processing
        timer = QtCore.QTimer()

        def process_messages():
            # Process control messages (ping/pong handled by ABC)
            server.process_messages()

            # Process data messages (images) if ready
            if server._ready:
                # Process multiple messages per timer tick for better throughput
                for _ in range(10):  # Process up to 10 messages per tick
                    try:
                        message = server.data_socket.recv(zmq.NOBLOCK)
                        server.process_image_message(message)
                    except zmq.Again:
                        # No more messages available
                        break

        # Connect timer to message processing
        timer.timeout.connect(process_messages)
        timer.start(50)  # Process messages every 50ms

        logger.info("🔬 NAPARI PROCESS: Starting Qt event loop")

        # Run the Qt event loop - this keeps napari responsive
        app.exec_()

    except Exception as e:
        logger.error(f"🔬 NAPARI PROCESS: Fatal error: {e}")
    finally:
        logger.info("🔬 NAPARI PROCESS: Shutting down")
        if 'server' in locals():
            server.stop()


def _spawn_detached_napari_process(port: int, viewer_title: str, replace_layers: bool = False) -> subprocess.Popen:
    """
    Spawn a completely detached napari viewer process that survives parent termination.

    This creates a subprocess that runs independently and won't be terminated when
    the parent process exits, enabling true persistence across pipeline runs.
    """
    # Use a simpler approach: spawn python directly with the napari viewer module
    # This avoids temporary file issues and import problems

    # Create the command to run the napari viewer directly
    current_dir = os.getcwd()
    python_code = f'''
import sys
import os

# Detach from parent process group (Unix only)
if hasattr(os, "setsid"):
    try:
        os.setsid()
    except OSError:
        pass

# Add current working directory to Python path
sys.path.insert(0, "{current_dir}")

try:
    from openhcs.runtime.napari_stream_visualizer import _napari_viewer_process
    _napari_viewer_process({port}, "{viewer_title}", {replace_layers}, "{current_dir}/.napari_log_path_placeholder")
except Exception as e:
    import logging
    logger = logging.getLogger("openhcs.runtime.napari_detached")
    logger.error(f"Detached napari error: {{e}}")
    import traceback
    logger.error(traceback.format_exc())
    sys.exit(1)
'''

    try:
        # Create log file for detached process
        log_dir = os.path.expanduser("~/.local/share/openhcs/logs")
        os.makedirs(log_dir, exist_ok=True)
        log_file = os.path.join(log_dir, f"napari_detached_port_{port}.log")

        # Replace placeholder with actual log file path in python code
        python_code = python_code.replace(f"{current_dir}/.napari_log_path_placeholder", log_file)

        # Use subprocess.Popen with detachment flags
        if sys.platform == "win32":
            # Windows: Use CREATE_NEW_PROCESS_GROUP to detach but preserve display environment
            env = os.environ.copy()  # Preserve environment variables
            with open(log_file, 'w') as log_f:
                process = subprocess.Popen(
                    [sys.executable, "-c", python_code],
                    creationflags=subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.DETACHED_PROCESS,
                    env=env,
                    cwd=os.getcwd(),
                    stdout=log_f,
                    stderr=subprocess.STDOUT
                )
        else:
            # Unix: Use start_new_session to detach but preserve display environment
            env = os.environ.copy()  # Preserve DISPLAY and other environment variables

            # Ensure Qt platform is set for GUI display
            if 'QT_QPA_PLATFORM' not in env:
                env['QT_QPA_PLATFORM'] = 'xcb'  # Use X11 backend

            # Ensure Qt can find the display
            env['QT_X11_NO_MITSHM'] = '1'  # Disable shared memory for X11 (helps with some display issues)

            # Redirect stdout/stderr to log file for debugging
            log_f = open(log_file, 'w')
            process = subprocess.Popen(
                [sys.executable, "-c", python_code],
                env=env,
                cwd=os.getcwd(),
                stdout=log_f,
                stderr=subprocess.STDOUT,
                start_new_session=True  # CRITICAL: Detach from parent process group
            )

        logger.info(f"🔬 VISUALIZER: Detached napari process started (PID: {process.pid}), logging to {log_file}")
        return process

    except Exception as e:
        logger.error(f"🔬 VISUALIZER: Failed to spawn detached napari process: {e}")
        raise e


class NapariStreamVisualizer:
    """
    Manages a Napari viewer instance for real-time visualization of tensors
    streamed from the OpenHCS pipeline. Runs napari in a separate process
    for Qt compatibility and true persistence across pipeline runs.
    """

    def __init__(self, filemanager: FileManager, visualizer_config, viewer_title: str = "OpenHCS Real-Time Visualization", persistent: bool = True, napari_port: int = DEFAULT_NAPARI_STREAM_PORT, replace_layers: bool = False, display_config=None):
        self.filemanager = filemanager
        self.viewer_title = viewer_title
        self.persistent = persistent  # If True, viewer process stays alive after pipeline completion
        self.visualizer_config = visualizer_config
        self.napari_port = napari_port  # Port for napari streaming
        self.replace_layers = replace_layers  # If True, replace existing layers; if False, add new layers
        self.display_config = display_config  # Configuration for display behavior
        self.port: Optional[int] = None
        self.process: Optional[multiprocessing.Process] = None
        self.zmq_context: Optional[zmq.Context] = None
        self.zmq_socket: Optional[zmq.Socket] = None
        self._is_running = False  # Internal flag, use is_running property instead
        self._connected_to_existing = False  # True if connected to viewer we didn't create
        self._lock = threading.Lock()

        # Clause 368: Visualization must be observer-only.
        # This class will only read data and display it.

    @property
    def is_running(self) -> bool:
        """
        Check if the napari viewer is actually running.

        This property checks the actual process state, not just a cached flag.
        Returns True only if the process exists and is alive.
        """
        if not self._is_running:
            return False

        # If we connected to an existing viewer, verify it's still responsive
        if self._connected_to_existing:
            # Quick ping check to verify viewer is still alive
            if not self._quick_ping_check():
                logger.debug(f"🔬 VISUALIZER: Connected viewer on port {self.napari_port} is no longer responsive")
                self._is_running = False
                self._connected_to_existing = False
                return False
            return True

        if self.process is None:
            self._is_running = False
            return False

        # Check if process is actually alive
        try:
            if hasattr(self.process, 'is_alive'):
                # multiprocessing.Process
                alive = self.process.is_alive()
            else:
                # subprocess.Popen
                alive = self.process.poll() is None

            if not alive:
                logger.debug(f"🔬 VISUALIZER: Napari process on port {self.napari_port} is no longer alive")
                self._is_running = False

            return alive
        except Exception as e:
            logger.warning(f"🔬 VISUALIZER: Error checking process status: {e}")
            self._is_running = False
            return False

    def _quick_ping_check(self) -> bool:
        """Quick ping check to verify viewer is responsive (for connected viewers)."""
        import zmq
        import pickle

        try:
            ctx = zmq.Context()
            sock = ctx.socket(zmq.REQ)
            sock.setsockopt(zmq.LINGER, 0)
            sock.setsockopt(zmq.RCVTIMEO, 200)  # 200ms timeout for quick check
            sock.connect(f"tcp://localhost:{self.napari_port + 1000}")
            sock.send(pickle.dumps({'type': 'ping'}))
            response = pickle.loads(sock.recv())
            sock.close()
            ctx.term()
            return response.get('type') == 'pong'
        except:
            return False

    def wait_for_ready(self, timeout: float = 10.0) -> bool:
        """
        Wait for the viewer to be ready to receive images.

        This method blocks until the viewer is responsive or the timeout expires.
        Should be called after start_viewer() when using async_mode=True.

        Args:
            timeout: Maximum time to wait in seconds

        Returns:
            True if viewer is ready, False if timeout
        """
        return self._wait_for_viewer_ready(timeout=timeout)

    def _find_free_port(self) -> int:
        """Find a free port for ZeroMQ communication."""
        import socket
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(('', 0))
            return s.getsockname()[1]

    def start_viewer(self, async_mode: bool = True):
        """
        Starts the Napari viewer in a separate process.

        Args:
            async_mode: If True, start viewer asynchronously in background thread.
                       If False, wait for viewer to be ready before returning (legacy behavior).
        """
        if async_mode:
            # Start viewer asynchronously in background thread
            thread = threading.Thread(target=self._start_viewer_sync, daemon=True)
            thread.start()
            logger.info(f"🔬 VISUALIZER: Starting napari viewer asynchronously on port {self.napari_port}")
        else:
            # Legacy synchronous mode
            self._start_viewer_sync()

    def _start_viewer_sync(self):
        """Internal synchronous viewer startup (called by start_viewer)."""
        global _global_viewer_process, _global_viewer_port

        with self._lock:
            # Check if there's already a napari viewer running on the configured port
            port_in_use = self._is_port_in_use(self.napari_port)
            logger.info(f"🔬 VISUALIZER: Port {self.napari_port} in use: {port_in_use}")

            if port_in_use:
                # Try to connect to existing viewer first before killing it
                logger.info(f"🔬 VISUALIZER: Port {self.napari_port} is in use, attempting to connect to existing viewer...")
                self.port = self.napari_port
                if self._try_connect_to_existing_viewer(self.napari_port):
                    logger.info(f"🔬 VISUALIZER: Successfully connected to existing viewer on port {self.napari_port}")
                    self._is_running = True
                    self._connected_to_existing = True  # Mark that we connected to existing viewer
                    return
                else:
                    # Existing viewer is unresponsive - kill it and start fresh
                    logger.info(f"🔬 VISUALIZER: Existing viewer on port {self.napari_port} is unresponsive, killing and restarting...")
                    # Use shared method from ZMQServer ABC
                    from openhcs.runtime.zmq_base import ZMQServer
                    ZMQServer.kill_processes_on_port(self.napari_port)
                    ZMQServer.kill_processes_on_port(self.napari_port + 1000)
                    # Wait a moment for ports to be freed
                    import time
                    time.sleep(0.5)

            if self._is_running:
                logger.warning("Napari viewer is already running.")
                return 

            # Use configured port for napari streaming
            self.port = self.napari_port
            logger.info(f"🔬 VISUALIZER: Starting napari viewer process on port {self.port}")

            if self.persistent:
                # For persistent viewers, use detached subprocess that truly survives parent termination
                logger.info("🔬 VISUALIZER: Creating detached persistent napari viewer")
                self.process = _spawn_detached_napari_process(self.port, self.viewer_title, self.replace_layers)
                # DON'T track persistent viewers in global variable - they should survive test cleanup
            else:
                # For non-persistent viewers, use multiprocessing.Process
                logger.info("🔬 VISUALIZER: Creating non-persistent napari viewer")
                self.process = multiprocessing.Process(
                    target=_napari_viewer_process,
                    args=(self.port, self.viewer_title, self.replace_layers, None),  # No log file for non-persistent
                    daemon=False
                )
                self.process.start()

                # Only track non-persistent viewers in global variable for test cleanup
                with _global_process_lock:
                    _global_viewer_process = self.process
                    _global_viewer_port = self.port

            # Wait for napari viewer to be ready before setting up ZMQ
            self._wait_for_viewer_ready()

            # Set up ZeroMQ client
            self._setup_zmq_client()

            # Check if process is running (different methods for subprocess vs multiprocessing)
            if hasattr(self.process, 'is_alive'):
                # multiprocessing.Process
                process_alive = self.process.is_alive()
            else:
                # subprocess.Popen
                process_alive = self.process.poll() is None

            if process_alive:
                self._is_running = True
                logger.info(f"🔬 VISUALIZER: Napari viewer process started successfully (PID: {self.process.pid})")
            else:
                logger.error("🔬 VISUALIZER: Failed to start napari viewer process")

    def _try_connect_to_existing_viewer(self, port: int) -> bool:
        """
        Try to connect to an existing napari viewer and verify it's responsive.

        Returns True only if we can successfully handshake with the viewer.
        """
        import zmq
        import pickle

        # Try to ping the control port to verify viewer is responsive
        control_port = port + 1000
        control_context = None
        control_socket = None

        try:
            control_context = zmq.Context()
            control_socket = control_context.socket(zmq.REQ)
            control_socket.setsockopt(zmq.LINGER, 0)
            control_socket.setsockopt(zmq.RCVTIMEO, 500)  # 500ms timeout
            control_socket.connect(f"tcp://localhost:{control_port}")

            # Send ping
            ping_message = {'type': 'ping'}
            control_socket.send(pickle.dumps(ping_message))

            # Wait for pong
            response = control_socket.recv()
            response_data = pickle.loads(response)

            if response_data.get('type') == 'pong' and response_data.get('ready'):
                # Viewer is responsive! Set up our ZMQ client
                control_socket.close()
                control_context.term()
                self._setup_zmq_client()
                return True
            else:
                return False

        except Exception as e:
            logger.debug(f"Failed to connect to existing viewer on port {port}: {e}")
            return False
        finally:
            if control_socket:
                try:
                    control_socket.close()
                except:
                    pass
            if control_context:
                try:
                    control_context.term()
                except:
                    pass



    def _is_port_in_use(self, port: int) -> bool:
        """Check if a port is already in use (indicating existing napari viewer)."""
        import socket

        # Check if any process is listening on this port
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(0.1)
        try:
            # Try to bind to the port - if it fails, something is already using it
            sock.bind(('localhost', port))
            sock.close()
            return False  # Port is free
        except OSError:
            # Port is already in use
            sock.close()
            return True
        except Exception:
            return False

    def _wait_for_viewer_ready(self, timeout: float = 10.0) -> bool:
        """Wait for the napari viewer to be ready using handshake protocol."""
        import zmq

        logger.info(f"🔬 VISUALIZER: Waiting for napari viewer to be ready on port {self.port}...")

        # First wait for ports to be bound
        start_time = time.time()
        while time.time() - start_time < timeout:
            if self._is_port_in_use(self.port) and self._is_port_in_use(self.port + 1000):
                break
            time.sleep(0.2)
        else:
            logger.warning("🔬 VISUALIZER: Timeout waiting for ports to be bound")
            return False

        # Now use handshake protocol - create fresh socket for each attempt
        start_time = time.time()
        while time.time() - start_time < timeout:
            control_context = zmq.Context()
            control_socket = control_context.socket(zmq.REQ)
            control_socket.setsockopt(zmq.LINGER, 0)
            control_socket.setsockopt(zmq.RCVTIMEO, 1000)  # 1 second timeout

            try:
                control_socket.connect(f"tcp://localhost:{self.port + 1000}")

                import pickle
                ping_message = {'type': 'ping'}
                control_socket.send(pickle.dumps(ping_message))

                response = control_socket.recv()
                response_data = pickle.loads(response)

                if response_data.get('type') == 'pong' and response_data.get('ready'):
                    logger.info(f"🔬 VISUALIZER: Napari viewer is ready on port {self.port}")
                    return True

            except zmq.Again:
                pass  # Timeout waiting for response
            except Exception as e:
                logger.debug(f"🔬 VISUALIZER: Handshake attempt failed: {e}")
            finally:
                control_socket.close()
                control_context.term()

            time.sleep(0.5)  # Wait before next ping

        logger.warning("🔬 VISUALIZER: Timeout waiting for napari viewer handshake")
        return False

    def _setup_zmq_client(self):
        """Set up ZeroMQ client to send data to viewer process."""
        if self.port is None:
            raise RuntimeError("Port not set - call start_viewer() first")

        self.zmq_context = zmq.Context()
        self.zmq_socket = self.zmq_context.socket(zmq.PUB)
        self.zmq_socket.connect(f"tcp://localhost:{self.port}")

        # Brief delay for ZMQ connection to establish
        time.sleep(0.1)
        logger.info(f"🔬 VISUALIZER: ZMQ client connected to port {self.port}")

    def send_image_data(self, step_id: str, image_data: np.ndarray, axis_id: str = "unknown"):
        """
        DISABLED: This method bypasses component-aware stacking.
        All visualization must go through the streaming backend.
        """
        raise RuntimeError(
            f"send_image_data() is disabled. Use streaming backend for component-aware display. "
            f"step_id: {step_id}, axis_id: {axis_id}, shape: {image_data.shape}"
        )

    def stop_viewer(self):
        """Stop the napari viewer process (only if not persistent)."""
        with self._lock:
            if not self.persistent:
                logger.info("🔬 VISUALIZER: Stopping non-persistent napari viewer")
                self._cleanup_zmq()
                if self.process:
                    # Handle both subprocess and multiprocessing process types
                    if hasattr(self.process, 'is_alive'):
                        # multiprocessing.Process
                        if self.process.is_alive():
                            self.process.terminate()
                            self.process.join(timeout=5)
                            if self.process.is_alive():
                                logger.warning("🔬 VISUALIZER: Force killing napari viewer process")
                                self.process.kill()
                    else:
                        # subprocess.Popen
                        if self.process.poll() is None:  # Still running
                            self.process.terminate()
                            try:
                                self.process.wait(timeout=5)
                            except subprocess.TimeoutExpired:
                                logger.warning("🔬 VISUALIZER: Force killing napari viewer process")
                                self.process.kill()
                self._is_running = False
            else:
                logger.info("🔬 VISUALIZER: Keeping persistent napari viewer alive")
                # Just cleanup our ZMQ connection, leave process running
                self._cleanup_zmq()
                # DON'T set is_running = False for persistent viewers!
                # The process is still alive and should be reusable

    def _cleanup_zmq(self):
        """Clean up ZeroMQ resources."""
        if self.zmq_socket:
            self.zmq_socket.close()
            self.zmq_socket = None
        if self.zmq_context:
            self.zmq_context.term()
            self.zmq_context = None

    def visualize_path(self, step_id: str, path: str, backend: str, axis_id: Optional[str] = None):
        """
        DISABLED: This method bypasses component-aware stacking.
        All visualization must go through the streaming backend.
        """
        raise RuntimeError(
            f"visualize_path() is disabled. Use streaming backend for component-aware display. "
            f"Path: {path}, step_id: {step_id}, axis_id: {axis_id}"
        )

    def _prepare_data_for_display(self, data: Any, step_id_for_log: str, display_config=None) -> Optional[np.ndarray]:
        """Converts loaded data to a displayable NumPy array (slice or stack based on config)."""
        cpu_tensor: Optional[np.ndarray] = None
        try:
            # GPU to CPU conversion logic
            if hasattr(data, 'is_cuda') and data.is_cuda:  # PyTorch
                cpu_tensor = data.cpu().numpy()
            elif hasattr(data, 'device') and 'cuda' in str(data.device).lower():  # Check for device attribute
                if hasattr(data, 'get'):  # CuPy
                    cpu_tensor = data.get()
                elif hasattr(data, 'numpy'): # JAX on GPU might have .numpy() after host transfer
                    cpu_tensor = np.asarray(data) # JAX arrays might need explicit conversion
                else: # Fallback for other GPU array types if possible
                    logger.warning(f"Unknown GPU array type for step '{step_id_for_log}'. Attempting .numpy().")
                    if hasattr(data, 'numpy'):
                        cpu_tensor = data.numpy()
                    else:
                        logger.error(f"Cannot convert GPU tensor of type {type(data)} for step '{step_id_for_log}'.")
                        return None
            elif isinstance(data, np.ndarray):
                cpu_tensor = data
            else:
                # Attempt to convert to numpy array if it's some other array-like structure
                try:
                    cpu_tensor = np.asarray(data)
                    logger.debug(f"Converted data of type {type(data)} to numpy array for step '{step_id_for_log}'.")
                except Exception as e_conv:
                    logger.warning(f"Unsupported data type for step '{step_id_for_log}': {type(data)}. Error: {e_conv}")
                    return None

            if cpu_tensor is None: # Should not happen if logic above is correct
                return None

            # Determine display mode based on configuration
            # Default behavior: show as stack unless config specifies otherwise
            should_slice = False

            if display_config:
                # Check if any component mode is set to SLICE
                from openhcs.core.config import NapariDimensionMode
                from openhcs.constants import VariableComponents

                # Check individual component mode fields
                for component in VariableComponents:
                    field_name = f"{component.value}_mode"
                    if hasattr(display_config, field_name):
                        mode = getattr(display_config, field_name)
                        if mode == NapariDimensionMode.SLICE:
                            should_slice = True
                            break
            else:
                # Default: slice for backward compatibility
                should_slice = True

            # Slicing/stacking logic
            display_data: Optional[np.ndarray] = None

            if should_slice:
                # Original slicing behavior
                if cpu_tensor.ndim == 3: # ZYX
                    display_data = cpu_tensor[cpu_tensor.shape[0] // 2, :, :]
                elif cpu_tensor.ndim == 2: # YX
                    display_data = cpu_tensor
                elif cpu_tensor.ndim > 3: # e.g. CZYX or TZYX
                    logger.debug(f"Tensor for step '{step_id_for_log}' has ndim > 3 ({cpu_tensor.ndim}). Taking a slice.")
                    slicer = [0] * (cpu_tensor.ndim - 2) # Slice first channels/times
                    slicer[-1] = cpu_tensor.shape[-3] // 2 # Middle Z
                    try:
                        display_data = cpu_tensor[tuple(slicer)]
                    except IndexError: # Handle cases where slicing might fail (e.g. very small dimensions)
                        logger.error(f"Slicing failed for tensor with shape {cpu_tensor.shape} for step '{step_id_for_log}'.", exc_info=True)
                        display_data = None
                else:
                    logger.warning(f"Tensor for step '{step_id_for_log}' has unsupported ndim for slicing: {cpu_tensor.ndim}.")
                    return None
            else:
                # Stack mode: send the full data to napari (napari can handle 3D+ data)
                if cpu_tensor.ndim >= 2:
                    display_data = cpu_tensor
                    logger.debug(f"Sending {cpu_tensor.ndim}D stack to napari for step '{step_id_for_log}' (shape: {cpu_tensor.shape})")
                else:
                    logger.warning(f"Tensor for step '{step_id_for_log}' has unsupported ndim for stacking: {cpu_tensor.ndim}.")
                    return None

            return display_data.copy() if display_data is not None else None

        except Exception as e:
            logger.error(f"Error preparing data from step '{step_id_for_log}' for display: {e}", exc_info=True)
            return None

