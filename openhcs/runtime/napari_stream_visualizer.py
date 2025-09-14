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
import queue
import subprocess
import sys
import threading
import time
import zmq
from typing import Any, Dict, Optional

from openhcs.io.filemanager import FileManager
from openhcs.utils.import_utils import optional_import
from openhcs.constants.constants import DEFAULT_NAPARI_STREAM_PORT

# Optional napari import - this module should only be imported if napari is available
napari = optional_import("napari")
if napari is None:
    raise ImportError(
        "napari is required for NapariStreamVisualizer. "
        "Install it with: pip install 'openhcs[viz]' or pip install napari"
    )

import numpy as np

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

def _napari_viewer_process(port: int, viewer_title: str, replace_layers: bool = False):
    """
    Napari viewer process entry point. Runs in a separate process.
    Listens for ZeroMQ messages with image data to display.

    Args:
        port: ZMQ port to listen on
        viewer_title: Title for the napari viewer window
        replace_layers: If True, replace existing layers; if False, add new layers with unique names
    """
    try:
        import zmq
        import napari
        import numpy as np
        import pickle

        # Set up ZeroMQ communication
        context = zmq.Context()

        # Data channel: SUB socket for receiving images
        data_socket = context.socket(zmq.SUB)
        data_socket.bind(f"tcp://*:{port}")
        data_socket.setsockopt(zmq.SUBSCRIBE, b"")  # Subscribe to all messages

        # Control channel: REP socket for handshake
        control_port = port + 1000  # Use port+1000 for control
        control_socket = context.socket(zmq.REP)
        control_socket.bind(f"tcp://*:{control_port}")

        # Create napari viewer in this process (main thread)
        viewer = napari.Viewer(title=viewer_title, show=True)
        layers = {}
        napari_ready = False  # Track readiness state

        print(f"🔬 NAPARI PROCESS: Viewer started on data port {port}, control port {control_port}")

        # Add cleanup handler for when viewer is closed
        def cleanup_and_exit():
            print("🔬 NAPARI PROCESS: Viewer closed, cleaning up and exiting...")
            try:
                data_socket.close()
                control_socket.close()
                context.term()
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
            nonlocal napari_ready
            try:
                # Handle control messages (handshake) first
                try:
                    control_message = control_socket.recv(zmq.NOBLOCK)
                    control_data = pickle.loads(control_message)

                    if control_data.get('type') == 'ping':
                        # Client is checking if we're ready
                        if not napari_ready:
                            # Mark as ready after first ping (GUI should be loaded by now)
                            napari_ready = True
                            print(f"🔬 NAPARI PROCESS: Marked as ready after ping")

                        response = {'type': 'pong', 'ready': napari_ready}
                        control_socket.send(pickle.dumps(response))
                        print(f"🔬 NAPARI PROCESS: Responded to ping with ready={napari_ready}")

                except zmq.Again:
                    pass  # No control messages

                # Debug: Print current layer count (only when layers change)
                # Removed continuous debug printing to avoid terminal spam

                # Process data messages only if ready
                if napari_ready:
                    # Process multiple messages per timer tick for better throughput
                    for _ in range(10):  # Process up to 10 messages per tick
                        try:
                            message = data_socket.recv(zmq.NOBLOCK)

                            # Try to parse as JSON first (from NapariStreamingBackend)
                            try:
                                import json
                                data = json.loads(message.decode('utf-8'))

                                # Handle streaming backend format
                                path = data.get('path', 'unknown')
                                shape = data.get('shape')
                                dtype = data.get('dtype')
                                shm_name = data.get('shm_name')
                                direct_data = data.get('data')

                                if shm_name:
                                    # Load from shared memory
                                    try:
                                        from multiprocessing import shared_memory
                                        shm = shared_memory.SharedMemory(name=shm_name)
                                        image_data = np.ndarray(shape, dtype=dtype, buffer=shm.buf).copy()
                                        shm.close()  # Close our reference
                                    except Exception as e:
                                        print(f"🔬 NAPARI PROCESS: Failed to load shared memory {shm_name}: {e}")
                                        continue
                                elif direct_data:
                                    # Load from direct data (fallback)
                                    image_data = np.array(direct_data, dtype=dtype).reshape(shape)
                                else:
                                    print(f"🔬 NAPARI PROCESS: No image data in message")
                                    continue

                                # Extract step info from path
                                layer_name = str(path).replace('/', '_').replace('\\', '_')

                            except (json.JSONDecodeError, UnicodeDecodeError):
                                # Try to parse as pickle (from direct visualizer calls)
                                data = pickle.loads(message)

                                step_id = data.get('step_id', 'unknown')
                                image_data = data.get('image_data')
                                axis_id = data.get('axis_id', 'unknown')
                                layer_name = f"{step_id}_{axis_id}"

                                if image_data is None:
                                    continue

                            # Handle layer management based on replace_layers setting
                            if replace_layers and layer_name in layers:
                                # Replace existing layer data
                                layers[layer_name].data = image_data
                                print(f"🔬 NAPARI PROCESS: Replaced layer {layer_name}")
                            else:
                                # Add new layer (or create if doesn't exist)
                                if layer_name in layers:
                                    # Create unique name for new layer
                                    import time
                                    timestamp = int(time.time() * 1000) % 100000  # Last 5 digits of timestamp
                                    unique_layer_name = f"{layer_name}_{timestamp}"
                                else:
                                    unique_layer_name = layer_name

                                layers[unique_layer_name] = viewer.add_image(
                                    image_data,
                                    name=unique_layer_name,
                                    colormap='viridis'
                                )
                                print(f"🔬 NAPARI PROCESS: Added layer {unique_layer_name} (total layers: {len(layers)})")

                        except zmq.Again:
                            # No more messages available
                            break

            except Exception as e:
                print(f"🔬 NAPARI PROCESS: Error processing message: {e}")

        # Connect timer to message processing
        timer.timeout.connect(process_messages)
        timer.start(50)  # Process messages every 50ms

        print("🔬 NAPARI PROCESS: Starting Qt event loop")

        # Run the Qt event loop - this keeps napari responsive
        app.exec_()

    except Exception as e:
        print(f"🔬 NAPARI PROCESS: Fatal error: {e}")
    finally:
        print("🔬 NAPARI PROCESS: Shutting down")
        if 'socket' in locals():
            socket.close()
        if 'context' in locals():
            context.term()


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
    _napari_viewer_process({port}, "{viewer_title}", {replace_layers})
except Exception as e:
    print(f"Detached napari error: {{e}}")
    import traceback
    traceback.print_exc()
    sys.exit(1)
'''

    try:
        # Use subprocess.Popen with detachment flags
        if sys.platform == "win32":
            # Windows: Use CREATE_NEW_PROCESS_GROUP to detach but preserve display environment
            env = os.environ.copy()  # Preserve environment variables
            process = subprocess.Popen(
                [sys.executable, "-c", python_code],
                creationflags=subprocess.CREATE_NEW_PROCESS_GROUP | subprocess.DETACHED_PROCESS,
                env=env,
                cwd=os.getcwd()
                # Don't redirect stdout/stderr to allow GUI to display properly
            )
        else:
            # Unix: Use start_new_session to detach but preserve display environment
            env = os.environ.copy()  # Preserve DISPLAY and other environment variables

            # Ensure Qt platform is set for GUI display
            if 'QT_QPA_PLATFORM' not in env:
                env['QT_QPA_PLATFORM'] = 'xcb'  # Use X11 backend

            # Ensure Qt can find the display
            env['QT_X11_NO_MITSHM'] = '1'  # Disable shared memory for X11 (helps with some display issues)

            # Try without start_new_session to see if GUI displays properly
            process = subprocess.Popen(
                [sys.executable, "-c", python_code],
                env=env,
                cwd=os.getcwd()
                # Don't redirect stdout/stderr to allow GUI to display properly
            )

        logger.info(f"🔬 VISUALIZER: Detached napari process started (PID: {process.pid})")
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

    def __init__(self, filemanager: FileManager, visualizer_config, viewer_title: str = "OpenHCS Real-Time Visualization", persistent: bool = True, napari_port: int = DEFAULT_NAPARI_STREAM_PORT, replace_layers: bool = False):
        self.filemanager = filemanager
        self.viewer_title = viewer_title
        self.persistent = persistent  # If True, viewer process stays alive after pipeline completion
        self.visualizer_config = visualizer_config
        self.napari_port = napari_port  # Port for napari streaming
        self.replace_layers = replace_layers  # If True, replace existing layers; if False, add new layers
        self.port: Optional[int] = None
        self.process: Optional[multiprocessing.Process] = None
        self.zmq_context: Optional[zmq.Context] = None
        self.zmq_socket: Optional[zmq.Socket] = None
        self.is_running = False
        self._lock = threading.Lock()

        # Clause 368: Visualization must be observer-only.
        # This class will only read data and display it.

    def _find_free_port(self) -> int:
        """Find a free port for ZeroMQ communication."""
        import socket
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(('', 0))
            return s.getsockname()[1]

    def start_viewer(self):
        """Starts the Napari viewer in a separate process."""
        global _global_viewer_process, _global_viewer_port

        with self._lock:
            # Check if there's already a napari viewer running on the configured port
            port_in_use = self._is_port_in_use(self.napari_port)
            logger.info(f"🔬 VISUALIZER: Port {self.napari_port} in use: {port_in_use}")
            if port_in_use:
                logger.info(f"🔬 VISUALIZER: Reusing existing napari viewer on port {self.napari_port}")
                # Set the port and connect to existing viewer
                self.port = self.napari_port

                # Check if we have a reference to the global process
                with _global_process_lock:
                    if _global_viewer_process and _global_viewer_port == self.napari_port:
                        self.process = _global_viewer_process
                        logger.info(f"🔬 VISUALIZER: Found global process reference (PID: {self.process.pid})")
                    else:
                        self.process = None  # External process we don't control
                        logger.info("🔬 VISUALIZER: No global process reference (external viewer)")

                self._setup_zmq_client()
                self.is_running = True
                return

            if self.is_running:
                logger.warning("Napari viewer is already running.")
                return

            # Use configured port for napari streaming
            self.port = self.napari_port
            logger.info(f"🔬 VISUALIZER: Starting napari viewer process on port {self.port}")

            if self.persistent:
                # For persistent viewers, use detached subprocess that truly survives parent termination
                logger.info("🔬 VISUALIZER: Creating detached persistent napari viewer")
                self.process = _spawn_detached_napari_process(self.port, self.viewer_title, self.replace_layers)
            else:
                # For non-persistent viewers, use multiprocessing.Process
                logger.info("🔬 VISUALIZER: Creating non-persistent napari viewer")
                self.process = multiprocessing.Process(
                    target=_napari_viewer_process,
                    args=(self.port, self.viewer_title, self.replace_layers),
                    daemon=False
                )
                self.process.start()

            # Update global references
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
                self.is_running = True
                logger.info(f"🔬 VISUALIZER: Napari viewer process started successfully (PID: {self.process.pid})")
            else:
                logger.error("🔬 VISUALIZER: Failed to start napari viewer process")

    def _try_connect_to_existing_viewer(self, port: int) -> bool:
        """Try to connect to an existing napari viewer on the given port."""
        import socket

        # First check if anything is listening on the port
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(0.1)  # 100ms timeout
        try:
            result = sock.connect_ex(('localhost', port))
            sock.close()

            if result == 0:  # Port is open
                # Set up ZMQ connection
                self._setup_zmq_client()
                return True
            else:
                return False

        except Exception:
            return False

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
            logger.warning(f"🔬 VISUALIZER: Timeout waiting for ports to be bound")
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

        logger.warning(f"🔬 VISUALIZER: Timeout waiting for napari viewer handshake")
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
        """Send image data to the napari viewer process via ZeroMQ."""
        if not self.is_running or self.zmq_socket is None:
            logger.warning(f"🔬 VISUALIZER: Cannot send data - viewer not running")
            return

        try:
            import pickle
            message_data = {
                'step_id': step_id,
                'image_data': image_data,
                'axis_id': axis_id
            }
            message = pickle.dumps(message_data)
            self.zmq_socket.send(message, zmq.NOBLOCK)
            logger.info(f"🔬 VISUALIZER: Sent image data for {step_id}_{axis_id} (shape: {image_data.shape})")
        except Exception as e:
            logger.error(f"🔬 VISUALIZER: Failed to send image data: {e}")

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
                self.is_running = False
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
        Load data from a path and send it to the napari viewer process.
        This method is called by the orchestrator for visualization.
        """
        if not self.is_running:
            logger.warning(f"🔬 VISUALIZER: Cannot visualize - viewer not running")
            return

        try:
            # Load data using FileManager
            loaded_data = self.filemanager.load(path, backend)
            if loaded_data is not None:
                # Prepare data for display (includes GPU->CPU conversion, slicing)
                display_data = self._prepare_data_for_display(loaded_data, step_id)

                if display_data is not None:
                    self.send_image_data(step_id, display_data, axis_id or "unknown")
                    logger.debug(f"🔬 VISUALIZER: Visualized data from {path}")
                else:
                    logger.warning(f"🔬 VISUALIZER: Could not prepare data for display from {path}")
            else:
                logger.warning(f"🔬 VISUALIZER: FileManager returned None for path '{path}', backend '{backend}'")
        except Exception as e:
            logger.error(f"🔬 VISUALIZER: Error visualizing path '{path}': {e}", exc_info=True)

    def _prepare_data_for_display(self, data: Any, step_id_for_log: str) -> Optional[np.ndarray]:
        """Converts loaded data to a displayable NumPy array (e.g., 2D slice)."""
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

            # Slicing logic
            display_slice: Optional[np.ndarray] = None
            if cpu_tensor.ndim == 3: # ZYX
                display_slice = cpu_tensor[cpu_tensor.shape[0] // 2, :, :]
            elif cpu_tensor.ndim == 2: # YX
                display_slice = cpu_tensor
            elif cpu_tensor.ndim > 3: # e.g. CZYX or TZYX
                logger.warning(f"Tensor for step '{step_id_for_log}' has ndim > 3 ({cpu_tensor.ndim}). Taking a default slice.")
                slicer = [0] * (cpu_tensor.ndim - 2) # Slice first channels/times
                slicer[-1] = cpu_tensor.shape[-3] // 2 # Middle Z
                try:
                    display_slice = cpu_tensor[tuple(slicer)]
                except IndexError: # Handle cases where slicing might fail (e.g. very small dimensions)
                    logger.error(f"Slicing failed for tensor with shape {cpu_tensor.shape} for step '{step_id_for_log}'.", exc_info=True)
                    display_slice = None
            else:
                logger.warning(f"Tensor for step '{step_id_for_log}' has unsupported ndim for display: {cpu_tensor.ndim}.")
                return None

            return display_slice.copy() if display_slice is not None else None

        except Exception as e:
            logger.error(f"Error preparing data from step '{step_id_for_log}' for display: {e}", exc_info=True)
            return None

