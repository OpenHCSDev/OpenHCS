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
import queue
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

def _napari_viewer_process(port: int, viewer_title: str):
    """
    Napari viewer process entry point. Runs in a separate process.
    Listens for ZeroMQ messages with image data to display.
    """
    try:
        import zmq
        import napari
        import numpy as np
        import pickle

        # Set up ZeroMQ subscriber
        context = zmq.Context()
        socket = context.socket(zmq.SUB)
        socket.bind(f"tcp://*:{port}")
        socket.setsockopt(zmq.SUBSCRIBE, b"")  # Subscribe to all messages

        # Create napari viewer in this process (main thread)
        viewer = napari.Viewer(title=viewer_title, show=True)
        layers = {}

        print(f"🔬 NAPARI PROCESS: Viewer started on port {port}")

        # Use proper Qt event loop integration
        import sys
        from qtpy import QtWidgets, QtCore

        # Get the Qt application
        app = QtWidgets.QApplication.instance()
        if app is None:
            app = QtWidgets.QApplication(sys.argv)

        # Set up a QTimer for message processing
        timer = QtCore.QTimer()

        def process_messages():
            try:
                # Process multiple messages per timer tick for better throughput
                for _ in range(10):  # Process up to 10 messages per tick
                    try:
                        message = socket.recv(zmq.NOBLOCK)

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
                                    import multiprocessing as mp
                                    shm = mp.shared_memory.SharedMemory(name=shm_name)
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

                        # Update or create layer
                        if layer_name in layers:
                            layers[layer_name].data = image_data
                        else:
                            layers[layer_name] = viewer.add_image(
                                image_data,
                                name=layer_name,
                                colormap='viridis'
                            )
                        print(f"🔬 NAPARI PROCESS: Updated layer {layer_name}")

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

class NapariStreamVisualizer:
    """
    Manages a Napari viewer instance for real-time visualization of tensors
    streamed from the OpenHCS pipeline. Runs napari in a separate process
    for Qt compatibility and true persistence across pipeline runs.
    """

    def __init__(self, filemanager: FileManager, viewer_title: str = "OpenHCS Real-Time Visualization", persistent: bool = True):
        self.filemanager = filemanager
        self.viewer_title = viewer_title
        self.persistent = persistent  # If True, viewer process stays alive after pipeline completion
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
            # Check if we can reuse existing global viewer process
            with _global_process_lock:
                if (_global_viewer_process is not None and
                    _global_viewer_process.is_alive() and
                    _global_viewer_port is not None):
                    logger.info(f"🔬 VISUALIZER: Reusing existing napari viewer process on port {_global_viewer_port}")
                    self.port = _global_viewer_port
                    self.process = _global_viewer_process
                    self._setup_zmq_client()
                    self.is_running = True
                    return

            if self.is_running:
                logger.warning("Napari viewer is already running.")
                return

            # Use constant port for napari streaming
            self.port = DEFAULT_NAPARI_STREAM_PORT
            logger.info(f"🔬 VISUALIZER: Starting napari viewer process on port {self.port}")

            self.process = multiprocessing.Process(
                target=_napari_viewer_process,
                args=(self.port, self.viewer_title),
                daemon=False  # Don't make it daemon so it can outlive parent
            )
            self.process.start()

            # Update global references
            with _global_process_lock:
                _global_viewer_process = self.process
                _global_viewer_port = self.port

            # Set up ZeroMQ client
            self._setup_zmq_client()

            # Wait a moment for process to start
            time.sleep(1.0)

            if self.process.is_alive():
                self.is_running = True
                logger.info(f"🔬 VISUALIZER: Napari viewer process started successfully (PID: {self.process.pid})")
            else:
                logger.error("🔬 VISUALIZER: Failed to start napari viewer process")

    def _setup_zmq_client(self):
        """Set up ZeroMQ client to send data to viewer process."""
        if self.port is None:
            raise RuntimeError("Port not set - call start_viewer() first")

        self.zmq_context = zmq.Context()
        self.zmq_socket = self.zmq_context.socket(zmq.PUB)
        self.zmq_socket.connect(f"tcp://localhost:{self.port}")

        # Give ZeroMQ time to connect
        time.sleep(0.1)

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
            logger.debug(f"🔬 VISUALIZER: Sent image data for {step_id}_{axis_id}")
        except Exception as e:
            logger.error(f"🔬 VISUALIZER: Failed to send image data: {e}")

    def stop_viewer(self):
        """Stop the napari viewer process (only if not persistent)."""
        with self._lock:
            if not self.persistent:
                logger.info("🔬 VISUALIZER: Stopping non-persistent napari viewer")
                self._cleanup_zmq()
                if self.process and self.process.is_alive():
                    self.process.terminate()
                    self.process.join(timeout=5)
                    if self.process.is_alive():
                        logger.warning("🔬 VISUALIZER: Force killing napari viewer process")
                        self.process.kill()
                self.is_running = False
            else:
                logger.info("🔬 VISUALIZER: Keeping persistent napari viewer alive")
                # Just cleanup our ZMQ connection, leave process running
                self._cleanup_zmq()
                self.is_running = False

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

