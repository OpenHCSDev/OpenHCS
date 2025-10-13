"""
Fiji stream visualizer for OpenHCS.

Manages Fiji viewer instances for real-time visualization via ZMQ.
Uses FijiViewerServer (inherits from ZMQServer) for PyImageJ-based display.
Follows same architecture as NapariStreamVisualizer.
"""

import logging
import multiprocessing
import subprocess
import threading
import time
from typing import Optional
from pathlib import Path

from openhcs.io.filemanager import FileManager

logger = logging.getLogger(__name__)

# Global process management for Fiji viewer
_global_fiji_process: Optional[multiprocessing.Process] = None
_global_fiji_lock = threading.Lock()


def _cleanup_global_fiji_viewer() -> None:
    """Clean up global Fiji viewer process for test mode."""
    global _global_fiji_process

    with _global_fiji_lock:
        if _global_fiji_process and _global_fiji_process.is_alive():
            logger.info("🔬 FIJI VISUALIZER: Terminating Fiji viewer for test cleanup")
            _global_fiji_process.terminate()
            _global_fiji_process.join(timeout=3)

            if _global_fiji_process.is_alive():
                logger.warning("🔬 FIJI VISUALIZER: Force killing Fiji viewer process")
                _global_fiji_process.kill()
                _global_fiji_process.join(timeout=1)

            _global_fiji_process = None






class FijiStreamVisualizer:
    """
    Manages Fiji viewer instance for real-time visualization via ZMQ.

    Uses FijiViewerServer (inherits from ZMQServer) for PyImageJ-based display.
    Follows same architecture as NapariStreamVisualizer.
    """

    def __init__(self, filemanager: FileManager, visualizer_config, viewer_title: str = "OpenHCS Fiji Visualization",
                 persistent: bool = True, fiji_port: int = 5556, display_config=None):
        self.filemanager = filemanager
        self.viewer_title = viewer_title
        self.persistent = persistent
        self.visualizer_config = visualizer_config
        self.fiji_port = fiji_port
        self.display_config = display_config
        self.process: Optional[multiprocessing.Process] = None
        self.is_running = False
        self._lock = threading.Lock()

    def start_viewer(self, async_mode: bool = False) -> None:
        """Start Fiji viewer server process."""
        global _global_fiji_process

        with self._lock:
            # Check for existing global viewer on same port
            with _global_fiji_lock:
                if _global_fiji_process is not None and _global_fiji_process.is_alive():
                    logger.info("🔬 FIJI VISUALIZER: Reusing existing Fiji viewer process")
                    self.process = _global_fiji_process
                    self.is_running = True
                    return

            if self.is_running:
                logger.warning("Fiji viewer is already running.")
                return

            # Create log file path for ZMQ discovery
            import tempfile
            log_dir = Path(tempfile.gettempdir()) / "openhcs_fiji_logs"
            log_dir.mkdir(exist_ok=True)
            log_file_path = str(log_dir / f"fiji_viewer_{self.fiji_port}.log")

            logger.info(f"🔬 FIJI VISUALIZER: Starting Fiji viewer server on port {self.fiji_port}")
            logger.info(f"🔬 FIJI VISUALIZER: Log file: {log_file_path}")

            # Import server process function
            from openhcs.runtime.fiji_viewer_server import _fiji_viewer_server_process

            self.process = multiprocessing.Process(
                target=_fiji_viewer_server_process,
                args=(self.fiji_port, self.viewer_title, self.display_config, log_file_path),
                daemon=False
            )
            self.process.start()

            # Update global reference
            with _global_fiji_lock:
                _global_fiji_process = self.process

            self.is_running = True
            logger.info(f"🔬 FIJI VISUALIZER: Fiji viewer server started (PID: {self.process.pid})")

            # Wait for server to be ready (ping/pong handshake)
            if not async_mode:
                self._wait_for_server_ready()

    def _wait_for_server_ready(self, timeout: float = 10.0) -> bool:
        """Wait for Fiji server to be ready via ping/pong."""
        import zmq
        import pickle

        logger.info(f"🔬 FIJI VISUALIZER: Waiting for server on port {self.fiji_port} to be ready...")

        start_time = time.time()
        while time.time() - start_time < timeout:
            try:
                # Simple ping/pong check
                ctx = zmq.Context()
                sock = ctx.socket(zmq.REQ)
                sock.setsockopt(zmq.LINGER, 0)
                sock.setsockopt(zmq.RCVTIMEO, 500)  # 500ms timeout
                sock.connect(f"tcp://localhost:{self.fiji_port + 1000}")

                # Send ping
                sock.send(pickle.dumps({'type': 'ping'}))
                response = pickle.loads(sock.recv())

                sock.close()
                ctx.term()

                if response.get('type') == 'pong':
                    logger.info(f"🔬 FIJI VISUALIZER: Server ready on port {self.fiji_port}")
                    return True
            except Exception as e:
                logger.debug(f"🔬 FIJI VISUALIZER: Ping failed: {e}")

            time.sleep(0.2)

        logger.warning(f"🔬 FIJI VISUALIZER: Timeout waiting for server on port {self.fiji_port}")
        return False

    def stop_viewer(self) -> None:
        """Stop Fiji viewer server."""
        global _global_fiji_process

        with self._lock:
            if not self.is_running or self.process is None:
                logger.warning("Fiji viewer is not running.")
                return

            if not self.persistent:
                logger.info("🔬 FIJI VISUALIZER: Stopping Fiji viewer server")

                # Try graceful shutdown via ZMQ
                if self._zmq_client:
                    try:
                        self._zmq_client.send_control_message({'type': 'shutdown'})
                    except Exception as e:
                        logger.warning(f"🔬 FIJI VISUALIZER: Graceful shutdown failed: {e}")

                self.process.terminate()
                self.process.join(timeout=5)

                if self.process.is_alive():
                    logger.warning("🔬 FIJI VISUALIZER: Force killing Fiji viewer")
                    self.process.kill()
                    self.process.join(timeout=2)

                # Clear global reference
                with _global_fiji_lock:
                    if _global_fiji_process == self.process:
                        _global_fiji_process = None

            self.process = None
            self.is_running = False
            logger.info("🔬 FIJI VISUALIZER: Fiji viewer stopped")

    def _cleanup_zmq(self) -> None:
        """Clean up ZMQ client connection (for persistent viewers)."""
        if self._zmq_client:
            try:
                self._zmq_client.close()
            except Exception as e:
                logger.warning(f"🔬 FIJI VISUALIZER: Failed to cleanup ZMQ client: {e}")
            self._zmq_client = None

    def is_viewer_running(self) -> bool:
        """Check if Fiji viewer process is running."""
        return self.is_running and self.process is not None and self.process.is_alive()
