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


def _spawn_detached_fiji_process(port: int, viewer_title: str, display_config) -> subprocess.Popen:
    """
    Spawn a completely detached Fiji viewer process that survives parent termination.

    This creates a subprocess that runs independently and won't be terminated when
    the parent process exits, enabling true persistence across pipeline runs.
    """
    import sys
    import os

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
    from openhcs.runtime.fiji_viewer_server import _fiji_viewer_server_process
    _fiji_viewer_server_process({port}, "{viewer_title}", None, "{current_dir}/.fiji_log_path_placeholder")
except Exception as e:
    import logging
    logger = logging.getLogger("openhcs.runtime.fiji_detached")
    logger.error(f"Detached Fiji error: {{e}}")
    import traceback
    logger.error(traceback.format_exc())
    sys.exit(1)
'''

    try:
        # Create log file for detached process
        log_dir = os.path.expanduser("~/.local/share/openhcs/logs")
        os.makedirs(log_dir, exist_ok=True)
        log_file = os.path.join(log_dir, f"fiji_detached_port_{port}.log")

        # Replace placeholder with actual log file path
        python_code = python_code.replace(f"{current_dir}/.fiji_log_path_placeholder", log_file)

        # Use subprocess.Popen with detachment flags
        if sys.platform == "win32":
            env = os.environ.copy()
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
            # Unix: Use start_new_session to detach
            env = os.environ.copy()

            # Ensure display environment is preserved
            if 'QT_QPA_PLATFORM' not in env:
                env['QT_QPA_PLATFORM'] = 'xcb'
            env['QT_X11_NO_MITSHM'] = '1'

            log_f = open(log_file, 'w')
            process = subprocess.Popen(
                [sys.executable, "-c", python_code],
                env=env,
                cwd=os.getcwd(),
                stdout=log_f,
                stderr=subprocess.STDOUT,
                start_new_session=True  # CRITICAL: Detach from parent
            )

        logger.info(f"🔬 FIJI VISUALIZER: Detached Fiji process started (PID: {process.pid}), logging to {log_file}")
        return process

    except Exception as e:
        logger.error(f"🔬 FIJI VISUALIZER: Failed to spawn detached Fiji process: {e}")
        raise






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
                if _global_fiji_process is not None:
                    # Check if it's alive (works for both Process and Popen)
                    is_alive = _global_fiji_process.is_alive() if hasattr(_global_fiji_process, 'is_alive') else _global_fiji_process.poll() is None
                    if is_alive:
                        logger.info("🔬 FIJI VISUALIZER: Reusing existing Fiji viewer process")
                        self.process = _global_fiji_process
                        self.is_running = True
                        return

            if self.is_running:
                logger.warning("Fiji viewer is already running.")
                return

            logger.info(f"🔬 FIJI VISUALIZER: Starting Fiji viewer server on port {self.fiji_port} (persistent={self.persistent})")

            if self.persistent:
                # For persistent viewers, use detached subprocess that truly survives parent termination
                logger.info("🔬 FIJI VISUALIZER: Creating detached persistent Fiji viewer")
                self.process = _spawn_detached_fiji_process(self.fiji_port, self.viewer_title, self.display_config)
                # DON'T track persistent viewers in global variable - they should survive test cleanup
            else:
                # For non-persistent viewers, use multiprocessing.Process
                logger.info("🔬 FIJI VISUALIZER: Creating non-persistent Fiji viewer")

                # Create log file path for ZMQ discovery
                import tempfile
                log_dir = Path(tempfile.gettempdir()) / "openhcs_fiji_logs"
                log_dir.mkdir(exist_ok=True)
                log_file_path = str(log_dir / f"fiji_viewer_{self.fiji_port}.log")

                # Import server process function
                from openhcs.runtime.fiji_viewer_server import _fiji_viewer_server_process

                self.process = multiprocessing.Process(
                    target=_fiji_viewer_server_process,
                    args=(self.fiji_port, self.viewer_title, self.display_config, log_file_path),
                    daemon=False
                )
                self.process.start()

                # Only track non-persistent viewers in global variable for test cleanup
                with _global_fiji_lock:
                    _global_fiji_process = self.process

            self.is_running = True
            logger.info(f"🔬 FIJI VISUALIZER: Fiji viewer server started (PID: {self.process.pid if hasattr(self.process, 'pid') else 'unknown'})")

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
        """Stop Fiji viewer server (only if not persistent)."""
        global _global_fiji_process

        with self._lock:
            if not self.persistent:
                logger.info("🔬 FIJI VISUALIZER: Stopping non-persistent Fiji viewer")

                if self.process:
                    # Handle both subprocess and multiprocessing process types
                    if hasattr(self.process, 'is_alive'):
                        # multiprocessing.Process
                        if self.process.is_alive():
                            self.process.terminate()
                            self.process.join(timeout=5)
                            if self.process.is_alive():
                                logger.warning("🔬 FIJI VISUALIZER: Force killing Fiji viewer")
                                self.process.kill()
                                self.process.join(timeout=2)
                    else:
                        # subprocess.Popen
                        if self.process.poll() is None:
                            self.process.terminate()
                            try:
                                self.process.wait(timeout=5)
                            except subprocess.TimeoutExpired:
                                logger.warning("🔬 FIJI VISUALIZER: Force killing Fiji viewer")
                                self.process.kill()

                # Clear global reference
                with _global_fiji_lock:
                    if _global_fiji_process == self.process:
                        _global_fiji_process = None

                self.is_running = False
            else:
                logger.info("🔬 FIJI VISUALIZER: Keeping persistent Fiji viewer alive")
                # DON'T set is_running = False for persistent viewers!
                # The process is still alive and should be reusable

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
