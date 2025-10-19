"""Generic ZMQ dual-channel pattern (data + control)."""

import logging
import socket
import subprocess
import platform
import time
import threading
import os
from abc import ABC, abstractmethod
from pathlib import Path
import pickle
from openhcs.runtime.zmq_messages import ControlMessageType, ResponseType, MessageFields, PongResponse, SocketType, ImageAck

logger = logging.getLogger(__name__)

# Global shared acknowledgment port for all viewers
# All viewers send acks to this port via PUSH sockets
# Client listens on this port via PULL socket
SHARED_ACK_PORT = 7555


# Global ack listener singleton
_ack_listener_thread = None
_ack_listener_lock = threading.Lock()
_ack_listener_running = False


def start_global_ack_listener():
    """Start the global ack listener thread (singleton).

    This thread listens on SHARED_ACK_PORT for acknowledgments from all viewers
    and routes them to the appropriate queue trackers.

    Safe to call multiple times - only starts once.
    """
    global _ack_listener_thread, _ack_listener_running

    with _ack_listener_lock:
        if _ack_listener_running:
            logger.debug("Ack listener already running")
            return

        logger.info(f"Starting global ack listener on port {SHARED_ACK_PORT}")
        _ack_listener_running = True
        _ack_listener_thread = threading.Thread(
            target=_ack_listener_loop,
            daemon=True,
            name="AckListener"
        )
        _ack_listener_thread.start()


def _ack_listener_loop():
    """Main loop for ack listener thread.

    Receives acks from all viewers and routes to queue trackers.
    """
    import zmq
    from openhcs.runtime.queue_tracker import GlobalQueueTrackerRegistry

    registry = GlobalQueueTrackerRegistry()
    context = zmq.Context()
    socket = None

    try:
        socket = context.socket(zmq.PULL)
        socket.bind(f"tcp://*:{SHARED_ACK_PORT}")
        logger.info(f"✅ Ack listener bound to port {SHARED_ACK_PORT}")

        while _ack_listener_running:
            try:
                # Receive ack message (with timeout to allow checking _ack_listener_running)
                if socket.poll(timeout=1000):  # 1 second timeout
                    ack_dict = socket.recv_json()

                    # Parse ack message
                    try:
                        ack = ImageAck.from_dict(ack_dict)

                        # Route to appropriate queue tracker
                        tracker = registry.get_tracker(ack.viewer_port)
                        if tracker:
                            tracker.mark_processed(ack.image_id)

                            # Trigger UI refresh to show updated progress immediately
                            try:
                                from openhcs.pyqt_gui.widgets.shared.zmq_server_manager import _trigger_manager_refresh_fast
                                _trigger_manager_refresh_fast()
                            except ImportError:
                                # PyQt not available (e.g., in TUI mode) - skip UI refresh
                                pass
                        else:
                            logger.warning(f"Received ack for unknown viewer port {ack.viewer_port}: {ack.image_id}")

                    except Exception as e:
                        logger.error(f"Failed to parse ack message: {e}", exc_info=True)

            except zmq.ZMQError as e:
                if _ack_listener_running:
                    logger.error(f"ZMQ error in ack listener: {e}")
                    time.sleep(0.1)

    except Exception as e:
        logger.error(f"Fatal error in ack listener: {e}", exc_info=True)

    finally:
        if socket:
            try:
                socket.close()
            except:
                pass
        try:
            context.term()
        except:
            pass
        logger.info("Ack listener stopped")


def stop_global_ack_listener():
    """Stop the global ack listener thread."""
    global _ack_listener_running

    with _ack_listener_lock:
        if not _ack_listener_running:
            return

        logger.info("Stopping global ack listener")
        _ack_listener_running = False


class ZMQServer(ABC):
    """ABC for ZMQ servers - dual-channel pattern with ping/pong handshake."""

    def __init__(self, port, host='*', log_file_path=None, data_socket_type=None):
        import zmq
        self.port = port
        self.host = host
        self.control_port = port + 1000
        self.log_file_path = log_file_path
        self.data_socket_type = data_socket_type if data_socket_type is not None else zmq.PUB
        self.zmq_context = None
        self.data_socket = None
        self.control_socket = None
        self._running = False
        self._ready = False
        self._lock = threading.Lock()
    
    def start(self):
        import zmq
        with self._lock:
            if self._running:
                return
            self.zmq_context = zmq.Context()
            self.data_socket = self.zmq_context.socket(self.data_socket_type)
            self.data_socket.setsockopt(zmq.LINGER, 0)
            self.data_socket.bind(f"tcp://{self.host}:{self.port}")
            if self.data_socket_type == zmq.SUB:
                self.data_socket.setsockopt(zmq.SUBSCRIBE, b"")
            self.control_socket = self.zmq_context.socket(zmq.REP)
            self.control_socket.setsockopt(zmq.LINGER, 0)
            self.control_socket.bind(f"tcp://{self.host}:{self.control_port}")
            self._running = True
            logger.info(f"ZMQ Server started on {self.port} ({SocketType.from_zmq_constant(self.data_socket_type).get_display_name()}), control {self.control_port}")

    def stop(self):
        with self._lock:
            if not self._running:
                return
            self._running = False
            if self.data_socket:
                self.data_socket.close()
                self.data_socket = None
            if self.control_socket:
                self.control_socket.close()
                self.control_socket = None
            if self.zmq_context:
                self.zmq_context.term()
                self.zmq_context = None
            logger.info("ZMQ Server stopped")

    def is_running(self):
        return self._running

    def process_messages(self):
        import zmq
        if not self._running:
            return
        try:
            control_data = pickle.loads(self.control_socket.recv(zmq.NOBLOCK))
            if control_data.get(MessageFields.TYPE) == ControlMessageType.PING.value:
                if not self._ready:
                    self._ready = True
                    logger.info("Server ready")
                response = self._create_pong_response()
            else:
                response = self.handle_control_message(control_data)
            self.control_socket.send(pickle.dumps(response))
        except zmq.Again:
            pass

    def _create_pong_response(self):
        return PongResponse(port=self.port, control_port=self.control_port, ready=self._ready,
                           server=self.__class__.__name__, log_file_path=self.log_file_path).to_dict()

    def get_status_info(self):
        return {'port': self.port, 'control_port': self.control_port, 'running': self._running,
                'ready': self._ready, 'server_type': self.__class__.__name__, 'log_file': self.log_file_path}

    def request_shutdown(self):
        self._running = False

    @staticmethod
    def kill_processes_on_port(port):
        killed = 0
        try:
            system = platform.system()
            if system in ["Linux", "Darwin"]:
                result = subprocess.run(['lsof', '-ti', f'TCP:{port}', '-sTCP:LISTEN'], capture_output=True, text=True, timeout=2)
                if result.returncode == 0 and result.stdout.strip():
                    for pid in result.stdout.strip().split('\n'):
                        try:
                            subprocess.run(['kill', '-9', pid], timeout=1)
                            killed += 1
                        except:
                            pass
            elif system == "Windows":
                result = subprocess.run(['netstat', '-ano'], capture_output=True, text=True, timeout=2)
                for line in result.stdout.split('\n'):
                    if f':{port}' in line and 'LISTENING' in line:
                        try:
                            subprocess.run(['taskkill', '/F', '/PID', line.split()[-1]], timeout=1)
                            killed += 1
                        except:
                            pass
        except:
            pass
        return killed

    @staticmethod
    def load_images_from_shared_memory(images, error_callback=None):
        """Load images from shared memory and clean up.

        Args:
            images: List of image info dicts with shm_name, shape, dtype, metadata, image_id
            error_callback: Optional callback(image_id, status, error) for errors

        Returns:
            List of dicts with 'data', 'metadata', 'image_id' keys
        """
        import numpy as np
        from multiprocessing import shared_memory

        image_data_list = []
        for image_info in images:
            shm_name = image_info.get('shm_name')
            shape = tuple(image_info.get('shape'))
            dtype = np.dtype(image_info.get('dtype'))
            metadata = image_info.get('metadata', {})
            image_id = image_info.get('image_id')

            try:
                shm = shared_memory.SharedMemory(name=shm_name)
                np_data = np.ndarray(shape, dtype=dtype, buffer=shm.buf).copy()
                shm.close()
                shm.unlink()

                image_data_list.append({
                    'data': np_data,
                    'metadata': metadata,
                    'image_id': image_id
                })
            except Exception as e:
                logger.error(f"Failed to read shared memory {shm_name}: {e}")
                if error_callback and image_id:
                    error_callback(image_id, 'error', f"Failed to read shared memory: {e}")
                continue

        return image_data_list

    @staticmethod
    def collect_dimension_values(images, components):
        """Collect unique dimension value tuples from images.

        Args:
            images: List of image data dicts with 'metadata' key
            components: List of component names to collect

        Returns:
            Sorted list of unique value tuples
        """
        if not components:
            return [()]

        values = set()
        for img_data in images:
            meta = img_data['metadata']
            # Fail loud if component missing from metadata
            value_tuple = tuple(meta[comp] for comp in components)
            values.add(value_tuple)

        return sorted(values)

    @staticmethod
    def organize_components_by_mode(component_order, component_modes, component_unique_values, always_include_window=True, skip_flat_dimensions=True):
        """Organize components by their display mode.

        Args:
            component_order: Ordered list of component names
            component_modes: Map of component name to mode ('window', 'channel', 'slice', 'frame')
            component_unique_values: Map of component name to set of unique values
            always_include_window: If True, include WINDOW components even if flat
            skip_flat_dimensions: If True, skip components with cardinality <= 1 for non-window dimensions

        Returns:
            Dict with keys 'window', 'channel', 'slice', 'frame' mapping to component lists
        """
        result = {
            'window': [],
            'channel': [],
            'slice': [],
            'frame': []
        }

        for comp_name in component_order:
            mode = component_modes[comp_name]
            is_flat = len(component_unique_values.get(comp_name, set())) <= 1

            if mode == 'window':
                # Always include WINDOW components, even if flat
                result['window'].append(comp_name)
            elif skip_flat_dimensions and is_flat:
                # Skip flat dimensions for hyperstack axes (only if skip_flat_dimensions=True)
                continue
            else:
                result[mode].append(comp_name)

        return result

    @abstractmethod
    def handle_control_message(self, message):
        pass

    @abstractmethod
    def handle_data_message(self, message):
        pass


class ZMQClient(ABC):
    """ABC for ZMQ clients - dual-channel pattern with auto-spawning."""

    def __init__(self, port, host='localhost', persistent=True):
        self.port = port
        self.host = host
        self.control_port = port + 1000
        self.persistent = persistent
        self.zmq_context = None
        self.data_socket = None
        self.control_socket = None
        self.server_process = None
        self._connected = False
        self._connected_to_existing = False
        self._lock = threading.Lock()
    
    def connect(self, timeout=10.0):
        with self._lock:
            if self._connected:
                return True
            if self._is_port_in_use(self.port):
                if self._try_connect_to_existing(self.port):
                    self._connected = self._connected_to_existing = True
                    return True
                self._kill_processes_on_port(self.port)
                self._kill_processes_on_port(self.control_port)
                time.sleep(0.5)
            self.server_process = self._spawn_server_process()
            if not self._wait_for_server_ready(timeout):
                return False
            self._setup_client_sockets()
            self._connected = True
            return True

    def disconnect(self):
        with self._lock:
            if not self._connected:
                return
            self._cleanup_sockets()
            if not self._connected_to_existing and self.server_process and not self.persistent:
                if hasattr(self.server_process, 'is_alive'):
                    if self.server_process.is_alive():
                        self.server_process.terminate()
                        self.server_process.join(timeout=5)
                        if self.server_process.is_alive():
                            self.server_process.kill()
                else:
                    if self.server_process.poll() is None:
                        self.server_process.terminate()
                        try:
                            self.server_process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            self.server_process.kill()
            self._connected = False

    def is_connected(self):
        return self._connected

    def _setup_client_sockets(self):
        import zmq
        self.zmq_context = zmq.Context()
        self.data_socket = self.zmq_context.socket(zmq.SUB)
        self.data_socket.setsockopt(zmq.LINGER, 0)
        self.data_socket.connect(f"tcp://{self.host}:{self.port}")
        self.data_socket.setsockopt(zmq.SUBSCRIBE, b"")
        time.sleep(0.1)

    def _cleanup_sockets(self):
        if self.data_socket:
            self.data_socket.close()
            self.data_socket = None
        if self.control_socket:
            self.control_socket.close()
            self.control_socket = None

        if self.zmq_context:
            self.zmq_context.term()
            self.zmq_context = None

    def _try_connect_to_existing(self, port):
        import zmq
        try:
            ctx = zmq.Context()
            sock = ctx.socket(zmq.REQ)
            sock.setsockopt(zmq.LINGER, 0)
            sock.setsockopt(zmq.RCVTIMEO, 500)
            sock.connect(f"tcp://{self.host}:{port + 1000}")
            sock.send(pickle.dumps({'type': 'ping'}))
            response = pickle.loads(sock.recv())
            return response.get('type') == 'pong' and response.get('ready')
        except:
            return False
        finally:
            try:
                sock.close()
                ctx.term()
            except:
                pass

    def _wait_for_server_ready(self, timeout=10.0):
        import zmq
        start = time.time()
        while time.time() - start < timeout:
            if self._is_port_in_use(self.port) and self._is_port_in_use(self.control_port):
                break
            time.sleep(0.2)
        else:
            return False
        start = time.time()
        while time.time() - start < timeout:
            try:
                ctx = zmq.Context()
                sock = ctx.socket(zmq.REQ)
                sock.setsockopt(zmq.LINGER, 0)
                sock.setsockopt(zmq.RCVTIMEO, 1000)
                sock.connect(f"tcp://{self.host}:{self.control_port}")
                sock.send(pickle.dumps({'type': 'ping'}))
                response = pickle.loads(sock.recv())
                if response.get('type') == 'pong' and response.get('ready'):
                    sock.close()
                    ctx.term()
                    return True
            except:
                pass
            finally:
                try:
                    sock.close()
                    ctx.term()
                except:
                    pass
            time.sleep(0.5)

        return False

    def _is_port_in_use(self, port):
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(0.1)
        try:
            sock.bind(('localhost', port))
            sock.close()
            return False
        except OSError:
            sock.close()
            return True
        except:
            return False

    def _find_free_port(self):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(('', 0))
            return s.getsockname()[1]

    def _kill_processes_on_port(self, port):
        try:
            system = platform.system()
            if system in ["Linux", "Darwin"]:
                result = subprocess.run(['lsof', '-ti', f'TCP:{port}', '-sTCP:LISTEN'], capture_output=True, text=True, timeout=2)
                if result.returncode == 0 and result.stdout.strip():
                    for pid in result.stdout.strip().split('\n'):
                        try:
                            subprocess.run(['kill', '-9', pid], timeout=1)
                        except:
                            pass
            elif system == "Windows":
                result = subprocess.run(['netstat', '-ano'], capture_output=True, text=True, timeout=2)
                for line in result.stdout.split('\n'):
                    if f':{port}' in line and 'LISTENING' in line:
                        try:
                            subprocess.run(['taskkill', '/F', '/PID', line.split()[-1]], timeout=1)
                        except:
                            pass
        except:
            pass

    @staticmethod
    def scan_servers(ports, host='localhost', timeout_ms=200):
        import zmq
        servers = []
        for port in ports:
            try:
                ctx = zmq.Context()
                sock = ctx.socket(zmq.REQ)
                sock.setsockopt(zmq.LINGER, 0)
                sock.setsockopt(zmq.RCVTIMEO, timeout_ms)
                sock.connect(f"tcp://{host}:{port + 1000}")
                sock.send(pickle.dumps({'type': 'ping'}))
                pong = pickle.loads(sock.recv())
                if pong.get('type') == 'pong':
                    pong['port'] = port
                    pong['control_port'] = port + 1000
                    servers.append(pong)
            except:
                pass
            finally:
                try:
                    sock.close()
                    ctx.term()
                except:
                    pass
        return servers

    @staticmethod
    def kill_server_on_port(port, graceful=True, timeout=5.0):
        """
        Kill server on specified port.

        Args:
            port: Server port number
            graceful: If True, kills workers only (server stays alive).
                     If False, kills workers AND server (port becomes free).
            timeout: Timeout in seconds for server response

        Returns:
            bool: True if operation succeeded
        """
        import zmq
        msg_type = 'shutdown' if graceful else 'force_shutdown'
        shutdown_sent = False
        shutdown_acknowledged = False

        def is_port_free(port):
            """Check if port is free (not in use)."""
            sock_test = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock_test.settimeout(0.1)
            try:
                sock_test.bind(('localhost', port))
                sock_test.close()
                return True
            except OSError:
                return False
            finally:
                try:
                    sock_test.close()
                except:
                    pass

        try:
            ctx = zmq.Context()
            sock = ctx.socket(zmq.REQ)
            sock.setsockopt(zmq.LINGER, 0)
            sock.setsockopt(zmq.RCVTIMEO, int(timeout * 1000))
            sock.connect(f"tcp://localhost:{port + 1000}")
            sock.send(pickle.dumps({'type': msg_type}))
            shutdown_sent = True
            ack = pickle.loads(sock.recv())
            if ack.get('type') == 'shutdown_ack':
                shutdown_acknowledged = True

                if graceful:
                    # Graceful shutdown: workers killed, server stays alive
                    # Port should still be in use
                    logger.info(f"✅ Server on port {port} acknowledged graceful shutdown (workers killed, server alive)")
                    return True
                else:
                    # Force shutdown: workers AND server killed
                    # Port should become free
                    logger.info(f"✅ Server on port {port} acknowledged force shutdown")
                    # Wait for server to actually close
                    time.sleep(1.5)
                    # Verify port is actually closed
                    if is_port_free(port):
                        logger.info(f"✅ Port {port} is now free")
                        return True
                    # Port still in use, but server acknowledged - give it more time
                    time.sleep(1.0)
                    # Check again
                    if is_port_free(port):
                        logger.info(f"✅ Port {port} is now free (after extra wait)")
                        return True
                    # Server acknowledged but port still in use - consider it success anyway
                    # (might be in TIME_WAIT state, or server is still cleaning up)
                    logger.info(f"✅ Server on port {port} acknowledged shutdown but port still in use (may be TIME_WAIT) - considering success")
                    return True
        except Exception as e:
            # If we sent the shutdown message but got a timeout on response,
            # the server might still be shutting down - verify port status
            if shutdown_sent:
                if graceful:
                    # Graceful shutdown timeout - server might have killed workers but didn't respond
                    # This is OK, consider it success
                    logger.info(f"⚠️ Graceful shutdown message sent to port {port}, but no response received: {e}")
                    logger.info(f"✅ Considering graceful shutdown successful (workers likely killed)")
                    return True
                else:
                    # Force shutdown timeout - check if port is free
                    logger.info(f"⚠️ Force shutdown message sent to port {port}, but no response received: {e}")
                    time.sleep(2.0)  # Give server time to shut down
                    # Check if port is now free
                    if is_port_free(port):
                        # Port is free, shutdown was successful despite timeout
                        logger.info(f"✅ Port {port} is now free (shutdown succeeded despite timeout)")
                        return True
                    # Port still in use - shutdown may have failed
                    logger.warning(f"❌ Port {port} still in use after force shutdown timeout")
        finally:
            try:
                sock.close()
                ctx.term()
            except:
                pass

        # If shutdown was acknowledged, consider it a success even if we couldn't verify port closure
        # (the server confirmed it's shutting down, which is good enough)
        if shutdown_acknowledged:
            logger.info(f"✅ Shutdown acknowledged for port {port}, considering it successful")
            return True

        if not graceful:
            # Force shutdown failed via ZMQ, try killing processes directly
            killed = sum(ZMQServer.kill_processes_on_port(p) for p in [port, port + 1000])
            logger.info(f"Force killed {killed} processes on ports {port} and {port + 1000}")
            return killed > 0

        logger.warning(f"❌ Failed to shutdown server on port {port} gracefully")
        return False

    @abstractmethod
    def _spawn_server_process(self):
        pass

    @abstractmethod
    def send_data(self, data):
        pass

