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
from openhcs.runtime.zmq_messages import ControlMessageType, ResponseType, MessageFields, PongResponse, SocketType

logger = logging.getLogger(__name__)


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
        import zmq
        msg_type = 'shutdown' if graceful else 'force_shutdown'
        try:
            ctx = zmq.Context()
            sock = ctx.socket(zmq.REQ)
            sock.setsockopt(zmq.LINGER, 0)
            sock.setsockopt(zmq.RCVTIMEO, int(timeout * 1000))
            sock.connect(f"tcp://localhost:{port + 1000}")
            sock.send(pickle.dumps({'type': msg_type}))
            ack = pickle.loads(sock.recv())
            if ack.get('type') == 'shutdown_ack':
                time.sleep(1.0)
                return True
        except:
            pass
        finally:
            try:
                sock.close()
                ctx.term()
            except:
                pass
        if not graceful:
            return sum(ZMQServer.kill_processes_on_port(p) for p in [port, port + 1000]) > 0
        return False

    @abstractmethod
    def _spawn_server_process(self):
        pass

    @abstractmethod
    def send_data(self, data):
        pass

