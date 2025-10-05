"""
Generic ZMQ communication pattern extracted from Napari streaming.

This module provides abstract base classes for dual-channel ZMQ communication:
- Data channel: For sending/receiving data (SUB/PUB pattern)
- Control channel: For handshake and control messages (REQ/REP pattern)

The pattern supports:
- Multi-instance management (connect to existing or spawn new)
- Port-based tracking
- Handshake protocol (ping/pong)
- Process lifecycle management
"""

import logging
import socket
import subprocess
import platform
import time
import threading
from abc import ABC, abstractmethod
from pathlib import Path
from typing import Optional, Callable, Any, Dict
import pickle

logger = logging.getLogger(__name__)


class ZMQServer(ABC):
    """
    Abstract base class for ZMQ servers using dual-channel pattern.
    
    Implements:
    - Dual-channel setup (data + control ports)
    - Handshake protocol (ping/pong)
    - Port management utilities
    - Lifecycle management
    
    Subclasses must implement:
    - handle_data_message(): Process data channel messages
    - handle_control_message(): Process control channel messages (beyond ping/pong)
    """
    
    def __init__(self, port: int, host: str = '*'):
        """
        Initialize ZMQ server.
        
        Args:
            port: Data port (control port will be port + 1000)
            host: Host to bind to (default: '*' for all interfaces)
        """
        self.port = port
        self.host = host
        self.control_port = port + 1000
        
        self.zmq_context = None
        self.data_socket = None
        self.control_socket = None
        self._running = False
        self._ready = False
        self._lock = threading.Lock()
    
    def start(self):
        """Start the ZMQ server (bind sockets and start message loop)."""
        import zmq
        
        with self._lock:
            if self._running:
                logger.warning("Server already running")
                return
            
            # Create ZMQ context
            self.zmq_context = zmq.Context()
            
            # Set up data socket (PUB for sending data to clients)
            self.data_socket = self.zmq_context.socket(zmq.PUB)
            self.data_socket.setsockopt(zmq.LINGER, 0)
            self.data_socket.bind(f"tcp://{self.host}:{self.port}")
            
            # Set up control socket (REP for handshake and control)
            self.control_socket = self.zmq_context.socket(zmq.REP)
            self.control_socket.setsockopt(zmq.LINGER, 0)
            self.control_socket.bind(f"tcp://{self.host}:{self.control_port}")
            
            self._running = True
            logger.info(f"ZMQ Server started on data port {self.port}, control port {self.control_port}")
    
    def stop(self):
        """Stop the ZMQ server (close sockets and cleanup)."""
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
    
    def is_running(self) -> bool:
        """Check if server is running."""
        return self._running
    
    def process_messages(self):
        """
        Process incoming messages on both channels.
        
        This should be called periodically (e.g., in a timer or event loop).
        """
        import zmq
        
        if not self._running:
            return
        
        # Handle control messages (handshake) first
        try:
            control_message = self.control_socket.recv(zmq.NOBLOCK)
            control_data = pickle.loads(control_message)
            
            if control_data.get('type') == 'ping':
                # Handle ping - mark as ready after first ping
                if not self._ready:
                    self._ready = True
                    logger.info("Server marked as ready after ping")
                
                response = self._create_pong_response()
                self.control_socket.send(pickle.dumps(response))
                logger.debug(f"Responded to ping with ready={self._ready}")
            else:
                # Delegate to subclass
                response = self.handle_control_message(control_data)
                self.control_socket.send(pickle.dumps(response))
        
        except zmq.Again:
            pass  # No control messages
        
        # Process data messages only if ready
        if self._ready:
            try:
                # Subclasses can override to receive data messages
                # For execution server, we use REQ/REP on control channel instead
                pass
            except zmq.Again:
                pass  # No data messages
    
    def _create_pong_response(self) -> Dict[str, Any]:
        """Create pong response. Subclasses can override to add custom fields."""
        return {
            'type': 'pong',
            'ready': self._ready,
            'server': self.__class__.__name__
        }
    
    @abstractmethod
    def handle_control_message(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle control channel messages (beyond ping/pong).
        
        Args:
            message: Deserialized message from control channel
        
        Returns:
            Response to send back to client
        """
        pass
    
    @abstractmethod
    def handle_data_message(self, message: Dict[str, Any]):
        """
        Handle data channel messages.
        
        Args:
            message: Deserialized message from data channel
        """
        pass


class ZMQClient(ABC):
    """
    Abstract base class for ZMQ clients using dual-channel pattern.
    
    Implements:
    - Connection management (connect to existing or spawn new server)
    - Handshake verification (ping/pong)
    - Multi-instance support (port-based tracking)
    - Process spawning utilities
    
    Subclasses must implement:
    - _spawn_server_process(): Spawn new server process
    - send_data(): Send data to server
    """
    
    def __init__(self, port: int, host: str = 'localhost', persistent: bool = True):
        """
        Initialize ZMQ client.
        
        Args:
            port: Server data port (control port will be port + 1000)
            host: Server hostname
            persistent: If True, spawn detached subprocess; if False, use multiprocessing.Process
        """
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
    
    def connect(self, timeout: float = 10.0) -> bool:
        """
        Connect to server, spawning new one if needed.
        
        Args:
            timeout: Maximum time to wait for server to be ready
        
        Returns:
            True if connected successfully
        """
        with self._lock:
            # Check if already connected
            if self._connected:
                logger.info("Already connected to server")
                return True
            
            # Try to connect to existing server
            if self._is_port_in_use(self.port):
                logger.info(f"Port {self.port} in use, attempting to connect to existing server...")
                if self._try_connect_to_existing(self.port):
                    logger.info(f"Successfully connected to existing server on port {self.port}")
                    self._connected = True
                    self._connected_to_existing = True
                    return True
                else:
                    # Existing server is unresponsive - kill it and start fresh
                    logger.info(f"Existing server on port {self.port} is unresponsive, killing and restarting...")
                    self._kill_processes_on_port(self.port)
                    self._kill_processes_on_port(self.control_port)
                    time.sleep(0.5)
            
            # Spawn new server process
            logger.info(f"Starting new server on port {self.port}")
            self.server_process = self._spawn_server_process()
            
            # Wait for server to be ready
            if not self._wait_for_server_ready(timeout):
                logger.error("Server failed to become ready")
                return False
            
            # Set up client sockets
            self._setup_client_sockets()
            
            self._connected = True
            logger.info(f"Successfully connected to new server on port {self.port}")
            return True

    def disconnect(self):
        """Disconnect from server and cleanup."""
        with self._lock:
            if not self._connected:
                return

            self._cleanup_sockets()

            # Only kill server if we spawned it (not if we connected to existing)
            if not self._connected_to_existing and self.server_process:
                if hasattr(self.server_process, 'is_alive'):
                    # multiprocessing.Process
                    if self.server_process.is_alive():
                        self.server_process.terminate()
                        self.server_process.join(timeout=5)
                        if self.server_process.is_alive():
                            self.server_process.kill()
                else:
                    # subprocess.Popen
                    if self.server_process.poll() is None:
                        self.server_process.terminate()
                        try:
                            self.server_process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            self.server_process.kill()

            self._connected = False
            logger.info("Disconnected from server")

    def is_connected(self) -> bool:
        """Check if connected to server."""
        return self._connected

    def _setup_client_sockets(self):
        """Set up client ZMQ sockets."""
        import zmq

        self.zmq_context = zmq.Context()

        # Data socket (SUB for receiving data from server)
        self.data_socket = self.zmq_context.socket(zmq.SUB)
        self.data_socket.setsockopt(zmq.LINGER, 0)
        self.data_socket.connect(f"tcp://{self.host}:{self.port}")
        self.data_socket.setsockopt(zmq.SUBSCRIBE, b"")  # Subscribe to all messages

        # Brief delay for connection to establish
        time.sleep(0.1)
        logger.info(f"Client sockets connected to {self.host}:{self.port}")

    def _cleanup_sockets(self):
        """Close client sockets."""
        if self.data_socket:
            self.data_socket.close()
            self.data_socket = None

        if self.control_socket:
            self.control_socket.close()
            self.control_socket = None

        if self.zmq_context:
            self.zmq_context.term()
            self.zmq_context = None

    def _try_connect_to_existing(self, port: int) -> bool:
        """
        Try to connect to existing server and verify it's responsive.

        Returns:
            True if successfully connected and verified
        """
        import zmq

        control_port = port + 1000
        control_context = None
        control_socket = None

        try:
            control_context = zmq.Context()
            control_socket = control_context.socket(zmq.REQ)
            control_socket.setsockopt(zmq.LINGER, 0)
            control_socket.setsockopt(zmq.RCVTIMEO, 500)  # 500ms timeout
            control_socket.connect(f"tcp://{self.host}:{control_port}")

            # Send ping
            ping_message = {'type': 'ping'}
            control_socket.send(pickle.dumps(ping_message))

            # Wait for pong
            response = control_socket.recv()
            response_data = pickle.loads(response)

            if response_data.get('type') == 'pong' and response_data.get('ready'):
                # Server is responsive!
                return True
            else:
                return False

        except Exception as e:
            logger.debug(f"Failed to connect to existing server on port {port}: {e}")
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

    def _wait_for_server_ready(self, timeout: float = 10.0) -> bool:
        """
        Wait for server to be ready using handshake protocol.

        Args:
            timeout: Maximum time to wait (seconds)

        Returns:
            True if server became ready
        """
        import zmq

        logger.info(f"Waiting for server to be ready on port {self.port}...")

        # First wait for ports to be bound
        start_time = time.time()
        while time.time() - start_time < timeout:
            if self._is_port_in_use(self.port) and self._is_port_in_use(self.control_port):
                break
            time.sleep(0.2)
        else:
            logger.warning("Timeout waiting for ports to be bound")
            return False

        # Now use handshake protocol
        start_time = time.time()
        while time.time() - start_time < timeout:
            control_context = zmq.Context()
            control_socket = control_context.socket(zmq.REQ)
            control_socket.setsockopt(zmq.LINGER, 0)
            control_socket.setsockopt(zmq.RCVTIMEO, 1000)  # 1 second timeout

            try:
                control_socket.connect(f"tcp://{self.host}:{self.control_port}")

                ping_message = {'type': 'ping'}
                control_socket.send(pickle.dumps(ping_message))

                response = control_socket.recv()
                response_data = pickle.loads(response)

                if response_data.get('type') == 'pong' and response_data.get('ready'):
                    logger.info(f"Server is ready on port {self.port}")
                    control_socket.close()
                    control_context.term()
                    return True

            except Exception:
                pass
            finally:
                try:
                    control_socket.close()
                    control_context.term()
                except:
                    pass

            time.sleep(0.5)

        logger.warning("Timeout waiting for server to be ready")
        return False

    def _is_port_in_use(self, port: int) -> bool:
        """Check if a port is already in use."""
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(0.1)
        try:
            sock.bind(('localhost', port))
            sock.close()
            return False  # Port is free
        except OSError:
            sock.close()
            return True  # Port is in use
        except Exception:
            return False

    def _find_free_port(self) -> int:
        """Find a free port for ZMQ communication."""
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            s.bind(('', 0))
            return s.getsockname()[1]

    def _kill_processes_on_port(self, port: int):
        """
        Kill only the process LISTENING on the specified port.

        Does NOT kill client processes that are merely connected to the port.
        """
        try:
            system = platform.system()

            if system == "Linux" or system == "Darwin":
                # Use lsof with -sTCP:LISTEN to find only LISTENING processes
                result = subprocess.run(
                    ['lsof', '-ti', f'TCP:{port}', '-sTCP:LISTEN'],
                    capture_output=True,
                    text=True,
                    timeout=2
                )

                if result.returncode == 0 and result.stdout.strip():
                    pids = result.stdout.strip().split('\n')
                    for pid in pids:
                        try:
                            subprocess.run(['kill', '-9', pid], timeout=1)
                            logger.info(f"Killed process {pid} listening on port {port}")
                        except Exception as e:
                            logger.warning(f"Failed to kill process {pid}: {e}")

            elif system == "Windows":
                # Use netstat to find processes LISTENING on the port
                result = subprocess.run(
                    ['netstat', '-ano'],
                    capture_output=True,
                    text=True,
                    timeout=2
                )

                for line in result.stdout.split('\n'):
                    if f':{port}' in line and 'LISTENING' in line:
                        parts = line.split()
                        pid = parts[-1]
                        try:
                            subprocess.run(['taskkill', '/F', '/PID', pid], timeout=1)
                            logger.info(f"Killed process {pid} listening on port {port}")
                        except Exception as e:
                            logger.warning(f"Failed to kill process {pid}: {e}")

        except Exception as e:
            logger.warning(f"Failed to kill processes on port {port}: {e}")

    @abstractmethod
    def _spawn_server_process(self):
        """
        Spawn new server process.

        Returns:
            Process object (subprocess.Popen or multiprocessing.Process)
        """
        pass

    @abstractmethod
    def send_data(self, data: Dict[str, Any]):
        """
        Send data to server.

        Args:
            data: Data to send
        """
        pass

