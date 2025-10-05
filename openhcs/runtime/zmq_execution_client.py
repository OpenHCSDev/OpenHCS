"""
ZMQ Execution Client - Sends pipeline execution requests to ZMQ execution server.

This client uses the dual-channel ZMQ pattern:
- Control channel: Sends execute requests, receives responses
- Data channel: Receives progress updates

The client can connect to local or remote servers, providing location-transparent
execution (same API whether server is localhost subprocess or remote machine).
"""

import logging
import subprocess
import multiprocessing
import sys
import time
import zmq
import pickle
from pathlib import Path
from typing import Any, Dict, Optional, Callable, List
from openhcs.runtime.zmq_base import ZMQClient

logger = logging.getLogger(__name__)


class ZMQExecutionClient(ZMQClient):
    """
    ZMQ-based execution client for OpenHCS pipelines.
    
    Sends pipeline code and config to execution server,
    receives progress updates and results.
    """
    
    def __init__(
        self,
        port: int = 7777,
        host: str = 'localhost',
        persistent: bool = True,
        progress_callback: Optional[Callable[[Dict[str, Any]], None]] = None
    ):
        """
        Initialize execution client.
        
        Args:
            port: Server data port (control port will be port + 1000)
            host: Server hostname
            persistent: If True, spawn detached subprocess; if False, use multiprocessing.Process
            progress_callback: Optional callback for progress updates
        """
        super().__init__(port, host, persistent)
        self.progress_callback = progress_callback
    
    def execute_pipeline(
        self,
        plate_id: str,
        pipeline_steps: List[Any],
        global_config: Any,
        pipeline_config: Any = None,
        config_params: Optional[Dict[str, Any]] = None
    ) -> Dict[str, Any]:
        """
        Execute pipeline on server.
        
        Args:
            plate_id: Plate identifier (path or ID)
            pipeline_steps: List of pipeline step objects
            global_config: GlobalPipelineConfig instance
            pipeline_config: Optional PipelineConfig instance
            config_params: Optional dict of config parameters (alternative to global_config)
        
        Returns:
            Execution results
        """
        # Ensure connected
        if not self._connected:
            if not self.connect():
                raise RuntimeError("Failed to connect to execution server")
        
        # Generate pipeline code
        from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code
        pipeline_code = generate_complete_pipeline_steps_code(pipeline_steps, clean_mode=True)
        
        # Build request
        request = {
            'type': 'execute',
            'plate_id': str(plate_id),
            'pipeline_code': pipeline_code
        }
        
        # Add config (either as code or params)
        if config_params:
            request['config_params'] = config_params
        else:
            # Generate config code
            from openhcs.debug.pickle_to_python import generate_config_code
            from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
            
            config_code = generate_config_code(global_config, GlobalPipelineConfig, clean_mode=True)
            request['config_code'] = config_code
            
            # Optionally add pipeline_config_code
            if pipeline_config is not None:
                pipeline_config_code = generate_config_code(pipeline_config, PipelineConfig, clean_mode=True)
                request['pipeline_config_code'] = pipeline_config_code
        
        logger.info(f"Sending execution request for plate {plate_id}...")
        logger.info(f"  - Pipeline code: {len(pipeline_code)} chars")
        if 'config_code' in request:
            logger.info(f"  - Config code: {len(request['config_code'])} chars")
        if 'pipeline_config_code' in request:
            logger.info(f"  - Pipeline config code: {len(request['pipeline_config_code'])} chars")
        
        # Send request via control channel
        response = self._send_control_request(request)
        
        logger.info(f"Server response: {response.get('status')}")
        
        return response
    
    def get_status(self, execution_id: Optional[str] = None) -> Dict[str, Any]:
        """
        Query execution status.
        
        Args:
            execution_id: Specific execution ID, or None for server status
        
        Returns:
            Status response
        """
        request = {'type': 'status'}
        if execution_id:
            request['execution_id'] = execution_id
        
        return self._send_control_request(request)
    
    def cancel_execution(self, execution_id: str) -> Dict[str, Any]:
        """
        Cancel execution (not yet implemented).
        
        Args:
            execution_id: Execution to cancel
        
        Returns:
            Cancellation response
        """
        request = {
            'type': 'cancel',
            'execution_id': execution_id
        }
        
        return self._send_control_request(request)
    
    def ping(self) -> bool:
        """
        Ping server to check if alive.
        
        Returns:
            True if server responds
        """
        try:
            if not self._connected:
                # Try to connect first
                if not self.connect():
                    return False
            
            # Send ping via control channel
            control_context = zmq.Context()
            control_socket = control_context.socket(zmq.REQ)
            control_socket.setsockopt(zmq.LINGER, 0)
            control_socket.setsockopt(zmq.RCVTIMEO, 1000)  # 1 second timeout
            control_socket.connect(f"tcp://{self.host}:{self.control_port}")
            
            ping_message = {'type': 'ping'}
            control_socket.send(pickle.dumps(ping_message))
            
            response = control_socket.recv()
            response_data = pickle.loads(response)
            
            control_socket.close()
            control_context.term()
            
            return response_data.get('type') == 'pong' and response_data.get('ready')
        
        except Exception as e:
            logger.debug(f"Ping failed: {e}")
            return False
    
    def _send_control_request(self, request: Dict[str, Any]) -> Dict[str, Any]:
        """
        Send request via control channel and wait for response.
        
        Args:
            request: Request message
        
        Returns:
            Response from server
        """
        # Create fresh control socket for this request
        control_context = zmq.Context()
        control_socket = control_context.socket(zmq.REQ)
        control_socket.setsockopt(zmq.LINGER, 0)
        control_socket.connect(f"tcp://{self.host}:{self.control_port}")
        
        try:
            # Send request
            control_socket.send(pickle.dumps(request))
            
            # Wait for response
            response = control_socket.recv()
            response_data = pickle.loads(response)
            
            return response_data
        
        finally:
            control_socket.close()
            control_context.term()
    
    def _spawn_server_process(self):
        """
        Spawn new execution server process.
        
        Returns:
            Process object (subprocess.Popen or multiprocessing.Process)
        """
        if self.persistent:
            # Spawn detached subprocess
            return self._spawn_detached_server()
        else:
            # Spawn multiprocessing.Process
            return self._spawn_multiprocessing_server()
    
    def _spawn_detached_server(self):
        """Spawn detached subprocess that survives parent termination."""
        # Find the server launcher script
        launcher_module = 'openhcs.runtime.zmq_execution_server_launcher'
        
        # Spawn detached process
        process = subprocess.Popen(
            [sys.executable, '-m', launcher_module, '--port', str(self.port), '--persistent'],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True  # Detach from parent
        )
        
        logger.info(f"Spawned detached execution server on port {self.port} (PID: {process.pid})")
        return process
    
    def _spawn_multiprocessing_server(self):
        """Spawn multiprocessing.Process that dies with parent."""
        def run_server():
            from openhcs.runtime.zmq_execution_server import ZMQExecutionServer
            server = ZMQExecutionServer(port=self.port)
            server.start()
            server.start_time = time.time()
            
            # Run message loop
            import time
            try:
                while server.is_running():
                    server.process_messages()
                    time.sleep(0.01)  # Small delay to avoid busy loop
            except KeyboardInterrupt:
                pass
            finally:
                server.stop()
        
        process = multiprocessing.Process(target=run_server, daemon=False)
        process.start()
        
        logger.info(f"Spawned multiprocessing execution server on port {self.port} (PID: {process.pid})")
        return process
    
    def send_data(self, data: Dict[str, Any]):
        """
        Send data to server (not used for execution client).
        
        For execution client, we send requests via control channel,
        not data channel.
        """
        pass
    
    def __enter__(self):
        """Context manager entry."""
        self.connect()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self.disconnect()

