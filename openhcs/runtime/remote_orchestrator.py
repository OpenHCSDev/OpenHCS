#!/usr/bin/env python3
"""
Remote Orchestrator - Client for OpenHCS Execution Server

Sends pipeline execution requests to remote OpenHCS server and receives
streamed results. Generates Python code instead of pickling objects.
"""

import json
import logging
from typing import Any, Dict, List, Optional

logger = logging.getLogger(__name__)


class RemoteOrchestrator:
    """
    Client-side orchestrator for remote pipeline execution.
    
    Sends pipeline code to execution server, receives streamed results.
    """
    
    def __init__(self, server_host: str, server_port: int = 7777):
        """
        Initialize remote orchestrator.
        
        Args:
            server_host: Execution server hostname/IP
            server_port: Execution server port
        """
        self.server_host = server_host
        self.server_port = server_port
        self.zmq_context = None
        self.zmq_socket = None
        
        logger.info(f"RemoteOrchestrator configured for {server_host}:{server_port}")
    
    def _connect(self):
        """Establish ZeroMQ connection to server."""
        if self.zmq_socket is None:
            import zmq
            self.zmq_context = zmq.Context()
            self.zmq_socket = self.zmq_context.socket(zmq.REQ)
            self.zmq_socket.connect(f"tcp://{self.server_host}:{self.server_port}")
            logger.info(f"Connected to execution server at {self.server_host}:{self.server_port}")
    
    def _disconnect(self):
        """Close ZeroMQ connection."""
        if self.zmq_socket:
            self.zmq_socket.close()
            self.zmq_socket = None
        if self.zmq_context:
            self.zmq_context.term()
            self.zmq_context = None
    
    def run_remote_pipeline(
        self,
        plate_id: int,
        pipeline_steps: List[Any],
        global_config: Any,
        pipeline_config: Any = None,
        viewer_host: str = 'localhost',
        viewer_port: int = 5555
    ) -> Dict[str, Any]:
        """
        Execute pipeline on remote server.

        Args:
            plate_id: OMERO plate ID
            pipeline_steps: List of FunctionStep objects
            global_config: GlobalPipelineConfig instance
            pipeline_config: Optional PipelineConfig instance
            viewer_host: Host for result streaming (this machine)
            viewer_port: Port for result streaming

        Returns:
            Response from server with execution_id
        """
        # Generate pipeline code
        from openhcs.debug.pickle_to_python import generate_complete_pipeline_steps_code
        pipeline_code = generate_complete_pipeline_steps_code(pipeline_steps, clean_mode=True)

        # Generate global config code
        from openhcs.debug.pickle_to_python import generate_config_code
        from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
        config_code = generate_config_code(global_config, GlobalPipelineConfig, clean_mode=True)

        # Build request
        request = {
            'command': 'execute',
            'plate_id': plate_id,
            'pipeline_code': pipeline_code,
            'config_code': config_code,
            'client_address': f"{viewer_host}:{viewer_port}"
        }

        # Optionally add pipeline_config_code
        if pipeline_config is not None:
            pipeline_config_code = generate_config_code(pipeline_config, PipelineConfig, clean_mode=True)
            request['pipeline_config_code'] = pipeline_config_code

        # Send request
        self._connect()
        logger.info(f"Sending execution request for plate {plate_id}...")
        logger.info(f"  - Pipeline code: {len(pipeline_code)} chars")
        logger.info(f"  - Global config code: {len(config_code)} chars")
        if 'pipeline_config_code' in request:
            logger.info(f"  - Pipeline config code: {len(request['pipeline_config_code'])} chars")

        self.zmq_socket.send_json(request)

        # Receive response
        response = self.zmq_socket.recv_json()
        logger.info(f"Server response: {response.get('status')} - {response.get('message')}")

        return response
    
    def get_status(self, execution_id: Optional[str] = None) -> Dict[str, Any]:
        """
        Query execution status.
        
        Args:
            execution_id: Specific execution ID, or None for server status
        
        Returns:
            Status response
        """
        request = {'command': 'status'}
        if execution_id:
            request['execution_id'] = execution_id
        
        self._connect()
        self.zmq_socket.send_json(request)
        response = self.zmq_socket.recv_json()
        
        return response
    
    def ping(self) -> bool:
        """
        Ping server to check if alive.
        
        Returns:
            True if server responds
        """
        try:
            self._connect()
            self.zmq_socket.send_json({'command': 'ping'})
            response = self.zmq_socket.recv_json()
            return response.get('status') == 'ok'
        except Exception as e:
            logger.error(f"Ping failed: {e}")
            return False
    
    def __enter__(self):
        """Context manager entry."""
        self._connect()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit."""
        self._disconnect()

