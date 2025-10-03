#!/usr/bin/env python3
"""
OpenHCS Execution Server

Server daemon that listens for pipeline execution requests via ZeroMQ and executes
them on behalf of remote clients. Based on subprocess_runner pattern but adapted
for network communication.

Architecture:
- ZeroMQ REQ/REP for command protocol
- Receives Python code (not pickled objects)
- Compiles pipelines server-side (correct GPU topology, paths, backends)
- Streams results back to client via ZeroMQ PUB/SUB
- Supports concurrent executions via thread pool
"""

import json
import logging
import os
import signal
import sys
import threading
import time
import traceback
import uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, Dict, List, Optional

logger = logging.getLogger(__name__)


class OpenHCSExecutionServer:
    """
    Server daemon for remote OpenHCS pipeline execution.
    
    Listens for execution requests via ZeroMQ, executes pipelines server-side,
    and streams results back to clients.
    """
    
    def __init__(
        self,
        omero_data_dir: Optional[Path] = None,
        omero_host: str = 'localhost',
        omero_port: int = 4064,
        omero_user: str = 'root',
        omero_password: str = 'omero-root-password',
        server_port: int = 7777,
        max_workers: int = 4
    ):
        """
        Initialize execution server.
        
        Args:
            omero_data_dir: Path to OMERO binary repository (e.g., /OMERO/Files)
            omero_host: OMERO server host
            omero_port: OMERO server port
            omero_user: OMERO username
            omero_password: OMERO password
            server_port: ZeroMQ listening port for execution requests
            max_workers: Maximum concurrent executions
        """
        self.omero_data_dir = Path(omero_data_dir) if omero_data_dir else None
        self.omero_host = omero_host
        self.omero_port = omero_port
        self.omero_user = omero_user
        self.omero_password = omero_password
        self.server_port = server_port
        self.max_workers = max_workers
        
        # Server state
        self.running = False
        self.omero_conn = None
        self.zmq_context = None
        self.zmq_socket = None
        self.executor = None
        self.active_executions: Dict[str, Dict[str, Any]] = {}
        self.start_time = None
        
        # Set up signal handlers for graceful shutdown
        signal.signal(signal.SIGTERM, self._signal_handler)
        signal.signal(signal.SIGINT, self._signal_handler)
        
        logger.info(f"Initialized OpenHCSExecutionServer on port {server_port}")
    
    def _signal_handler(self, signum, frame):
        """Handle shutdown signals gracefully."""
        logger.info(f"Received signal {signum}, shutting down gracefully...")
        self.shutdown()
    
    def start(self):
        """Start the execution server."""
        logger.info("Starting OpenHCS Execution Server...")
        self.start_time = time.time()
        
        # 1. Connect to OMERO
        logger.info(f"Connecting to OMERO at {self.omero_host}:{self.omero_port}...")
        try:
            from omero.gateway import BlitzGateway
            self.omero_conn = BlitzGateway(
                self.omero_user,
                self.omero_password,
                host=self.omero_host,
                port=self.omero_port
            )
            connected = self.omero_conn.connect()
            if not connected:
                raise RuntimeError("Failed to connect to OMERO")
            logger.info("✓ Connected to OMERO")
        except Exception as e:
            logger.error(f"Failed to connect to OMERO: {e}")
            raise
        
        # 2. Initialize OMERO backend and register it
        logger.info("Initializing OMERO Local Backend...")
        try:
            from openhcs.io.omero_local import OMEROLocalBackend
            from openhcs.io.backend_registry import STORAGE_BACKENDS, _backend_instances
            
            # Create backend instance
            omero_backend = OMEROLocalBackend(
                omero_data_dir=self.omero_data_dir,
                omero_conn=self.omero_conn
            )
            
            # Register in global registry
            _backend_instances['omero_local'] = omero_backend
            logger.info("✓ OMERO backend registered")
        except Exception as e:
            logger.error(f"Failed to initialize OMERO backend: {e}")
            self.omero_conn.close()
            raise
        
        # 3. Set up ZeroMQ socket
        logger.info(f"Setting up ZeroMQ socket on port {self.server_port}...")
        try:
            import zmq
            self.zmq_context = zmq.Context()
            self.zmq_socket = self.zmq_context.socket(zmq.REP)
            self.zmq_socket.bind(f"tcp://*:{self.server_port}")
            logger.info(f"✓ Listening on tcp://*:{self.server_port}")
        except Exception as e:
            logger.error(f"Failed to set up ZeroMQ socket: {e}")
            self.omero_conn.close()
            raise
        
        # 4. Create thread pool for concurrent executions
        self.executor = ThreadPoolExecutor(max_workers=self.max_workers)
        logger.info(f"✓ Thread pool created with {self.max_workers} workers")
        
        # 5. Start main server loop
        self.running = True
        logger.info("=" * 60)
        logger.info("OpenHCS Execution Server READY")
        logger.info(f"Listening on port {self.server_port}")
        logger.info(f"OMERO: {self.omero_host}:{self.omero_port}")
        logger.info(f"Max concurrent executions: {self.max_workers}")
        logger.info("=" * 60)
        
        self.run()
    
    def run(self):
        """Main server loop - listen for requests and dispatch executions."""
        while self.running:
            try:
                # Wait for request (blocking)
                logger.debug("Waiting for execution request...")
                message = self.zmq_socket.recv_json()
                
                logger.info(f"Received request: {message.get('command', 'unknown')}")
                
                # Handle request
                response = self._handle_request(message)
                
                # Send response
                self.zmq_socket.send_json(response)
                
            except KeyboardInterrupt:
                logger.info("Keyboard interrupt received, shutting down...")
                break
            except Exception as e:
                logger.error(f"Error in main loop: {e}", exc_info=True)
                # Send error response
                try:
                    self.zmq_socket.send_json({
                        'status': 'error',
                        'message': str(e)
                    })
                except:
                    pass
        
        logger.info("Server loop exited")
    
    def _handle_request(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle incoming request.
        
        Args:
            message: Request message (JSON)
        
        Returns:
            Response message (JSON)
        """
        command = message.get('command')
        
        if command == 'execute':
            return self._handle_execute_request(message)
        elif command == 'status':
            return self._handle_status_request(message)
        elif command == 'ping':
            return {'status': 'ok', 'message': 'pong'}
        else:
            return {
                'status': 'error',
                'message': f"Unknown command: {command}"
            }
    
    def _handle_execute_request(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle pipeline execution request.
        
        Expected message format:
        {
            "command": "execute",
            "plate_id": 123,
            "pipeline_code": "...",
            "config_code": "...",
            "client_address": "192.168.1.100:5555"
        }
        """
        try:
            # Validate request
            required_fields = ['plate_id', 'pipeline_code', 'config_code']
            for field in required_fields:
                if field not in message:
                    return {
                        'status': 'error',
                        'message': f"Missing required field: {field}"
                    }
            
            # Generate execution ID
            execution_id = str(uuid.uuid4())
            
            # Create execution record
            execution_record = {
                'execution_id': execution_id,
                'plate_id': message['plate_id'],
                'client_address': message.get('client_address'),
                'status': 'accepted',
                'start_time': time.time(),
                'end_time': None,
                'error': None
            }
            self.active_executions[execution_id] = execution_record
            
            # Submit execution to thread pool
            future = self.executor.submit(
                self._execute_pipeline,
                execution_id,
                message['plate_id'],
                message['pipeline_code'],
                message['config_code'],
                message.get('client_address')
            )
            
            # Store future in execution record
            execution_record['future'] = future
            
            logger.info(f"Accepted execution {execution_id} for plate {message['plate_id']}")
            
            return {
                'status': 'accepted',
                'execution_id': execution_id,
                'message': 'Pipeline execution started'
            }
            
        except Exception as e:
            logger.error(f"Error handling execute request: {e}", exc_info=True)
            return {
                'status': 'error',
                'message': str(e)
            }
    
    def _handle_status_request(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """Handle status request."""
        execution_id = message.get('execution_id')
        
        if execution_id:
            # Status for specific execution
            if execution_id not in self.active_executions:
                return {
                    'status': 'error',
                    'message': f"Execution not found: {execution_id}"
                }
            
            record = self.active_executions[execution_id]
            return {
                'status': 'ok',
                'execution_id': execution_id,
                'execution_status': record['status'],
                'plate_id': record['plate_id'],
                'start_time': record['start_time'],
                'end_time': record['end_time'],
                'error': record['error']
            }
        else:
            # Server status
            uptime = time.time() - self.start_time if self.start_time else 0
            return {
                'status': 'ok',
                'uptime': uptime,
                'active_executions': len([r for r in self.active_executions.values() if r['status'] == 'running']),
                'total_executions': len(self.active_executions),
                'omero_connected': self.omero_conn is not None and self.omero_conn.isConnected()
            }

    def _execute_pipeline(
        self,
        execution_id: str,
        plate_id: int,
        pipeline_code: str,
        config_code: str,
        client_address: Optional[str] = None
    ):
        """
        Execute pipeline in background thread.

        This follows the subprocess_runner pattern but with server-side compilation.
        """
        record = self.active_executions[execution_id]
        record['status'] = 'running'

        try:
            logger.info(f"[{execution_id}] Starting execution for plate {plate_id}")

            # 1. Execute pipeline code to reconstruct pipeline steps
            logger.info(f"[{execution_id}] Executing pipeline code...")
            namespace = {}
            exec(pipeline_code, namespace)
            pipeline_steps = namespace.get('pipeline_steps')

            if pipeline_steps is None:
                raise ValueError("pipeline_code must define 'pipeline_steps' variable")

            logger.info(f"[{execution_id}] Pipeline has {len(pipeline_steps)} steps")

            # 2. Execute config code to reconstruct config
            logger.info(f"[{execution_id}] Executing config code...")
            exec(config_code, namespace)
            config = namespace.get('config')

            if config is None:
                raise ValueError("config_code must define 'config' variable")

            logger.info(f"[{execution_id}] Config loaded: {type(config).__name__}")

            # 3. Modify streaming config to point to client if provided
            if client_address:
                logger.info(f"[{execution_id}] Configuring streaming to client: {client_address}")
                # Parse client address
                if ':' in client_address:
                    client_host, client_port = client_address.rsplit(':', 1)
                    client_port = int(client_port)
                else:
                    client_host = client_address
                    client_port = 5555

                # Update streaming configs in pipeline steps
                for step in pipeline_steps:
                    if hasattr(step, 'napari_streaming_config') and step.napari_streaming_config:
                        # Create new config with client address
                        from openhcs.core.config import NapariStreamingConfig
                        from dataclasses import replace

                        old_config = step.napari_streaming_config
                        new_config = replace(
                            old_config,
                            napari_host=client_host,
                            napari_port=client_port
                        )
                        # Replace config (steps are frozen dataclasses, need to use replace)
                        step = replace(step, napari_streaming_config=new_config)

            # 4. Create orchestrator with OMERO backend
            logger.info(f"[{execution_id}] Creating orchestrator...")
            from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
            from openhcs.io.base import storage_registry, ensure_storage_registry

            ensure_storage_registry()

            # Set up global config context (required before orchestrator creation)
            from openhcs.config_framework.lazy_factory import ensure_global_config_context
            from openhcs.core.config import GlobalPipelineConfig
            ensure_global_config_context(GlobalPipelineConfig, config)

            orchestrator = PipelineOrchestrator(
                plate_path=str(plate_id),  # OMERO plate ID as string
                storage_registry=storage_registry
            )

            # 5. Initialize orchestrator
            logger.info(f"[{execution_id}] Initializing orchestrator...")
            orchestrator.initialize()

            # 6. Compile pipeline (server-side compilation with correct GPU topology)
            logger.info(f"[{execution_id}] Compiling pipeline...")
            compiled_contexts = orchestrator.compile_pipelines(pipeline_steps)

            wells = list(compiled_contexts.keys())
            logger.info(f"[{execution_id}] Compiled {len(wells)} wells: {wells}")

            # 7. Execute compiled plate
            logger.info(f"[{execution_id}] Executing plate...")
            orchestrator.execute_compiled_plate(
                pipeline_definition=pipeline_steps,
                compiled_contexts=compiled_contexts
            )

            # 8. Mark as completed
            record['status'] = 'completed'
            record['end_time'] = time.time()
            record['wells_processed'] = len(wells)

            elapsed = record['end_time'] - record['start_time']
            logger.info(f"[{execution_id}] ✓ Completed in {elapsed:.1f}s, processed {len(wells)} wells")

        except Exception as e:
            # Mark as error
            record['status'] = 'error'
            record['end_time'] = time.time()
            record['error'] = str(e)

            logger.error(f"[{execution_id}] ✗ Execution failed: {e}", exc_info=True)

    def shutdown(self):
        """Shutdown server gracefully."""
        logger.info("Shutting down server...")
        self.running = False

        # Wait for active executions to complete
        if self.active_executions:
            logger.info(f"Waiting for {len(self.active_executions)} active executions to complete...")
            for execution_id, record in self.active_executions.items():
                if 'future' in record and record['status'] == 'running':
                    try:
                        record['future'].result(timeout=30)  # Wait up to 30s per execution
                    except Exception as e:
                        logger.error(f"Error waiting for execution {execution_id}: {e}")

        # Shutdown thread pool
        if self.executor:
            logger.info("Shutting down thread pool...")
            self.executor.shutdown(wait=True)

        # Close OMERO connection
        if self.omero_conn:
            logger.info("Closing OMERO connection...")
            self.omero_conn.close()

        # Close ZeroMQ socket
        if self.zmq_socket:
            logger.info("Closing ZeroMQ socket...")
            self.zmq_socket.close()

        if self.zmq_context:
            self.zmq_context.term()

        logger.info("Server shutdown complete")


def main():
    """Entry point for execution server."""
    import argparse

    parser = argparse.ArgumentParser(description='OpenHCS Execution Server')
    parser.add_argument('--omero-data-dir', type=Path, default='/OMERO/Files',
                       help='Path to OMERO binary repository')
    parser.add_argument('--omero-host', default='localhost',
                       help='OMERO server host')
    parser.add_argument('--omero-port', type=int, default=4064,
                       help='OMERO server port')
    parser.add_argument('--omero-user', default='root',
                       help='OMERO username')
    parser.add_argument('--omero-password', default='omero-root-password',
                       help='OMERO password')
    parser.add_argument('--port', type=int, default=7777,
                       help='Server listening port')
    parser.add_argument('--max-workers', type=int, default=4,
                       help='Maximum concurrent executions')
    parser.add_argument('--log-file', type=Path,
                       help='Log file path (default: stdout)')
    parser.add_argument('--log-level', default='INFO',
                       choices=['DEBUG', 'INFO', 'WARNING', 'ERROR'],
                       help='Logging level')

    args = parser.parse_args()

    # Set up logging
    log_format = '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    if args.log_file:
        logging.basicConfig(
            level=getattr(logging, args.log_level),
            format=log_format,
            filename=args.log_file
        )
    else:
        logging.basicConfig(
            level=getattr(logging, args.log_level),
            format=log_format
        )

    # Create and start server
    server = OpenHCSExecutionServer(
        omero_data_dir=args.omero_data_dir,
        omero_host=args.omero_host,
        omero_port=args.omero_port,
        omero_user=args.omero_user,
        omero_password=args.omero_password,
        server_port=args.port,
        max_workers=args.max_workers
    )

    try:
        server.start()
    except KeyboardInterrupt:
        logger.info("Keyboard interrupt received")
    finally:
        server.shutdown()


if __name__ == '__main__':
    main()

