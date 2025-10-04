#!/usr/bin/env python3
"""
OpenHCS Execution Server

Minimal server daemon for remote pipeline execution.
Receives Python code, compiles server-side, executes, streams results.
"""

import logging
import signal
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, Dict, Optional

logger = logging.getLogger(__name__)


class OpenHCSExecutionServer:
    """Server daemon for remote pipeline execution."""

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
        self.omero_data_dir = Path(omero_data_dir) if omero_data_dir else None
        self.omero_host = omero_host
        self.omero_port = omero_port
        self.omero_user = omero_user
        self.omero_password = omero_password
        self.server_port = server_port
        self.max_workers = max_workers

        self.running = False
        self.omero_conn = None
        self.zmq_context = None
        self.zmq_socket = None
        self.executor = None
        self.active_executions: Dict[str, Dict[str, Any]] = {}
        self.start_time = None

        signal.signal(signal.SIGTERM, lambda s, f: self.shutdown())
        signal.signal(signal.SIGINT, lambda s, f: self.shutdown())

    def start(self):
        """Start server: connect OMERO, register backend, listen for requests."""
        logger.info("Starting OpenHCS Execution Server...")
        self.start_time = time.time()

        self._connect_omero()
        self._register_backend()
        self._setup_zmq()

        self.executor = ThreadPoolExecutor(max_workers=self.max_workers)
        self.running = True

        logger.info("=" * 60)
        logger.info(f"OpenHCS Execution Server READY on port {self.server_port}")
        logger.info("=" * 60)

        self.run()

    def _connect_omero(self):
        """Connect to OMERO server."""
        from omero.gateway import BlitzGateway

        self.omero_conn = BlitzGateway(
            self.omero_user,
            self.omero_password,
            host=self.omero_host,
            port=self.omero_port
        )

        if not self.omero_conn.connect():
            raise RuntimeError("Failed to connect to OMERO")

        logger.info(f"✓ Connected to OMERO at {self.omero_host}:{self.omero_port}")

    def _register_backend(self):
        """Initialize and register OMERO backend."""
        from openhcs.io.omero_local import OMEROLocalBackend
        from openhcs.io.backend_registry import _backend_instances

        backend = OMEROLocalBackend(
            omero_data_dir=self.omero_data_dir,
            omero_conn=self.omero_conn
        )

        _backend_instances['omero_local'] = backend
        logger.info("✓ OMERO backend registered")

    def _setup_zmq(self):
        """Set up ZeroMQ socket."""
        import zmq

        self.zmq_context = zmq.Context()
        self.zmq_socket = self.zmq_context.socket(zmq.REP)
        self.zmq_socket.bind(f"tcp://*:{self.server_port}")

        logger.info(f"✓ Listening on tcp://*:{self.server_port}")
    
    def run(self):
        """Main server loop."""
        while self.running:
            try:
                message = self.zmq_socket.recv_json()
                response = self._handle_request(message)
                self.zmq_socket.send_json(response)
            except KeyboardInterrupt:
                break
            except Exception as e:
                logger.error(f"Error in main loop: {e}", exc_info=True)
                try:
                    self.zmq_socket.send_json({'status': 'error', 'message': str(e)})
                except:
                    pass

    def _handle_request(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """Route request to appropriate handler."""
        handlers = {
            'execute': self._handle_execute,
            'status': self._handle_status,
            'ping': lambda m: {'status': 'ok', 'message': 'pong'}
        }

        handler = handlers.get(msg.get('command'))
        if not handler:
            return {'status': 'error', 'message': f"Unknown command: {msg.get('command')}"}

        return handler(msg)

    def _handle_execute(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """Handle execution request."""
        required = ['plate_id', 'pipeline_code', 'config_code']
        if missing := [f for f in required if f not in msg]:
            return {'status': 'error', 'message': f"Missing fields: {missing}"}

        execution_id = str(uuid.uuid4())

        record = {
            'execution_id': execution_id,
            'plate_id': msg['plate_id'],
            'client_address': msg.get('client_address'),
            'status': 'accepted',
            'start_time': time.time(),
            'end_time': None,
            'error': None
        }

        self.active_executions[execution_id] = record

        record['future'] = self.executor.submit(
            self._execute_pipeline,
            execution_id,
            msg['plate_id'],
            msg['pipeline_code'],
            msg['config_code'],
            msg.get('client_address')
        )

        logger.info(f"Accepted execution {execution_id} for plate {msg['plate_id']}")

        return {
            'status': 'accepted',
            'execution_id': execution_id,
            'message': 'Pipeline execution started'
        }

    def _handle_status(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """Handle status request."""
        if execution_id := msg.get('execution_id'):
            if execution_id not in self.active_executions:
                return {'status': 'error', 'message': f"Execution not found: {execution_id}"}

            r = self.active_executions[execution_id]
            return {
                'status': 'ok',
                'execution_id': execution_id,
                'execution_status': r['status'],
                'plate_id': r['plate_id'],
                'start_time': r['start_time'],
                'end_time': r['end_time'],
                'error': r['error']
            }

        # Server status
        return {
            'status': 'ok',
            'uptime': time.time() - self.start_time if self.start_time else 0,
            'active_executions': sum(1 for r in self.active_executions.values() if r['status'] == 'running'),
            'total_executions': len(self.active_executions),
            'omero_connected': self.omero_conn and self.omero_conn.isConnected()
        }

    def _execute_pipeline(
        self,
        execution_id: str,
        plate_id: int,
        pipeline_code: str,
        config_code: str,
        client_address: Optional[str] = None
    ):
        """Execute pipeline: reconstruct from code, compile server-side, execute."""
        record = self.active_executions[execution_id]
        record['status'] = 'running'

        try:
            logger.info(f"[{execution_id}] Starting execution for plate {plate_id}")

            # Reconstruct pipeline and config from code
            namespace = {}
            exec(pipeline_code, namespace)
            exec(config_code, namespace)

            pipeline_steps = namespace.get('pipeline_steps')
            config = namespace.get('config')

            if not pipeline_steps or not config:
                raise ValueError("Code must define 'pipeline_steps' and 'config'")

            logger.info(f"[{execution_id}] Loaded {len(pipeline_steps)} steps")

            # Update streaming configs to point to client
            if client_address:
                pipeline_steps = self._update_streaming_configs(pipeline_steps, client_address)

            # Set up orchestrator
            from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
            from openhcs.io.base import storage_registry, ensure_storage_registry
            from openhcs.config_framework.lazy_factory import ensure_global_config_context
            from openhcs.core.config import GlobalPipelineConfig

            ensure_storage_registry()
            ensure_global_config_context(GlobalPipelineConfig, config)

            orchestrator = PipelineOrchestrator(
                plate_path=str(plate_id),
                storage_registry=storage_registry
            )

            orchestrator.initialize()

            # Compile and execute
            logger.info(f"[{execution_id}] Compiling pipeline...")
            compiled_contexts = orchestrator.compile_pipelines(pipeline_steps)

            logger.info(f"[{execution_id}] Executing {len(compiled_contexts)} wells...")
            orchestrator.execute_compiled_plate(
                pipeline_definition=pipeline_steps,
                compiled_contexts=compiled_contexts
            )

            # Mark completed
            record['status'] = 'completed'
            record['end_time'] = time.time()
            record['wells_processed'] = len(compiled_contexts)

            elapsed = record['end_time'] - record['start_time']
            logger.info(f"[{execution_id}] ✓ Completed in {elapsed:.1f}s")

        except Exception as e:
            record['status'] = 'error'
            record['end_time'] = time.time()
            record['error'] = str(e)
            logger.error(f"[{execution_id}] ✗ Failed: {e}", exc_info=True)

    def _update_streaming_configs(self, pipeline_steps, client_address):
        """Update streaming configs to point to client."""
        from dataclasses import replace

        client_host, _, port = client_address.rpartition(':')
        client_port = int(port) if port else 5555

        updated_steps = []
        for step in pipeline_steps:
            if hasattr(step, 'napari_streaming_config') and step.napari_streaming_config:
                new_config = replace(
                    step.napari_streaming_config,
                    napari_host=client_host,
                    napari_port=client_port
                )
                step = replace(step, napari_streaming_config=new_config)
            updated_steps.append(step)

        return updated_steps

    def shutdown(self):
        """Shutdown server gracefully."""
        logger.info("Shutting down...")
        self.running = False

        # Wait for active executions
        for execution_id, record in self.active_executions.items():
            if 'future' in record and record['status'] == 'running':
                try:
                    record['future'].result(timeout=30)
                except Exception as e:
                    logger.error(f"Error waiting for {execution_id}: {e}")

        # Clean up resources
        if self.executor:
            self.executor.shutdown(wait=True)
        if self.omero_conn:
            self.omero_conn.close()
        if self.zmq_socket:
            self.zmq_socket.close()
        if self.zmq_context:
            self.zmq_context.term()

        logger.info("Shutdown complete")


def main():
    """Entry point for execution server."""
    import argparse

    parser = argparse.ArgumentParser(description='OpenHCS Execution Server')
    parser.add_argument('--omero-data-dir', type=Path, default=None,
                       help='Path to OMERO binary repository (optional, uses API if not set)')
    parser.add_argument('--omero-host', default='localhost')
    parser.add_argument('--omero-port', type=int, default=4064)
    parser.add_argument('--omero-user', default='root')
    parser.add_argument('--omero-password', default='omero-root-password')
    parser.add_argument('--port', type=int, default=7777)
    parser.add_argument('--max-workers', type=int, default=4)
    parser.add_argument('--log-file', type=Path)
    parser.add_argument('--log-level', default='INFO', choices=['DEBUG', 'INFO', 'WARNING', 'ERROR'])

    args = parser.parse_args()

    # Set up logging
    logging.basicConfig(
        level=getattr(logging, args.log_level),
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        filename=args.log_file
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
        pass
    finally:
        server.shutdown()


if __name__ == '__main__':
    main()

