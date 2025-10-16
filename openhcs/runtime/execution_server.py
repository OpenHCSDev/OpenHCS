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
        server_port: int = 7777
    ):
        self.omero_data_dir = Path(omero_data_dir) if omero_data_dir else None
        self.omero_host = omero_host
        self.omero_port = omero_port
        self.omero_user = omero_user
        self.omero_password = omero_password
        self.server_port = server_port

        self.running = False
        self.omero_conn = None
        self.zmq_context = None
        self.zmq_socket = None
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
        """Handle execution request - executes synchronously in main thread."""
        # Require plate_id and pipeline_code
        # Accept EITHER config_params (dict) OR config_code (Python code)
        # Optionally accept pipeline_config_code for separate PipelineConfig
        # Optionally accept omero_config for OMERO mode
        if 'plate_id' not in msg or 'pipeline_code' not in msg:
            return {'status': 'error', 'message': 'Missing required fields: plate_id, pipeline_code'}

        if 'config_params' not in msg and 'config_code' not in msg:
            return {'status': 'error', 'message': 'Missing config: provide either config_params or config_code'}

        execution_id = str(uuid.uuid4())

        record = {
            'execution_id': execution_id,
            'plate_id': msg['plate_id'],
            'client_address': msg.get('client_address'),
            'status': 'running',
            'start_time': time.time(),
            'end_time': None,
            'error': None
        }

        self.active_executions[execution_id] = record

        # Execute synchronously in main thread (like UI does)
        # This ensures exec() runs in main thread, not worker thread
        try:
            results = self._execute_pipeline(
                execution_id,
                msg['plate_id'],
                msg['pipeline_code'],
                msg.get('config_params'),  # May be None
                msg.get('config_code'),    # May be None
                msg.get('pipeline_config_code'),  # May be None - separate PipelineConfig code
                msg.get('client_address'),
                msg.get('omero_config')  # May be None - OMERO connection config
            )
            record['status'] = 'complete'
            record['end_time'] = time.time()
            record['results'] = results

            return {
                'status': 'complete',
                'execution_id': execution_id,
                'results': results
            }
        except Exception as e:
            record['status'] = 'failed'
            record['end_time'] = time.time()
            record['error'] = str(e)
            logger.error(f"[{execution_id}] ✗ Failed: {e}")

            return {
                'status': 'error',
                'execution_id': execution_id,
                'message': str(e)
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

    def _setup_omero_connection(self, omero_config: dict) -> None:
        """
        Connect to OMERO and set connection on backend.

        Args:
            omero_config: {"host": ..., "port": ..., "username": ..., "password": ...}
        """
        from omero.gateway import BlitzGateway
        from openhcs.io.base import storage_registry
        from openhcs.constants.constants import Backend

        # Connect to OMERO
        self.omero_conn = BlitzGateway(
            omero_config['username'],
            omero_config['password'],
            host=omero_config['host'],
            port=omero_config.get('port', 4064)
        )

        if not self.omero_conn.connect():
            raise ConnectionError("Failed to connect to OMERO")

        # Set connection on OMERO backend
        omero_backend = storage_registry[Backend.OMERO_LOCAL.value]
        omero_backend.omero_conn = self.omero_conn

        logger.info(f"Connected to OMERO at {omero_config['host']}")

    def _teardown_omero_connection(self) -> None:
        """Close OMERO connection if open."""
        if self.omero_conn:
            self.omero_conn.close()
            self.omero_conn = None
            logger.info("Closed OMERO connection")

    def _execute_pipeline(
        self,
        execution_id: str,
        plate_id: int,
        pipeline_code: str,
        config_params: Optional[dict],
        config_code: Optional[str],
        pipeline_config_code: Optional[str],
        client_address: Optional[str] = None,
        omero_config: Optional[dict] = None
    ):
        """Execute pipeline: reconstruct from code, compile server-side, execute."""
        record = self.active_executions[execution_id]
        record['status'] = 'running'

        try:
            # OMERO-specific setup
            if omero_config:
                self._setup_omero_connection(omero_config)

            logger.info(f"[{execution_id}] Starting execution for plate {plate_id}")

            # Reconstruct pipeline by executing the exact generated Python code (same as UI)
            # Use an empty namespace so imports resolve naturally to module-level symbols
            namespace: Dict[str, Any] = {}
            exec(pipeline_code, namespace)
            pipeline_steps = namespace.get('pipeline_steps')
            if not pipeline_steps:
                raise ValueError("Code must define 'pipeline_steps'")

            logger.info(f"[{execution_id}] Loaded {len(pipeline_steps)} steps")

            # Create config - support both approaches
            if config_code:
                # Approach 1: Execute config code to get GlobalPipelineConfig object
                logger.info(f"[{execution_id}] Loading config from code...")
                # Use same namespace pattern to ensure enum identity
                from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
                config_namespace = {}
                exec(config_code, config_namespace)

                global_config = config_namespace.get('config')
                if not global_config:
                    raise ValueError("config_code must define 'config' variable")

                # Handle PipelineConfig - either from separate code or use defaults
                if pipeline_config_code:
                    logger.info(f"[{execution_id}] Loading PipelineConfig from code...")
                    pipeline_config_namespace = {}
                    exec(pipeline_config_code, pipeline_config_namespace)
                    pipeline_config = pipeline_config_namespace.get('config')
                    if not pipeline_config:
                        raise ValueError("pipeline_config_code must define 'config' variable")
                else:
                    # Use defaults
                    from openhcs.core.config import PipelineConfig
                    pipeline_config = PipelineConfig()

            elif config_params:
                # Approach 2: Build GlobalPipelineConfig/PipelineConfig directly from params
                logger.info(f"[{execution_id}] Creating config from params...")
                from openhcs.core.config import (
                    GlobalPipelineConfig,
                    MaterializationBackend,
                    PathPlanningConfig,
                    StepWellFilterConfig,
                    VFSConfig,
                    ZarrConfig,
                    PipelineConfig,
                )
                from openhcs.constants.constants import Backend

                # OMERO mode overrides
                if omero_config:
                    config_params['read_backend'] = Backend.OMERO_LOCAL.value
                    config_params['materialization_backend'] = 'zarr'  # Force zarr for OMERO

                global_config = GlobalPipelineConfig(
                    num_workers=config_params.get('num_workers', 4),
                    path_planning_config=PathPlanningConfig(
                        output_dir_suffix=config_params.get('output_dir_suffix', '_output')
                    ),
                    vfs_config=VFSConfig(
                        read_backend=Backend(config_params.get('read_backend', 'auto')),
                        materialization_backend=MaterializationBackend(
                            config_params.get('materialization_backend', 'disk')
                        )
                    ),
                    zarr_config=ZarrConfig(),
                    step_well_filter_config=StepWellFilterConfig(
                        well_filter=config_params.get('well_filter')
                    ),
                    use_threading=config_params.get('use_threading', False),
                )
                pipeline_config = PipelineConfig()
            else:
                raise ValueError("Either config_params or config_code must be provided")

            # Update streaming configs to point to client
            if client_address:
                pipeline_steps = self._update_streaming_configs(pipeline_steps, client_address)

            # Set up orchestrator exactly like test_main.py (no special transport)
            from pathlib import Path
            from openhcs.config_framework.global_config import ensure_global_config_context
            from openhcs.core.orchestrator.gpu_scheduler import setup_global_gpu_registry
            from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
            from openhcs.constants import MULTIPROCESSING_AXIS
            from openhcs.io.base import reset_memory_backend

            # Reset ephemeral backends and initialize GPU registry
            reset_memory_backend()
            setup_global_gpu_registry()

            # Install global config context for dual-axis resolver
            ensure_global_config_context(type(global_config), global_config)

            orchestrator = PipelineOrchestrator(
                plate_path=Path(f"/omero/plate_{plate_id}"),
                pipeline_config=pipeline_config
            )
            orchestrator.initialize()

            # Execute using standard compile→execute phases
            logger.info(f"[{execution_id}] Executing pipeline...")

            # Determine wells to process
            if config_params and config_params.get('well_filter'):
                wells = config_params['well_filter']
            elif hasattr(global_config, 'step_well_filter_config') and global_config.step_well_filter_config and global_config.step_well_filter_config.well_filter:
                wells = global_config.step_well_filter_config.well_filter
            else:
                wells = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)

            compilation = orchestrator.compile_pipelines(
                pipeline_definition=pipeline_steps,
                well_filter=wells,
            )
            compiled_contexts = compilation['compiled_contexts']

            results = orchestrator.execute_compiled_plate(
                pipeline_definition=pipeline_steps,
                compiled_contexts=compiled_contexts,
            )

            # Mark completed
            record['status'] = 'completed'
            record['end_time'] = time.time()
            record['wells_processed'] = len(results.get('well_results', {}))

            elapsed = record['end_time'] - record['start_time']
            logger.info(f"[{execution_id}] ✓ Completed in {elapsed:.1f}s")
            return results

        except Exception as e:
            record['status'] = 'error'
            record['end_time'] = time.time()
            record['error'] = str(e)
            logger.error(f"[{execution_id}] ✗ Failed: {e}", exc_info=True)
            raise

        finally:
            # OMERO-specific teardown
            if omero_config:
                self._teardown_omero_connection()

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

        # Clean up resources
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
        server_port=args.port
    )

    try:
        server.start()
    except KeyboardInterrupt:
        pass
    finally:
        server.shutdown()


if __name__ == '__main__':
    main()

