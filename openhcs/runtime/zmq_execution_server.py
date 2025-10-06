"""
ZMQ Execution Server - Receives and executes OpenHCS pipelines via ZMQ.

This server uses the dual-channel ZMQ pattern extracted from Napari:
- Control channel: Handles ping/pong, execute requests, status queries, cancellation
- Data channel: Streams progress updates back to clients

The server can run locally (subprocess) or remotely (network), providing
location-transparent execution.
"""

import logging
import time
import uuid
import zmq
from pathlib import Path
from typing import Any, Dict, Optional
from openhcs.runtime.zmq_base import ZMQServer

logger = logging.getLogger(__name__)


class ZMQExecutionServer(ZMQServer):
    """
    ZMQ-based execution server for OpenHCS pipelines.
    
    Receives pipeline code and config code via control channel,
    executes pipelines, and streams progress via data channel.
    """
    
    def __init__(self, port: int = 7777, host: str = '*'):
        """
        Initialize execution server.
        
        Args:
            port: Data port (control port will be port + 1000)
            host: Host to bind to (default: '*' for all interfaces)
        """
        super().__init__(port, host)
        self.active_executions: Dict[str, Dict[str, Any]] = {}
        self.start_time = None
    
    def _create_pong_response(self) -> Dict[str, Any]:
        """Create pong response with execution server info."""
        return {
            'type': 'pong',
            'ready': self._ready,
            'server': 'ZMQExecutionServer',
            'active_executions': len(self.active_executions),
            'uptime': time.time() - self.start_time if self.start_time else 0
        }
    
    def handle_control_message(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle control channel messages.
        
        Supported message types:
        - execute: Execute pipeline
        - status: Query execution status
        - cancel: Cancel execution (not yet implemented)
        """
        msg_type = message.get('type')
        
        if msg_type == 'execute':
            return self._handle_execute(message)
        elif msg_type == 'status':
            return self._handle_status(message)
        elif msg_type == 'cancel':
            return self._handle_cancel(message)
        else:
            return {'status': 'error', 'message': f'Unknown message type: {msg_type}'}
    
    def handle_data_message(self, message: Dict[str, Any]):
        """
        Handle data channel messages.
        
        For execution server, we don't receive data messages - we only send them
        (progress updates). This is a no-op.
        """
        pass
    
    def _handle_execute(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle execution request - executes synchronously in main thread.
        
        Required fields:
        - plate_id: Plate identifier (path or ID)
        - pipeline_code: Python code defining pipeline_steps
        
        Config options (one required):
        - config_params: Dict of config parameters
        - config_code: Python code defining global_config
        
        Optional fields:
        - pipeline_config_code: Python code defining pipeline_config
        - client_address: Address for streaming results
        """
        # Validate required fields
        if 'plate_id' not in msg or 'pipeline_code' not in msg:
            return {'status': 'error', 'message': 'Missing required fields: plate_id, pipeline_code'}
        
        if 'config_params' not in msg and 'config_code' not in msg:
            return {'status': 'error', 'message': 'Missing config: provide either config_params or config_code'}
        
        execution_id = str(uuid.uuid4())
        
        # Create execution record
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
        try:
            results = self._execute_pipeline(
                execution_id,
                msg['plate_id'],
                msg['pipeline_code'],
                msg.get('config_params'),
                msg.get('config_code'),
                msg.get('pipeline_config_code'),
                msg.get('client_address')
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
            logger.error(f"[{execution_id}] ✗ Failed: {e}", exc_info=True)
            
            return {
                'status': 'error',
                'execution_id': execution_id,
                'message': str(e)
            }
    
    def _handle_status(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """Handle status request."""
        execution_id = msg.get('execution_id')
        
        if execution_id:
            # Status for specific execution
            if execution_id in self.active_executions:
                record = self.active_executions[execution_id]
                return {
                    'status': 'ok',
                    'execution': record
                }
            else:
                return {
                    'status': 'error',
                    'message': f'Execution {execution_id} not found'
                }
        else:
            # Overall server status
            return {
                'status': 'ok',
                'active_executions': len(self.active_executions),
                'uptime': time.time() - self.start_time if self.start_time else 0,
                'executions': list(self.active_executions.keys())
            }
    
    def _handle_cancel(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """Handle cancellation request."""
        execution_id = msg.get('execution_id')

        if not execution_id:
            return {
                'status': 'error',
                'message': 'Missing execution_id'
            }

        # Find the orchestrator for this execution
        if execution_id not in self.active_executions:
            return {
                'status': 'error',
                'message': f'No active execution found for {execution_id}'
            }

        execution_info = self.active_executions[execution_id]
        orchestrator = execution_info.get('orchestrator')

        if not orchestrator:
            return {
                'status': 'error',
                'message': f'No orchestrator found for execution {execution_id}'
            }

        # Request cancellation
        try:
            orchestrator.cancel()
            logger.info(f"🛑 Cancellation requested for execution {execution_id}")
            return {
                'status': 'ok',
                'message': f'Cancellation requested for {execution_id}'
            }
        except Exception as e:
            logger.error(f"Failed to cancel execution {execution_id}: {e}")
            return {
                'status': 'error',
                'message': f'Failed to cancel: {str(e)}'
            }
    
    def _execute_pipeline(
        self,
        execution_id: str,
        plate_id: str,
        pipeline_code: str,
        config_params: Optional[dict],
        config_code: Optional[str],
        pipeline_config_code: Optional[str],
        client_address: Optional[str] = None
    ):
        """
        Execute pipeline: reconstruct from code, compile server-side, execute.
        
        This mirrors the execution_server.py implementation exactly.
        """
        record = self.active_executions[execution_id]
        
        try:
            logger.info(f"[{execution_id}] Starting execution for plate {plate_id}")
            
            # Reconstruct pipeline by executing the exact generated Python code
            namespace: Dict[str, Any] = {}
            exec(pipeline_code, namespace)
            pipeline_steps = namespace.get('pipeline_steps')
            if not pipeline_steps:
                raise ValueError("Code must define 'pipeline_steps'")
            
            logger.info(f"[{execution_id}] Loaded {len(pipeline_steps)} steps")
            
            # Create config - support both approaches
            if config_code:
                # Approach 1: Execute config code
                from openhcs.core.config import GlobalPipelineConfig, PipelineConfig
                config_namespace = {}
                exec(config_code, config_namespace)
                
                global_config = config_namespace.get('config')
                if not global_config:
                    raise ValueError("config_code must define 'config' variable")
                
                # Handle PipelineConfig
                if pipeline_config_code:
                    pipeline_config_namespace = {}
                    exec(pipeline_config_code, pipeline_config_namespace)
                    pipeline_config = pipeline_config_namespace.get('config')
                    if not pipeline_config:
                        raise ValueError("pipeline_config_code must define 'config' variable")
                else:
                    pipeline_config = PipelineConfig()
            
            elif config_params:
                # Approach 2: Build from params
                global_config, pipeline_config = self._build_config_from_params(config_params)
            else:
                raise ValueError("Either config_params or config_code must be provided")
            
            # Execute using standard orchestrator pattern
            results = self._execute_with_orchestrator(
                execution_id,
                plate_id,
                pipeline_steps,
                global_config,
                pipeline_config,
                config_params
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

    def _build_config_from_params(self, config_params: dict):
        """Build GlobalPipelineConfig and PipelineConfig from parameters."""
        from openhcs.core.config import (
            GlobalPipelineConfig,
            MaterializationBackend,
            PathPlanningConfig,
            StepWellFilterConfig,
            VFSConfig,
            ZarrConfig,
            PipelineConfig,
        )

        global_config = GlobalPipelineConfig(
            num_workers=config_params.get('num_workers', 4),
            path_planning_config=PathPlanningConfig(
                output_dir_suffix=config_params.get('output_dir_suffix', '_output')
            ),
            vfs_config=VFSConfig(
                materialization_backend=MaterializationBackend(
                    config_params.get('materialization_backend', 'disk')
                )
            ),
            zarr_config=ZarrConfig(
                store_name='images.zarr',
                ome_zarr_metadata=True,
                write_plate_metadata=True,
            ),
            step_well_filter_config=StepWellFilterConfig(
                well_filter=config_params.get('well_filter')
            ),
            use_threading=config_params.get('use_threading', False),
        )
        pipeline_config = PipelineConfig()

        return global_config, pipeline_config

    def _execute_with_orchestrator(
        self,
        execution_id: str,
        plate_id: str,
        pipeline_steps,
        global_config,
        pipeline_config,
        config_params: Optional[dict]
    ):
        """Execute pipeline using standard orchestrator pattern."""
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

        # Create progress callback that sends updates via ZMQ
        def progress_callback(axis_id: str, step: str, status: str, metadata: dict):
            """Send progress update via ZMQ data channel."""
            self.send_progress_update(axis_id, step, status)

        orchestrator = PipelineOrchestrator(
            plate_path=Path(str(plate_id)),
            pipeline_config=pipeline_config,
            progress_callback=progress_callback
        )
        orchestrator.initialize()

        # Store orchestrator in active_executions for cancellation support
        record = self.active_executions[execution_id]
        record['orchestrator'] = orchestrator

        # Reset cancellation flag before execution
        orchestrator.reset_cancellation()

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

        return results

    def send_progress_update(self, well_id: str, step: str, status: str):
        """
        Send progress update to clients via data channel.

        Args:
            well_id: Well identifier
            step: Step name
            status: Status message
        """
        if not self.data_socket:
            return

        import json

        message = {
            'type': 'progress',
            'well_id': well_id,
            'step': step,
            'status': status,
            'timestamp': time.time()
        }

        try:
            self.data_socket.send_string(json.dumps(message))
        except Exception as e:
            logger.warning(f"Failed to send progress update: {e}")

