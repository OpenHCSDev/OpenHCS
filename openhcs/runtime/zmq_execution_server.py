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
import threading
import queue
import os
import signal
from pathlib import Path
from typing import Any, Dict, Optional, List
from openhcs.runtime.zmq_base import ZMQServer

logger = logging.getLogger(__name__)


class ZMQExecutionServer(ZMQServer):
    """
    ZMQ-based execution server for OpenHCS pipelines.

    Receives pipeline code and config code via control channel,
    executes pipelines, and streams progress via data channel.
    """

    def __init__(self, port: int = 7777, host: str = '*', log_file_path: Optional[str] = None):
        """
        Initialize execution server.

        Args:
            port: Data port (control port will be port + 1000)
            host: Host to bind to (default: '*' for all interfaces)
            log_file_path: Path to server log file (for client discovery)
        """
        super().__init__(port, host, log_file_path)
        self.active_executions: Dict[str, Dict[str, Any]] = {}
        self.start_time = None
        # Thread-safe queue for progress updates from background threads
        self.progress_queue: queue.Queue = queue.Queue()
    
    def _create_pong_response(self) -> Dict[str, Any]:
        """Create pong response with execution server info."""
        response = super()._create_pong_response()

        # Count only RUNNING executions
        running_count = sum(1 for record in self.active_executions.values()
                           if record.get('status') == 'running')

        # Get list of running execution details for UI display
        running_executions = []
        for exec_id, record in self.active_executions.items():
            if record.get('status') == 'running':
                running_executions.append({
                    'execution_id': exec_id,
                    'plate_id': record.get('plate_id', 'unknown'),
                    'start_time': record.get('start_time', 0),
                    'elapsed': time.time() - record.get('start_time', 0) if record.get('start_time') else 0
                })

        # Get worker process information
        logger.debug(f"🔍 PONG: Getting worker info (running executions: {running_count})")
        workers = self._get_worker_info()
        logger.debug(f"🔍 PONG: Got {len(workers)} workers")

        response.update({
            'server': 'ZMQExecutionServer',
            'active_executions': running_count,
            'running_executions': running_executions,  # Detailed list for UI
            'workers': workers,  # Worker process info for hierarchical display
            'uptime': time.time() - self.start_time if self.start_time else 0
        })
        if self.log_file_path:
            response['log_file_path'] = self.log_file_path
        return response

    def process_messages(self):
        """
        Process control messages and drain progress queue.

        Overrides parent to also send queued progress updates from background threads.
        """
        # First process control messages (ping/pong, execute, status, etc.)
        super().process_messages()

        # Then drain progress queue and send updates (thread-safe)
        import json
        while not self.progress_queue.empty():
            try:
                message = self.progress_queue.get_nowait()
                if self.data_socket:
                    self.data_socket.send_string(json.dumps(message))
            except queue.Empty:
                break
            except Exception as e:
                logger.warning(f"Failed to send queued progress update: {e}")

    def get_status_info(self) -> Dict[str, Any]:
        """Get server status with execution progress information."""
        status = super().get_status_info()
        status.update({
            'active_executions': len(self.active_executions),
            'uptime': time.time() - self.start_time if self.start_time else 0,
            'executions': list(self.active_executions.values())
        })
        return status

    def handle_control_message(self, message: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle control channel messages.

        Supported message types:
        - execute: Execute pipeline
        - status: Query execution status
        - cancel: Cancel execution (kills workers for specific execution)
        - shutdown: Graceful shutdown (kills all workers, server stays alive)
        - force_shutdown: Force shutdown (kills workers AND server)
        """
        msg_type = message.get('type')

        if msg_type == 'execute':
            return self._handle_execute(message)
        elif msg_type == 'status':
            return self._handle_status(message)
        elif msg_type == 'cancel':
            return self._handle_cancel(message)
        elif msg_type == 'shutdown':
            return self._handle_shutdown(message)
        elif msg_type == 'force_shutdown':
            return self._handle_force_shutdown(message)
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
        Handle execution request - executes asynchronously in background thread.

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

        # Execute asynchronously in background thread so server can continue processing control messages
        def execute_in_background():
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
                # Store serializable summary instead of full results (which may contain unpicklable objects)
                record['results_summary'] = {
                    'well_count': len(results) if isinstance(results, dict) else 0,
                    'wells': list(results.keys()) if isinstance(results, dict) else []
                }
                logger.info(f"[{execution_id}] ✓ Completed in {record['end_time'] - record['start_time']:.1f}s")
            except Exception as e:
                # Check if this is a BrokenProcessPool due to intentional cancellation
                from concurrent.futures.process import BrokenProcessPool
                if isinstance(e, BrokenProcessPool) and record['status'] == 'cancelled':
                    # This is expected - workers were killed intentionally
                    logger.info(f"[{execution_id}] Execution cancelled - workers were terminated")
                else:
                    # Unexpected failure
                    record['status'] = 'failed'
                    record['end_time'] = time.time()
                    record['error'] = str(e)
                    logger.error(f"[{execution_id}] ✗ Failed: {e}", exc_info=True)
            finally:
                # Clean up unpicklable objects from record
                if 'orchestrator' in record:
                    del record['orchestrator']

        # Start background thread
        thread = threading.Thread(target=execute_in_background, daemon=True)
        thread.start()

        # Return immediately with execution_id (client can poll for status)
        return {
            'status': 'accepted',
            'execution_id': execution_id,
            'message': 'Execution started in background'
        }
    
    def _handle_status(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """Handle status request."""
        execution_id = msg.get('execution_id')

        if execution_id:
            # Status for specific execution
            if execution_id in self.active_executions:
                record = self.active_executions[execution_id]
                # Filter out unpicklable objects (orchestrator, results, etc.)
                # Only include basic status fields that are guaranteed to be picklable
                serializable_record = {
                    'execution_id': record.get('execution_id'),
                    'plate_id': record.get('plate_id'),
                    'status': record.get('status'),
                    'start_time': record.get('start_time'),
                    'end_time': record.get('end_time'),
                    'error': record.get('error'),
                    'results_summary': record.get('results_summary')
                }
                return {
                    'status': 'ok',
                    'execution': serializable_record
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
        """Handle cancellation request - kill worker processes for the execution."""
        execution_id = msg.get('execution_id')

        if not execution_id:
            return {
                'status': 'error',
                'message': 'Missing execution_id'
            }

        if execution_id not in self.active_executions:
            return {
                'status': 'error',
                'message': f'Execution {execution_id} not found'
            }

        logger.info(f"[{execution_id}] Cancellation requested - killing worker processes")

        # CRITICAL: Mark execution as cancelled BEFORE killing workers
        # This prevents race condition where BrokenProcessPool is raised before status is set
        record = self.active_executions[execution_id]
        record['status'] = 'cancelled'
        record['end_time'] = time.time()

        # Kill all worker processes spawned by this server
        killed_count = self._kill_worker_processes()

        logger.info(f"[{execution_id}] Cancelled - killed {killed_count} worker processes")

        return {
            'status': 'ok',
            'message': f'Execution cancelled - killed {killed_count} worker processes',
            'workers_killed': killed_count
        }

    def _cancel_all_executions(self) -> None:
        """Mark all active executions as cancelled."""
        for execution_id, record in self.active_executions.items():
            if record['status'] == 'running':
                record['status'] = 'cancelled'
                record['end_time'] = time.time()
                logger.info(f"[{execution_id}] Marked as cancelled")

    def _handle_shutdown(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle graceful shutdown request - kills workers only, server stays alive.

        This allows the server to remain available for new executions while
        terminating any currently running workers.
        """
        logger.info("Shutdown requested via control channel - killing workers only")
        # CRITICAL: Mark executions as cancelled BEFORE killing workers
        # This prevents race condition where BrokenProcessPool is raised before status is set
        self._cancel_all_executions()
        killed_count = self._kill_worker_processes()
        logger.info(f"Shutdown complete - killed {killed_count} workers, server remains alive")

        return {
            'type': 'shutdown_ack',
            'status': 'success',
            'message': f'Workers terminated ({killed_count} killed), server remains alive'
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
        # CRITICAL: Force enum creation BEFORE any exec() to ensure pickle identity
        # This must happen before exec(pipeline_code) or exec(config_code)
        from openhcs.constants import AllComponents, VariableComponents, GroupBy
        logger.debug(f"🔧 ENUM INIT: Forced enum creation in _execute_pipeline (VariableComponents={id(VariableComponents)})")

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

                # Check if config code is empty (just creates default config)
                # Empty config code looks like: "config = GlobalPipelineConfig(\n\n)"
                is_empty_config = 'GlobalPipelineConfig(\n\n)' in config_code or 'GlobalPipelineConfig()' in config_code

                if is_empty_config:
                    # Use direct instantiation for empty configs to avoid import issues
                    logger.info(f"[{execution_id}] Using default GlobalPipelineConfig (empty config code)")
                    global_config = GlobalPipelineConfig()
                else:
                    # Execute non-empty config code
                    logger.info(f"🔍 SERVER DEBUG: Received GlobalPipelineConfig code:\n{config_code}")
                    config_namespace = {}
                    exec(config_code, config_namespace)

                    global_config = config_namespace.get('config')
                    if not global_config:
                        raise ValueError("config_code must define 'config' variable")

                    logger.info(f"🔍 SERVER DEBUG: Recreated GlobalPipelineConfig")
                    logger.info(f"🔍 SERVER DEBUG: global_config.zarr_config type: {type(global_config.zarr_config)}")
                    logger.info(f"🔍 SERVER DEBUG: global_config.zarr_config.compressor: {global_config.zarr_config.compressor}")

                # Handle PipelineConfig
                if pipeline_config_code:
                    logger.info(f"🔍 SERVER DEBUG: Received PipelineConfig code:\n{pipeline_config_code}")
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
        import multiprocessing
        import logging
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        from openhcs.core.orchestrator.gpu_scheduler import setup_global_gpu_registry
        from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
        from openhcs.constants import MULTIPROCESSING_AXIS
        from openhcs.io.base import reset_memory_backend

        logger = logging.getLogger(__name__)

        # CRITICAL: Force enum creation BEFORE multiprocessing to ensure identity consistency
        # The lazy __getattr__ in constants.py creates enums on first access and stores them in globals()
        # We must do this in the parent process so worker processes inherit the same enum objects
        from openhcs.constants import AllComponents, VariableComponents, GroupBy
        logger.debug(f"🔧 ENUM INIT: Forced enum creation before multiprocessing (AllComponents={id(AllComponents)}, VariableComponents={id(VariableComponents)})")

        # CUDA COMPATIBILITY: Set spawn method for multiprocessing to support CUDA
        try:
            current_method = multiprocessing.get_start_method(allow_none=True)
            if current_method != 'spawn':
                logger.info(f"🔥 CUDA: Setting multiprocessing start method from '{current_method}' to 'spawn' for CUDA compatibility")
                multiprocessing.set_start_method('spawn', force=True)
            else:
                logger.debug("🔥 CUDA: Multiprocessing start method already set to 'spawn'")
        except RuntimeError as e:
            # Start method may already be set, which is fine
            logger.debug(f"🔥 CUDA: Start method already configured: {e}")

        # Reset ephemeral backends and initialize GPU registry
        reset_memory_backend()
        setup_global_gpu_registry(global_config=global_config)

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

        # Execute using standard compile→execute phases
        logger.info(f"[{execution_id}] Executing pipeline...")

        # Determine wells to process
        # Always get wells from orchestrator (matches direct mode behavior)
        # config_params['well_filter'] can optionally provide a pre-computed list
        if config_params and config_params.get('well_filter'):
            wells = config_params['well_filter']
        else:
            wells = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)

        compilation = orchestrator.compile_pipelines(
            pipeline_definition=pipeline_steps,
            well_filter=wells,
        )
        compiled_contexts = compilation['compiled_contexts']

        # Create log file base for worker processes
        from pathlib import Path
        log_dir = Path.home() / ".local" / "share" / "openhcs" / "logs"
        log_dir.mkdir(parents=True, exist_ok=True)
        log_file_base = str(log_dir / f"zmq_worker_exec_{execution_id}")

        results = orchestrator.execute_compiled_plate(
            pipeline_definition=pipeline_steps,
            compiled_contexts=compiled_contexts,
            log_file_base=log_file_base
        )

        return results

    def send_progress_update(self, well_id: str, step: str, status: str):
        """
        Send progress update to clients via data channel.

        Thread-safe: Queues the message for the main thread to send.

        Args:
            well_id: Well identifier
            step: Step name
            status: Status message
        """
        message = {
            'type': 'progress',
            'well_id': well_id,
            'step': step,
            'status': status,
            'timestamp': time.time()
        }

        # Queue the message for main thread to send (ZMQ sockets are not thread-safe)
        try:
            self.progress_queue.put_nowait(message)
        except queue.Full:
            logger.warning(f"Progress queue full, dropping update for {well_id}")

    def _get_worker_info(self) -> List[Dict[str, Any]]:
        """
        Get information about worker processes.

        Returns list of worker process info dicts with pid, status, etc.
        """
        workers = []

        try:
            import psutil
        except ImportError:
            logger.warning("psutil not available - cannot get worker info")
            return workers

        try:
            current_process = psutil.Process(os.getpid())

            # Try both direct children and recursive (workers might be grandchildren)
            direct_children = current_process.children(recursive=False)
            all_descendants = current_process.children(recursive=True)

            logger.info(f"🔍 WORKER DETECTION: Server PID {os.getpid()}")
            logger.info(f"🔍 WORKER DETECTION: Found {len(direct_children)} direct children, {len(all_descendants)} total descendants")

            # Check all descendants (workers might be spawned by a subprocess)
            for child in all_descendants:
                try:
                    # Check if it's a Python worker process
                    cmdline = child.cmdline()
                    cmdline_preview = ' '.join(cmdline[:3]) if cmdline else 'None'
                    logger.info(f"🔍 WORKER DETECTION: Descendant PID {child.pid} cmdline: {cmdline_preview}...")

                    if cmdline and len(cmdline) > 0 and 'python' in cmdline[0].lower():
                        cmdline_str = ' '.join(cmdline)

                        # Exclude Napari viewers
                        if 'napari' in cmdline_str.lower():
                            logger.info(f"🔍 WORKER DETECTION: Skipping Napari viewer PID {child.pid}")
                            continue

                        # Exclude multiprocessing helper processes (infrastructure, not workers)
                        # resource_tracker and semaphore_tracker are helpers
                        # BUT spawn_main is the actual worker process!
                        if 'resource_tracker' in cmdline_str or 'semaphore_tracker' in cmdline_str:
                            logger.info(f"🔍 WORKER DETECTION: Skipping multiprocessing helper PID {child.pid}")
                            continue

                        # Exclude the server process itself (shouldn't happen but be safe)
                        if child.pid == os.getpid():
                            continue

                        # Include all other Python processes as potential workers
                        # ProcessPoolExecutor workers are just spawned Python processes
                        logger.info(f"🔍 WORKER DETECTION: ✅ Identified worker PID {child.pid}")
                        workers.append({
                            'pid': child.pid,
                            'status': child.status(),
                            'cpu_percent': child.cpu_percent(interval=0),  # Non-blocking (returns 0.0 on first call)
                            'memory_mb': child.memory_info().rss / 1024 / 1024,
                            'create_time': child.create_time()
                        })
                    else:
                        logger.info(f"🔍 WORKER DETECTION: Skipping non-Python process PID {child.pid}")
                except (psutil.NoSuchProcess, psutil.AccessDenied) as e:
                    logger.debug(f"🔍 WORKER DETECTION: Cannot access process: {e}")

        except Exception as e:
            logger.warning(f"Error getting worker info: {e}", exc_info=True)

        logger.info(f"🔍 WORKER DETECTION: Returning {len(workers)} workers")
        return workers

    def _kill_worker_processes(self) -> int:
        """
        Kill worker processes spawned by ProcessPoolExecutor.

        This method attempts to gracefully shutdown executors via orchestrator first,
        then falls back to killing only Python worker processes (not all children like Napari viewers).
        """
        killed_count = 0

        # First, try to gracefully cancel via orchestrator
        for execution_id, record in self.active_executions.items():
            if 'orchestrator' in record:
                try:
                    orchestrator = record['orchestrator']
                    logger.info(f"[{execution_id}] Gracefully cancelling execution via orchestrator")
                    orchestrator.cancel_execution()
                    killed_count += 1
                except Exception as e:
                    logger.warning(f"[{execution_id}] Failed to cancel via orchestrator: {e}")

        # If we successfully shutdown executors, return
        if killed_count > 0:
            logger.info(f"Gracefully shutdown {killed_count} executor(s)")
            return killed_count

        # Fallback: Kill only Python worker processes (not all children)
        # This avoids killing Napari viewers and other independent child processes
        try:
            import psutil
        except ImportError:
            logger.warning("psutil not available - cannot kill worker processes")
            return 0

        try:
            current_process = psutil.Process(os.getpid())
            children = current_process.children(recursive=False)  # Non-recursive to avoid Napari

            if not children:
                return 0

            # Filter for Python processes that look like workers or helper processes
            # We want to kill workers AND multiprocessing helpers (resource_tracker, etc.)
            # but NOT Napari viewers
            worker_processes = []
            for child in children:
                try:
                    # Check if it's a Python process
                    cmdline = child.cmdline()
                    if cmdline and 'python' in cmdline[0].lower():
                        cmdline_str = ' '.join(cmdline)
                        # Exclude Napari viewers (they should stay alive)
                        if 'napari' not in cmdline_str.lower():
                            # Include workers AND helper processes (resource_tracker, etc.)
                            worker_processes.append(child)
                            logger.debug(f"Will kill child process PID {child.pid}: {cmdline_str[:100]}")
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    pass

            if not worker_processes:
                logger.info("No worker processes found to kill")
                return 0

            logger.info(f"Killing {len(worker_processes)} worker processes")

            # Terminate worker processes
            for child in worker_processes:
                try:
                    child.terminate()
                except (psutil.NoSuchProcess, Exception):
                    pass

            # Wait for graceful exit, then force kill stragglers
            gone, alive = psutil.wait_procs(worker_processes, timeout=3)
            for child in alive:
                try:
                    child.kill()
                except (psutil.NoSuchProcess, Exception):
                    pass

            return len(worker_processes)

        except Exception as e:
            logger.error(f"Error killing worker processes: {e}")
            return 0

    def _handle_force_shutdown(self, msg: Dict[str, Any]) -> Dict[str, Any]:
        """
        Handle force shutdown request - kills workers AND shuts down server.

        This is the nuclear option that terminates everything.
        """
        logger.info("Force shutdown requested - killing workers and shutting down server")
        # CRITICAL: Mark executions as cancelled BEFORE killing workers
        # This prevents race condition where BrokenProcessPool is raised before status is set
        self._cancel_all_executions()
        killed_count = self._kill_worker_processes()
        self.request_shutdown()
        logger.info(f"Force shutdown complete - killed {killed_count} workers, server shutting down")

        return {
            'type': 'shutdown_ack',
            'status': 'success',
            'message': f'Force shutdown complete - killed {killed_count} workers, server shutting down'
        }

