"""ZMQ Execution Server - dual-channel pattern for pipeline execution."""

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
from openhcs.runtime.zmq_messages import (
    ControlMessageType, ResponseType, ExecutionStatus, MessageFields,
    PongResponse, ExecuteRequest, ExecuteResponse, StatusRequest, CancelRequest, ProgressUpdate,
)
from openhcs.core.config import TransportMode
from openhcs.constants.constants import DEFAULT_EXECUTION_SERVER_PORT

logger = logging.getLogger(__name__)


class ZMQExecutionServer(ZMQServer):
    """ZMQ execution server for OpenHCS pipelines."""

    _server_type = 'execution'  # Registration key for AutoRegisterMeta

    def __init__(self, port=DEFAULT_EXECUTION_SERVER_PORT, host='*', log_file_path=None, transport_mode=None):
        # Use platform-aware default if not specified (TCP on Windows, IPC on Unix/Mac)
        super().__init__(port, host, log_file_path, transport_mode=transport_mode)
        self.active_executions = {}
        self.start_time = None
        self.progress_queue = queue.Queue()

        # Execution queue for sequential processing
        self.execution_queue = queue.Queue()
        self.queue_worker_thread = None
        # Don't start queue worker here - it will be started in start() after _running is set to True

    def start(self):
        """Override start to also start the queue worker thread after server is running."""
        super().start()
        # Now that _running is True, start the queue worker
        self._start_queue_worker()

    def _create_pong_response(self):
        running = [(eid, r) for eid, r in self.active_executions.items()
                   if r.get(MessageFields.STATUS) == ExecutionStatus.RUNNING.value]
        queued = [(eid, r) for eid, r in self.active_executions.items()
                  if r.get(MessageFields.STATUS) == ExecutionStatus.QUEUED.value]
        return PongResponse(
            port=self.port, control_port=self.control_port, ready=self._ready,
            server=self.__class__.__name__, log_file_path=self.log_file_path,
            active_executions=len(running) + len(queued),
            running_executions=[{
                MessageFields.EXECUTION_ID: eid, MessageFields.PLATE_ID: r.get(MessageFields.PLATE_ID, 'unknown'),
                MessageFields.START_TIME: r.get(MessageFields.START_TIME, 0),
                MessageFields.ELAPSED: time.time() - r.get(MessageFields.START_TIME, 0) if r.get(MessageFields.START_TIME) else 0
            } for eid, r in running],
            workers=self._get_worker_info(),
            uptime=time.time() - self.start_time if self.start_time else 0,
        ).to_dict()

    def process_messages(self):
        super().process_messages()
        import json
        while not self.progress_queue.empty():
            try:
                if self.data_socket:
                    self.data_socket.send_string(json.dumps(self.progress_queue.get_nowait()))
            except (queue.Empty, Exception) as e:
                if not isinstance(e, queue.Empty):
                    logger.warning(f"Failed to send progress: {e}")
                break

    def get_status_info(self):
        status = super().get_status_info()
        status.update({'active_executions': len(self.active_executions),
                      'uptime': time.time() - self.start_time if self.start_time else 0,
                      'executions': list(self.active_executions.values())})
        return status

    def handle_control_message(self, message):
        try:
            return ControlMessageType(message.get(MessageFields.TYPE)).dispatch(self, message)
        except ValueError as e:
            return ExecuteResponse(ResponseType.ERROR, error=f'Unknown message type: {message.get(MessageFields.TYPE)}').to_dict()

    def handle_data_message(self, message):
        pass

    def _validate_and_parse(self, msg, request_class):
        try:
            request = request_class.from_dict(msg)
            if hasattr(request, 'validate') and (error := request.validate()):
                return None, ExecuteResponse(ResponseType.ERROR, error=error).to_dict()
            return request, None
        except KeyError as e:
            return None, ExecuteResponse(ResponseType.ERROR, error=f'Missing field: {e}').to_dict()

    def _start_queue_worker(self):
        """Start the queue worker thread that processes executions sequentially."""
        if self.queue_worker_thread is None or not self.queue_worker_thread.is_alive():
            self.queue_worker_thread = threading.Thread(target=self._queue_worker, daemon=True)
            self.queue_worker_thread.start()
            logger.info("Started execution queue worker thread")

    def _queue_worker(self):
        """Worker thread that processes executions from the queue sequentially."""
        logger.info("Queue worker thread started - will process executions sequentially")
        try:
            while self._running:
                try:
                    # Block with timeout so we can check _running flag periodically
                    try:
                        execution_id, request, record = self.execution_queue.get(timeout=1.0)
                    except queue.Empty:
                        continue

                    logger.info(f"[{execution_id}] Dequeued for execution (queue size: {self.execution_queue.qsize()})")

                    # Check if server is still running before starting execution
                    if not self._running:
                        logger.info(f"[{execution_id}] Server shutting down, skipping execution")
                        record[MessageFields.STATUS] = ExecutionStatus.CANCELLED.value
                        self.execution_queue.task_done()
                        break

                    # Check if execution was cancelled while queued
                    if record[MessageFields.STATUS] == ExecutionStatus.CANCELLED.value:
                        logger.info(f"[{execution_id}] Execution was cancelled while queued, skipping")
                        self.execution_queue.task_done()
                        continue

                    # Run the execution (this blocks until complete)
                    self._run_execution(execution_id, request, record)

                    # Mark task as done
                    self.execution_queue.task_done()
                except Exception as e:
                    logger.error(f"Queue worker error: {e}", exc_info=True)
        finally:
            # Clean up any remaining queued executions when worker exits
            remaining = 0
            while not self.execution_queue.empty():
                try:
                    execution_id, request, record = self.execution_queue.get_nowait()
                    record[MessageFields.STATUS] = ExecutionStatus.CANCELLED.value
                    record[MessageFields.END_TIME] = time.time()
                    logger.info(f"[{execution_id}] Cancelled (was queued when server shut down)")
                    self.execution_queue.task_done()
                    remaining += 1
                except queue.Empty:
                    break

            if remaining > 0:
                logger.info(f"Cancelled {remaining} queued executions during shutdown")
            logger.info("Queue worker thread exiting")

    def _handle_execute(self, msg):
        request, error = self._validate_and_parse(msg, ExecuteRequest)
        if error:
            return error
        execution_id = str(uuid.uuid4())
        record = {MessageFields.EXECUTION_ID: execution_id, MessageFields.PLATE_ID: request.plate_id,
                  MessageFields.CLIENT_ADDRESS: request.client_address, MessageFields.STATUS: ExecutionStatus.QUEUED.value,
                  MessageFields.START_TIME: None, MessageFields.END_TIME: None, MessageFields.ERROR: None}
        self.active_executions[execution_id] = record

        # Add to queue instead of spawning a thread immediately
        self.execution_queue.put((execution_id, request, record))
        queue_position = self.execution_queue.qsize()
        logger.info(f"[{execution_id}] Queued for execution (position: {queue_position})")

        return ExecuteResponse(ResponseType.ACCEPTED, execution_id=execution_id,
                             message=f'Execution queued (position: {queue_position})').to_dict()

    def _run_execution(self, execution_id, request, record):
        try:
            # Update status to RUNNING and set start time when execution actually begins
            record[MessageFields.STATUS] = ExecutionStatus.RUNNING.value
            record[MessageFields.START_TIME] = time.time()
            logger.info(f"[{execution_id}] Starting execution (was queued)")

            results = self._execute_pipeline(execution_id, request.plate_id, request.pipeline_code,
                                            request.config_params, request.config_code,
                                            request.pipeline_config_code, request.client_address)
            logger.info(f"[{execution_id}] Pipeline execution returned, updating status to COMPLETE")
            record[MessageFields.STATUS] = ExecutionStatus.COMPLETE.value
            record[MessageFields.END_TIME] = time.time()
            record[MessageFields.RESULTS_SUMMARY] = {MessageFields.WELL_COUNT: len(results) if isinstance(results, dict) else 0,
                                                     MessageFields.WELLS: list(results.keys()) if isinstance(results, dict) else []}
            logger.info(f"[{execution_id}] ✓ Completed in {record[MessageFields.END_TIME] - record[MessageFields.START_TIME]:.1f}s")
            logger.info(f"[{execution_id}] Record status after update: {record[MessageFields.STATUS]}")
            logger.info(f"[{execution_id}] Active executions status: {self.active_executions[execution_id][MessageFields.STATUS]}")
        except Exception as e:
            from concurrent.futures.process import BrokenProcessPool
            if isinstance(e, BrokenProcessPool) and record[MessageFields.STATUS] == ExecutionStatus.CANCELLED.value:
                logger.info(f"[{execution_id}] Cancelled")
            else:
                record[MessageFields.STATUS] = ExecutionStatus.FAILED.value
                record[MessageFields.END_TIME] = time.time()
                record[MessageFields.ERROR] = str(e)
                logger.error(f"[{execution_id}] ✗ Failed: {e}", exc_info=True)
        finally:
            # Clean up orchestrator reference
            record.pop('orchestrator', None)

            # Kill all worker processes to ensure clean state for next execution
            # This prevents resource conflicts and deadlocks between consecutive executions
            killed = self._kill_worker_processes()
            if killed > 0:
                logger.info(f"[{execution_id}] Killed {killed} worker processes during cleanup")

            logger.info(f"[{execution_id}] Execution cleanup complete")
    
    def _handle_status(self, msg):
        execution_id = StatusRequest.from_dict(msg).execution_id
        if execution_id:
            if execution_id not in self.active_executions:
                return ExecuteResponse(ResponseType.ERROR, error=f'Execution {execution_id} not found').to_dict()
            r = self.active_executions[execution_id]
            return {MessageFields.STATUS: ResponseType.OK.value,
                   'execution': {k: r.get(k) for k in [MessageFields.EXECUTION_ID, MessageFields.PLATE_ID,
                                MessageFields.STATUS, MessageFields.START_TIME, MessageFields.END_TIME,
                                MessageFields.ERROR, MessageFields.RESULTS_SUMMARY]}}
        return {MessageFields.STATUS: ResponseType.OK.value, MessageFields.ACTIVE_EXECUTIONS: len(self.active_executions),
                MessageFields.UPTIME: time.time() - self.start_time if self.start_time else 0,
                MessageFields.EXECUTIONS: list(self.active_executions.keys())}

    def _handle_cancel(self, msg):
        request, error = self._validate_and_parse(msg, CancelRequest)
        if error:
            return error
        if request.execution_id not in self.active_executions:
            return ExecuteResponse(ResponseType.ERROR, error=f'Execution {request.execution_id} not found').to_dict()

        # Use the same logic as Quit button: cancel all executions and kill workers
        # This ensures workers are actually killed and the server stays alive
        self._cancel_all_executions()
        killed = self._kill_worker_processes()
        logger.info(f"[{request.execution_id}] Cancelled - killed {killed} workers")
        return {MessageFields.STATUS: ResponseType.OK.value, MessageFields.MESSAGE: f'Cancelled - killed {killed} workers',
                MessageFields.WORKERS_KILLED: killed}

    def _cancel_all_executions(self):
        for eid, r in self.active_executions.items():
            if r[MessageFields.STATUS] in (ExecutionStatus.RUNNING.value, ExecutionStatus.QUEUED.value):
                r[MessageFields.STATUS] = ExecutionStatus.CANCELLED.value
                r[MessageFields.END_TIME] = time.time()
                logger.info(f"[{eid}] Cancelled")

    def _shutdown_workers(self, force=False):
        self._cancel_all_executions()
        killed = self._kill_worker_processes()
        if force:
            self.request_shutdown()
        msg = f'Workers killed ({killed}), server {"shutting down" if force else "alive"}'
        logger.info(msg)
        return {MessageFields.TYPE: ResponseType.SHUTDOWN_ACK.value, MessageFields.STATUS: 'success', MessageFields.MESSAGE: msg}

    def _handle_shutdown(self, msg):
        return self._shutdown_workers(force=False)

    def _execute_pipeline(self, execution_id, plate_id, pipeline_code, config_params, config_code, pipeline_config_code, client_address=None):
        from openhcs.constants import AllComponents, VariableComponents, GroupBy
        from openhcs.core.config import GlobalPipelineConfig, PipelineConfig

        logger.info(f"[{execution_id}] Starting plate {plate_id}")

        # Initialize function registry BEFORE executing pipeline code
        # (pipeline code may import virtual modules like openhcs.cucim)
        import openhcs.processing.func_registry as func_registry_module
        with func_registry_module._registry_lock:
            if not func_registry_module._registry_initialized:
                func_registry_module._auto_initialize_registry()

        namespace = {}
        exec(pipeline_code, namespace)
        if not (pipeline_steps := namespace.get('pipeline_steps')):
            raise ValueError("Code must define 'pipeline_steps'")

        if config_code:
            is_empty = 'GlobalPipelineConfig(\n\n)' in config_code or 'GlobalPipelineConfig()' in config_code
            global_config = GlobalPipelineConfig() if is_empty else (exec(config_code, ns := {}) or ns.get('config'))
            if not global_config:
                raise ValueError("config_code must define 'config'")
            pipeline_config = (exec(pipeline_config_code, ns := {}) or ns.get('config')) if pipeline_config_code else PipelineConfig()
            if pipeline_config_code and not pipeline_config:
                raise ValueError("pipeline_config_code must define 'config'")
        elif config_params:
            global_config, pipeline_config = self._build_config_from_params(config_params)
        else:
            raise ValueError("Either config_params or config_code required")

        return self._execute_with_orchestrator(execution_id, plate_id, pipeline_steps, global_config, pipeline_config, config_params)

    def _build_config_from_params(self, p):
        from openhcs.core.config import GlobalPipelineConfig, MaterializationBackend, PathPlanningConfig, StepWellFilterConfig, VFSConfig, PipelineConfig
        return (GlobalPipelineConfig(
            num_workers=p.get('num_workers', 4),
            path_planning_config=PathPlanningConfig(output_dir_suffix=p.get('output_dir_suffix', '_output')),
            vfs_config=VFSConfig(materialization_backend=MaterializationBackend(p.get('materialization_backend', 'disk'))),
            step_well_filter_config=StepWellFilterConfig(well_filter=p.get('well_filter')),
            use_threading=p.get('use_threading', False),
        ), PipelineConfig())

    def _execute_with_orchestrator(self, execution_id, plate_id, pipeline_steps, global_config, pipeline_config, config_params):
        from pathlib import Path
        import multiprocessing
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        from openhcs.core.orchestrator.gpu_scheduler import setup_global_gpu_registry
        from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
        from openhcs.constants import AllComponents, VariableComponents, GroupBy, MULTIPROCESSING_AXIS
        from openhcs.io.base import reset_memory_backend, storage_registry
        from openhcs.runtime.omero_instance_manager import OMEROInstanceManager
        from openhcs.io.omero_local import OMEROLocalBackend

        try:
            if multiprocessing.get_start_method(allow_none=True) != 'spawn':
                multiprocessing.set_start_method('spawn', force=True)
        except RuntimeError:
            pass

        reset_memory_backend()

        # Trigger GPU cleanup (cache clearing) AFTER reset_memory_backend() returns
        # NOTE: We do NOT call gc.collect() here because:
        # 1. gc.collect() is synchronous and blocks until all __del__ methods complete
        # 2. __del__ methods can acquire locks (e.g., streaming backends call context.term())
        # 3. This creates deadlock potential if any lock is held when gc.collect() is called
        # 4. Python's automatic GC will collect objects eventually without blocking
        try:
            from openhcs.core.memory.gpu_cleanup import cleanup_all_gpu_frameworks
            cleanup_all_gpu_frameworks()
        except Exception as cleanup_error:
            logger.warning(f"[{execution_id}] Failed to trigger GPU cleanup: {cleanup_error}")

        setup_global_gpu_registry(global_config=global_config)
        ensure_global_config_context(type(global_config), global_config)

        # Convert OMERO plate IDs to virtual paths
        plate_path_str = str(plate_id)
        is_omero_plate_id = False
        try:
            int(plate_path_str)
            is_omero_plate_id = True
        except ValueError:
            is_omero_plate_id = plate_path_str.startswith("/omero/")

        # Connect to OMERO and convert plate ID to virtual path if needed
        if is_omero_plate_id:
            omero_manager = OMEROInstanceManager()
            if not omero_manager.connect(timeout=60):
                raise RuntimeError("OMERO server not available")
            storage_registry['omero_local'] = OMEROLocalBackend(omero_conn=omero_manager.conn)

            # Convert integer plate ID to virtual path format
            if not plate_path_str.startswith("/omero/"):
                plate_path_str = f"/omero/plate_{plate_path_str}"

        # CRITICAL: Don't pass progress_callback - it can't be pickled for ProcessPoolExecutor
        # Progress updates would need a multiprocessing-safe mechanism (e.g., Manager().Queue())
        # For now, progress is tracked via worker process monitoring in get_server_info()
        orchestrator = PipelineOrchestrator(
            plate_path=Path(plate_path_str),
            pipeline_config=pipeline_config,
            progress_callback=None  # Can't pickle lambdas for multiprocessing
        )
        orchestrator.initialize()
        self.active_executions[execution_id]['orchestrator'] = orchestrator

        # Check for cancellation after initialization (which can be slow for large plates)
        if self.active_executions[execution_id][MessageFields.STATUS] == ExecutionStatus.CANCELLED.value:
            logger.info(f"[{execution_id}] Execution cancelled after initialization, aborting")
            raise RuntimeError("Execution cancelled by user")

        wells = config_params.get('well_filter') if config_params else orchestrator.get_component_keys(MULTIPROCESSING_AXIS)
        compilation = orchestrator.compile_pipelines(pipeline_definition=pipeline_steps, well_filter=wells)

        # Check for cancellation after compilation (which can be slow for complex pipelines)
        if self.active_executions[execution_id][MessageFields.STATUS] == ExecutionStatus.CANCELLED.value:
            logger.info(f"[{execution_id}] Execution cancelled after compilation, aborting")
            raise RuntimeError("Execution cancelled by user")

        log_dir = Path.home() / ".local" / "share" / "openhcs" / "logs"
        log_dir.mkdir(parents=True, exist_ok=True)

        # Check if execution was cancelled before starting worker processes
        if self.active_executions[execution_id][MessageFields.STATUS] == ExecutionStatus.CANCELLED.value:
            logger.info(f"[{execution_id}] Execution cancelled before starting workers, aborting")
            raise RuntimeError("Execution cancelled by user")

        return orchestrator.execute_compiled_plate(pipeline_definition=pipeline_steps,
                                                   compiled_contexts=compilation['compiled_contexts'],
                                                   log_file_base=str(log_dir / f"zmq_worker_exec_{execution_id}"))

    def send_progress_update(self, well_id, step, status):
        try:
            self.progress_queue.put_nowait({'type': 'progress', 'well_id': well_id, 'step': step, 'status': status, 'timestamp': time.time()})
        except queue.Full:
            logger.warning(f"Progress queue full, dropping {well_id}")

    def _get_worker_info(self):
        try:
            import psutil
            workers = []
            for child in psutil.Process(os.getpid()).children(recursive=True):
                try:
                    cmdline = child.cmdline()
                    if not (cmdline and 'python' in cmdline[0].lower()):
                        continue
                    cmdline_str = ' '.join(cmdline)
                    # Exclude Napari, Fiji viewers, and process trackers
                    if any(x in cmdline_str.lower() for x in ['napari', 'fiji', 'resource_tracker', 'semaphore_tracker']) or child.pid == os.getpid():
                        continue
                    workers.append({'pid': child.pid, 'status': child.status(), 'cpu_percent': child.cpu_percent(interval=0),
                                   'memory_mb': child.memory_info().rss / 1024 / 1024, 'create_time': child.create_time()})
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    pass
            return workers
        except (ImportError, Exception) as e:
            logger.warning(f"Cannot get worker info: {e}")
            return []

    def _kill_worker_processes(self):
        """
        Kill all worker processes.

        First attempts graceful cancellation via orchestrator.cancel_execution(),
        then forcefully kills worker processes using psutil.

        Returns:
            int: Number of worker processes killed
        """
        # Step 1: Try graceful cancellation via orchestrator
        for eid, r in self.active_executions.items():
            if 'orchestrator' in r:
                try:
                    logger.info(f"[{eid}] Requesting graceful cancellation...")
                    r['orchestrator'].cancel_execution()
                except Exception as e:
                    logger.warning(f"[{eid}] Graceful cancellation failed: {e}")

        # Step 2: Forcefully kill worker processes using psutil
        # This ALWAYS runs, regardless of graceful cancellation
        try:
            import psutil

            # Find all child processes that are Python workers (exclude Napari and Fiji viewers)
            workers = [c for c in psutil.Process(os.getpid()).children(recursive=False)
                      if (cmd := c.cmdline()) and 'python' in cmd[0].lower()
                      and 'napari' not in ' '.join(cmd).lower()
                      and 'fiji' not in ' '.join(cmd).lower()]

            if not workers:
                logger.info("No worker processes found to kill")
                return 0

            logger.info(f"Found {len(workers)} worker processes to kill: {[w.pid for w in workers]}")

            # First try SIGTERM (graceful)
            for w in workers:
                try:
                    logger.info(f"Sending SIGTERM to worker PID {w.pid}")
                    w.terminate()
                except Exception as e:
                    logger.warning(f"Failed to terminate worker PID {w.pid}: {e}")

            # Wait up to 3 seconds for graceful shutdown
            gone, alive = psutil.wait_procs(workers, timeout=3)
            logger.info(f"After SIGTERM: {len(gone)} workers exited, {len(alive)} still alive")

            # Force kill any survivors with SIGKILL
            for w in alive:
                try:
                    logger.info(f"Force killing worker PID {w.pid} with SIGKILL")
                    w.kill()
                except Exception as e:
                    logger.warning(f"Failed to kill worker PID {w.pid}: {e}")

            logger.info(f"Successfully killed {len(workers)} worker processes")
            return len(workers)

        except (ImportError, Exception) as e:
            logger.error(f"Failed to kill worker processes: {e}")
            return 0

    def _handle_force_shutdown(self, msg):
        return self._shutdown_workers(force=True)

