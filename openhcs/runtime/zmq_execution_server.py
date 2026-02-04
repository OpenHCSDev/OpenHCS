"""OpenHCS execution server built on zmqruntime ExecutionServer."""

from __future__ import annotations

import logging
import time
import threading
from typing import Any

from zmqruntime.execution import ExecutionServer
from zmqruntime.messages import (
    ExecuteRequest,
    ExecuteResponse,
    ExecutionStatus,
    MessageFields,
    ResponseType,
    StatusRequest,
)

from zmqruntime.transport import coerce_transport_mode
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

logger = logging.getLogger(__name__)


class OpenHCSExecutionServer(ExecutionServer):
    """OpenHCS-specific execution server."""

    _server_type = "execution"

    def __init__(
        self,
        port: int | None = None,
        host: str = "*",
        log_file_path: str | None = None,
        transport_mode=None,
    ):
        super().__init__(
            port=port or OPENHCS_ZMQ_CONFIG.default_port,
            host=host,
            log_file_path=log_file_path,
            transport_mode=coerce_transport_mode(transport_mode),
            config=OPENHCS_ZMQ_CONFIG,
        )
        self._compile_status: str | None = None
        self._compile_message: str | None = None
        self._compile_status_expires_at: float | None = None

    def _set_compile_status(
        self, status: str, message: str | None = None, ttl_seconds: float = 4.0
    ) -> None:
        self._compile_status = status
        self._compile_message = message
        self._compile_status_expires_at = time.time() + ttl_seconds

    def _get_compile_status(self) -> tuple[str | None, str | None]:
        if self._compile_status_expires_at is None:
            return None, None
        if time.time() > self._compile_status_expires_at:
            self._compile_status = None
            self._compile_message = None
            self._compile_status_expires_at = None
            return None, None
        return self._compile_status, self._compile_message

    def _create_pong_response(self):
        response = super()._create_pong_response()
        compile_status, compile_message = self._get_compile_status()
        if compile_status is not None:
            response[MessageFields.COMPILE_STATUS] = compile_status
        if compile_message is not None:
            response[MessageFields.COMPILE_MESSAGE] = compile_message
        return response

    def _enqueue_progress(self, progress_update: dict) -> None:
        self.progress_queue.put(progress_update)

    def _forward_worker_progress(self, worker_queue) -> None:
        while True:
            progress_update = worker_queue.get()
            if progress_update is None:
                break
            self.progress_queue.put(progress_update)

    def _run_execution(self, execution_id, request, record):
        """Run an execution and enrich results_summary with output plate path.

        The base zmqruntime ExecutionServer only populates well_count/wells in
        results_summary. OpenHCS needs the final output plate root (computed by
        path planning during compilation) so the UI can optionally auto-add it
        as a new orchestrator in Plate Manager.
        """
        super()._run_execution(execution_id, request, record)

        try:
            if record.get(MessageFields.STATUS) != ExecutionStatus.COMPLETE.value:
                logger.info(
                    "[%s] Skipping results_summary attach (status=%s)",
                    execution_id,
                    record.get(MessageFields.STATUS),
                )
                return

            output_plate_root = record.get("output_plate_root")
            auto_add_output_plate = record.get("auto_add_output_plate")

            summary = record.get(MessageFields.RESULTS_SUMMARY)
            if not isinstance(summary, dict):
                summary = {}
                record[MessageFields.RESULTS_SUMMARY] = summary
            if output_plate_root:
                summary["output_plate_root"] = str(output_plate_root)
            if auto_add_output_plate is not None:
                summary["auto_add_output_plate_to_plate_manager"] = bool(
                    auto_add_output_plate
                )

            logger.info(
                "[%s] Attached results_summary extras: output_plate_root=%s auto_add=%s",
                execution_id,
                summary.get("output_plate_root"),
                summary.get("auto_add_output_plate_to_plate_manager"),
            )
        except Exception as e:
            logger.warning(
                "[%s] Failed to attach output_plate_root to results_summary: %s",
                execution_id,
                e,
            )

    def _handle_status(self, msg):
        execution_id = StatusRequest.from_dict(msg).execution_id
        if execution_id:
            if execution_id not in self.active_executions:
                return ExecuteResponse(
                    ResponseType.ERROR,
                    error=f"Execution {execution_id} not found",
                ).to_dict()
            record = self.active_executions[execution_id]
            if record.get(MessageFields.STATUS) == ExecutionStatus.COMPLETE.value:
                summary = record.get(MessageFields.RESULTS_SUMMARY)
                if not isinstance(summary, dict):
                    summary = {}
                    record[MessageFields.RESULTS_SUMMARY] = summary
                output_plate_root = record.get("output_plate_root")
                auto_add_output_plate = record.get("auto_add_output_plate")
                if output_plate_root:
                    summary["output_plate_root"] = str(output_plate_root)
                if auto_add_output_plate is not None:
                    summary["auto_add_output_plate_to_plate_manager"] = bool(
                        auto_add_output_plate
                    )

            return {
                MessageFields.STATUS: ResponseType.OK.value,
                "execution": {
                    k: record.get(k)
                    for k in [
                        MessageFields.EXECUTION_ID,
                        MessageFields.PLATE_ID,
                        MessageFields.STATUS,
                        MessageFields.START_TIME,
                        MessageFields.END_TIME,
                        MessageFields.ERROR,
                        MessageFields.RESULTS_SUMMARY,
                    ]
                },
            }
        return {
            MessageFields.STATUS: ResponseType.OK.value,
            MessageFields.ACTIVE_EXECUTIONS: len(self.active_executions),
            MessageFields.UPTIME: time.time() - self.start_time
            if self.start_time
            else 0,
            MessageFields.EXECUTIONS: list(self.active_executions.keys()),
        }

    def execute_task(self, execution_id: str, request: ExecuteRequest) -> Any:
        return self._execute_pipeline(
            execution_id,
            request.plate_id,
            request.pipeline_code,
            request.config_params,
            request.config_code,
            request.pipeline_config_code,
            request.client_address,
            request.compile_only,
        )

    def _execute_pipeline(
        self,
        execution_id,
        plate_id,
        pipeline_code,
        config_params,
        config_code,
        pipeline_config_code,
        client_address=None,
        compile_only: bool = False,
    ):
        from openhcs.constants import AllComponents, VariableComponents, GroupBy
        from openhcs.core.config import GlobalPipelineConfig, PipelineConfig

        logger.info("[%s] Starting plate %s", execution_id, plate_id)

        import openhcs.processing.func_registry as func_registry_module

        logger.info(
            "[%s] Registry initialized status BEFORE check: %s",
            execution_id,
            func_registry_module._registry_initialized,
        )
        with func_registry_module._registry_lock:
            if not func_registry_module._registry_initialized:
                logger.info("[%s] Initializing registry...", execution_id)
                func_registry_module._auto_initialize_registry()
                logger.info(
                    "[%s] Registry initialized status AFTER init: %s",
                    execution_id,
                    func_registry_module._registry_initialized,
                )
            else:
                logger.info("[%s] Registry already initialized, skipping", execution_id)

        namespace = {}
        exec(pipeline_code, namespace)
        if not (pipeline_steps := namespace.get("pipeline_steps")):
            raise ValueError("Code must define 'pipeline_steps'")

        if config_code:
            is_empty = (
                "GlobalPipelineConfig(\n\n)" in config_code
                or "GlobalPipelineConfig()" in config_code
            )
            global_config = (
                GlobalPipelineConfig()
                if is_empty
                else (exec(config_code, ns := {}) or ns.get("config"))
            )
            if not global_config:
                raise ValueError("config_code must define 'config'")
            pipeline_config = (
                exec(pipeline_config_code, ns := {}) or ns.get("config")
                if pipeline_config_code
                else PipelineConfig()
            )
            if pipeline_config_code and not pipeline_config:
                raise ValueError("pipeline_config_code must define 'config'")
        elif config_params:
            global_config, pipeline_config = self._build_config_from_params(
                config_params
            )
        else:
            raise ValueError("Either config_params or config_code required")

        try:
            return self._execute_with_orchestrator(
                execution_id,
                plate_id,
                pipeline_steps,
                global_config,
                pipeline_config,
                config_params,
                compile_only=compile_only,
            )
        except Exception as e:
            if compile_only:
                self._set_compile_status("compiled failed", str(e))
            raise

    def _build_config_from_params(self, p):
        from openhcs.core.config import (
            GlobalPipelineConfig,
            MaterializationBackend,
            PathPlanningConfig,
            StepWellFilterConfig,
            VFSConfig,
            PipelineConfig,
        )

        return (
            GlobalPipelineConfig(
                num_workers=p.get("num_workers", 4),
                path_planning_config=PathPlanningConfig(
                    output_dir_suffix=p.get("output_dir_suffix", "_output")
                ),
                vfs_config=VFSConfig(
                    materialization_backend=MaterializationBackend(
                        p.get("materialization_backend", "disk")
                    )
                ),
                step_well_filter_config=StepWellFilterConfig(
                    well_filter=p.get("well_filter")
                ),
                use_threading=p.get("use_threading", False),
            ),
            PipelineConfig(),
        )

    def _execute_with_orchestrator(
        self,
        execution_id,
        plate_id,
        pipeline_steps,
        global_config,
        pipeline_config,
        config_params,
        compile_only: bool = False,
    ):
        from pathlib import Path
        import multiprocessing
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        from openhcs.core.orchestrator.gpu_scheduler import setup_global_gpu_registry
        from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
        from openhcs.constants import (
            AllComponents,
            VariableComponents,
            GroupBy,
            MULTIPROCESSING_AXIS,
        )
        from polystore.base import reset_memory_backend, storage_registry

        try:
            if multiprocessing.get_start_method(allow_none=True) != "spawn":
                multiprocessing.set_start_method("spawn", force=True)
        except RuntimeError:
            pass

        reset_memory_backend()

        try:
            from openhcs.core.memory import cleanup_all_gpu_frameworks

            cleanup_all_gpu_frameworks()
        except Exception as cleanup_error:
            logger.warning(
                "[%s] Failed to trigger GPU cleanup: %s", execution_id, cleanup_error
            )

        setup_global_gpu_registry(global_config=global_config)
        ensure_global_config_context(type(global_config), global_config)

        plate_path_str = str(plate_id)
        is_omero_plate_id = False
        try:
            int(plate_path_str)
            is_omero_plate_id = True
        except ValueError:
            is_omero_plate_id = plate_path_str.startswith("/omero/")

        if is_omero_plate_id:
            # Lazy-load OMERO dependencies only when OMERO is actually used
            # Import OMERO parsers BEFORE creating backend to ensure registration
            # This is required because OMEROLocalBackend accesses FilenameParser.__registry__
            # which is a LazyDiscoveryDict that only populates when first accessed
            from openhcs.runtime.omero_instance_manager import OMEROInstanceManager
            from openhcs.microscopes import omero  # noqa: F401 - Import OMERO parsers to register them
            from polystore.omero_local import OMEROLocalBackend

            omero_manager = OMEROInstanceManager()
            if not omero_manager.connect(timeout=60):
                raise RuntimeError("OMERO server not available")
            storage_registry["omero_local"] = OMEROLocalBackend(
                omero_conn=omero_manager.conn,
                namespace_prefix="openhcs",
                lock_dir_name=".openhcs",
            )

            if not plate_path_str.startswith("/omero/"):
                plate_path_str = f"/omero/plate_{plate_path_str}"

        from openhcs.core.progress_reporter import (
            set_progress_emitter,
            clear_progress_emitter,
            emit_progress,
        )

        progress_context = {
            MessageFields.EXECUTION_ID: execution_id,
            MessageFields.PLATE_ID: plate_id,
        }
        worker_progress_queue = None
        progress_forwarder = None
        set_progress_emitter(self._enqueue_progress, progress_context)

        try:
            emit_progress(
                {
                    "axis_id": "",
                    "step_name": "pipeline",
                    "step_index": -1,
                    "total_steps": len(pipeline_steps),
                    "phase": "init",
                    "status": "started",
                    "completed": 0,
                    "total": 1,
                    "percent": 0.0,
                }
            )

            orchestrator = PipelineOrchestrator(
                plate_path=Path(plate_path_str),
                pipeline_config=pipeline_config,
                progress_callback=None,
            )
            orchestrator.initialize()
            self.active_executions[execution_id]["orchestrator"] = orchestrator

            emit_progress(
                {
                    "axis_id": "",
                    "step_name": "pipeline",
                    "step_index": -1,
                    "total_steps": len(pipeline_steps),
                    "phase": "init",
                    "status": "completed",
                    "completed": 1,
                    "total": 1,
                    "percent": 100.0,
                }
            )

            if (
                self.active_executions[execution_id][MessageFields.STATUS]
                == ExecutionStatus.CANCELLED.value
            ):
                logger.info(
                    "[%s] Execution cancelled after initialization, aborting",
                    execution_id,
                )
                raise RuntimeError("Execution cancelled by user")

            wells = (
                config_params.get("well_filter")
                if config_params
                else orchestrator.get_component_keys(MULTIPROCESSING_AXIS)
            )
            emit_progress(
                {
                    "axis_id": "",
                    "step_name": "pipeline",
                    "step_index": -1,
                    "total_steps": len(pipeline_steps),
                    "phase": "compile",
                    "status": "started",
                    "completed": 0,
                    "total": 1,
                    "percent": 0.0,
                }
            )

            compilation = orchestrator.compile_pipelines(
                pipeline_definition=pipeline_steps,
                well_filter=wells,
                is_zmq_execution=True,
            )

            emit_progress(
                {
                    "axis_id": "",
                    "step_name": "pipeline",
                    "step_index": -1,
                    "total_steps": len(pipeline_steps),
                    "phase": "compile",
                    "status": "completed",
                    "completed": 1,
                    "total": 1,
                    "percent": 100.0,
                }
            )

            # Persist the final output plate root computed by the path planner so the
            # client can retrieve it from status/results_summary on completion.
            try:
                compiled_contexts = (
                    compilation.get("compiled_contexts")
                    if isinstance(compilation, dict)
                    else None
                )
                if compiled_contexts:
                    first_context = next(iter(compiled_contexts.values()))
                    output_plate_root = getattr(
                        first_context, "output_plate_root", None
                    )
                    if output_plate_root:
                        self.active_executions[execution_id]["output_plate_root"] = str(
                            output_plate_root
                        )
                    auto_add_output_plate = (
                        first_context.auto_add_output_plate_to_plate_manager
                    )
                    self.active_executions[execution_id]["auto_add_output_plate"] = (
                        bool(auto_add_output_plate)
                    )
                    logger.info(
                        "[%s] Captured auto_add_output_plate=%s output_plate_root=%s",
                        execution_id,
                        bool(auto_add_output_plate),
                        output_plate_root,
                    )
                else:
                    logger.warning(
                        "[%s] No compiled_contexts; cannot capture auto_add_output_plate",
                        execution_id,
                    )
            except Exception as e:
                logger.warning(
                    "[%s] Failed to capture output_plate_root during compilation: %s",
                    execution_id,
                    e,
                )

            if (
                self.active_executions[execution_id][MessageFields.STATUS]
                == ExecutionStatus.CANCELLED.value
            ):
                logger.info(
                    "[%s] Execution cancelled after compilation, aborting",
                    execution_id,
                )
                raise RuntimeError("Execution cancelled by user")

            if compile_only:
                logger.info("[%s] Compilation-only request completed", execution_id)
                self._set_compile_status("compiled success")
                return compilation["compiled_contexts"]

            log_dir = Path.home() / ".local" / "share" / "openhcs" / "logs"
            log_dir.mkdir(parents=True, exist_ok=True)

            worker_progress_queue = multiprocessing.Queue()
            progress_forwarder = threading.Thread(
                target=self._forward_worker_progress,
                args=(worker_progress_queue,),
                daemon=True,
            )
            progress_forwarder.start()

            if (
                self.active_executions[execution_id][MessageFields.STATUS]
                == ExecutionStatus.CANCELLED.value
            ):
                logger.info(
                    "[%s] Execution cancelled before starting workers, aborting",
                    execution_id,
                )
                raise RuntimeError("Execution cancelled by user")

            return orchestrator.execute_compiled_plate(
                pipeline_definition=pipeline_steps,
                compiled_contexts=compilation["compiled_contexts"],
                log_file_base=str(log_dir / f"zmq_worker_exec_{execution_id}"),
                progress_queue=worker_progress_queue,
                progress_context=progress_context,
            )
        finally:
            if worker_progress_queue is not None:
                worker_progress_queue.put(None)
            if progress_forwarder is not None:
                progress_forwarder.join()
            clear_progress_emitter()

    def _kill_worker_processes(self) -> int:
        """OpenHCS-specific worker cleanup (graceful cancellation + kill)."""
        for eid, r in self.active_executions.items():
            if "orchestrator" in r:
                try:
                    logger.info("[%s] Requesting graceful cancellation...", eid)
                    r["orchestrator"].cancel_execution()
                except Exception as e:
                    logger.warning("[%s] Graceful cancellation failed: %s", eid, e)
        return super()._kill_worker_processes()


# Backwards-compatible alias
ZMQExecutionServer = OpenHCSExecutionServer
