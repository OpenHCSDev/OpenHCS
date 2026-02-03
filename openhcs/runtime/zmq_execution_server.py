"""OpenHCS execution server built on zmqruntime ExecutionServer."""

from __future__ import annotations

import logging
import os
import time
from typing import Any

from zmqruntime.execution import ExecutionServer
from zmqruntime.messages import ExecuteRequest, ExecutionStatus, MessageFields

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
        # Mark this process as the ZMQ execution server.
        # Compiler uses this to decide whether to unregister compiler-created ObjectStates
        # at the end of resolution (free RAM in server; keep in UI/editor).
        os.environ.setdefault("OPENHCS_ZMQ_EXECUTION_SERVER", "1")
        super().__init__(
            port=port or OPENHCS_ZMQ_CONFIG.default_port,
            host=host,
            log_file_path=log_file_path,
            transport_mode=coerce_transport_mode(transport_mode),
            config=OPENHCS_ZMQ_CONFIG,
        )

    def execute_task(self, execution_id: str, request: ExecuteRequest) -> Any:
        return self._execute_pipeline(
            execution_id,
            request.plate_id,
            request.pipeline_code,
            request.config_params,
            request.config_code,
            request.pipeline_config_code,
            request.client_address,
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

        return self._execute_with_orchestrator(
            execution_id,
            plate_id,
            pipeline_steps,
            global_config,
            pipeline_config,
            config_params,
        )

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

        orchestrator = PipelineOrchestrator(
            plate_path=Path(plate_path_str),
            pipeline_config=pipeline_config,
            progress_callback=None,
        )
        orchestrator.initialize()
        self.active_executions[execution_id]["orchestrator"] = orchestrator

        if (
            self.active_executions[execution_id][MessageFields.STATUS]
            == ExecutionStatus.CANCELLED.value
        ):
            logger.info(
                "[%s] Execution cancelled after initialization, aborting", execution_id
            )
            raise RuntimeError("Execution cancelled by user")

        wells = (
            config_params.get("well_filter")
            if config_params
            else orchestrator.get_component_keys(MULTIPROCESSING_AXIS)
        )
        compilation = orchestrator.compile_pipelines(
            pipeline_definition=pipeline_steps, well_filter=wells
        )

        if (
            self.active_executions[execution_id][MessageFields.STATUS]
            == ExecutionStatus.CANCELLED.value
        ):
            logger.info(
                "[%s] Execution cancelled after compilation, aborting", execution_id
            )
            raise RuntimeError("Execution cancelled by user")

        log_dir = Path.home() / ".local" / "share" / "openhcs" / "logs"
        log_dir.mkdir(parents=True, exist_ok=True)

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
        )

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
