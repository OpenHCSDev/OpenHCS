"""Unified batch workflow service for compile + execute flows."""

from __future__ import annotations

import asyncio
import logging
import os
import threading
import time
from dataclasses import dataclass
from typing import Any, Dict, List, Callable, Optional, TypeVar

from openhcs.core.orchestrator.orchestrator import OrchestratorState
from openhcs.core.progress import ProgressEvent, ProgressPhase, ProgressStatus
from openhcs.core.progress.projection import (
    ExecutionRuntimeProjection,
    build_execution_runtime_projection_from_registry,
)
from openhcs.pyqt_gui.widgets.shared.services.plate_config_resolver import (
    resolve_pipeline_config_for_plate,
)
from openhcs.pyqt_gui.widgets.shared.services.progress_batch_reset import (
    reset_progress_views_for_new_batch,
)
from openhcs.pyqt_gui.widgets.shared.services.execution_server_status_presenter import (
    ExecutionServerStatusPresenter,
)
from openhcs.pyqt_gui.widgets.shared.server_browser import (
    ServerKillPlan,
    ServerKillService,
)
from openhcs.pyqt_gui.widgets.shared.services.zmq_client_service import ZMQClientService
from pyqt_reactive.services import (
    CallbackIntervalSnapshotPollerPolicy,
    DefaultServerInfoParser,
    ExecutionServerInfo,
    IntervalSnapshotPoller,
    ServerInfoParserABC,
)
from zmqruntime.execution import (
    BatchSubmitWaitEngine,
    CallbackBatchSubmitWaitPolicy,
    ExecutionStatusPoller,
    CallbackExecutionStatusPollPolicy,
)

logger = logging.getLogger(__name__)
T = TypeVar("T")


@dataclass(frozen=True)
class CompileJob:
    """Single compile unit for a plate."""

    plate_path: str
    plate_name: str
    definition_pipeline: List
    pipeline_config: Any


class BatchWorkflowService:
    """Single owner of batch compilation and execution workflow."""

    def __init__(
        self,
        host,
        port: int = 7777,
        client_service: ZMQClientService | None = None,
        server_info_parser: ServerInfoParserABC | None = None,
    ) -> None:
        self.host = host
        self.port = port
        self.client_service = client_service or ZMQClientService(port=port)
        server_info_parser_impl = (
            server_info_parser
            if server_info_parser is not None
            else DefaultServerInfoParser()
        )

        self._progress_dirty = False
        from PyQt6.QtCore import QTimer
        from openhcs.pyqt_gui.config import ProgressUIConfig

        self._progress_coalesce_timer = QTimer()
        self._progress_coalesce_timer.timeout.connect(self._coalesced_progress_update)
        self._progress_coalesce_timer.start(ProgressUIConfig().update_interval_ms)
        self._runtime_projection = ExecutionRuntimeProjection()
        self._server_info_parser = server_info_parser_impl
        self._server_info_poller = IntervalSnapshotPoller[ExecutionServerInfo](
            CallbackIntervalSnapshotPollerPolicy(
                fetch_snapshot_fn=self._fetch_server_info_snapshot,
                clone_snapshot_fn=lambda snapshot: snapshot,
                poll_interval_seconds_value=1.0,
                on_snapshot_changed_fn=lambda _snapshot: self._mark_progress_dirty(),
                on_poll_error_fn=lambda error: logger.debug(
                    "Server info poll failed: %s", error
                ),
            )
        )
        self._compile_batch_engine = BatchSubmitWaitEngine[CompileJob]()
        self._execution_status_poller = ExecutionStatusPoller()
        self._server_kill_service = ServerKillService()
        self._server_status_presenter = ExecutionServerStatusPresenter()
        self._registry_listener = self._on_registry_event
        self.host._progress_tracker.add_listener(self._registry_listener)
        self._registry_listener_registered = True
        self._cleaned_up = False

    def cleanup(self) -> None:
        """Release timers/listeners owned by this service."""
        if self._cleaned_up:
            return
        self._cleaned_up = True

        if self._registry_listener_registered:
            removed = self.host._progress_tracker.remove_listener(self._registry_listener)
            if not removed:
                raise RuntimeError(
                    "BatchWorkflowService listener removal failed: listener not registered"
                )
            self._registry_listener_registered = False

        if self._progress_coalesce_timer is not None:
            self._progress_coalesce_timer.stop()
            self._progress_coalesce_timer.deleteLater()
            self._progress_coalesce_timer = None

    async def compile_plates(self, selected_items: List[Dict]) -> None:
        """Compile pipelines for selected plates."""
        reset_progress_views_for_new_batch(self.host)
        self.host.emit_progress_started(len(selected_items))
        loop = asyncio.get_event_loop()

        try:
            zmq_client = await self.client_service.connect(persistent=True, timeout=15)
            plate_paths = [str(item["path"]) for item in selected_items]
            self.host.plate_compile_pending.update(plate_paths)
            self.host.update_item_list()
            self.host.emit_status(
                f"Queueing compilation for {len(selected_items)} plate(s)..."
            )

            completed_count = 0
            compile_jobs: List[CompileJob] = []
            for plate_data in selected_items:
                plate_path = str(plate_data["path"])
                try:
                    compile_jobs.append(
                        self._build_compile_job_from_plate_data(plate_data)
                    )
                except Exception as error:
                    self._handle_compile_failure(plate_data, plate_path, error)
                    completed_count += 1
                    self.host.emit_progress_updated(completed_count)

            waiting_announced = False

            def _on_wait_success(
                job: CompileJob, _execution_id: str, _idx: int, _total: int
            ) -> None:
                self.host.plate_compiled_data[job.plate_path] = {
                    "definition_pipeline": job.definition_pipeline,
                }
                self._set_orchestrator_state(job.plate_path, OrchestratorState.COMPILED)
                self.host.emit_orchestrator_state(job.plate_path, "COMPILED")
                logger.info("Successfully compiled %s", job.plate_path)

            def _on_wait_error(
                job: CompileJob, error: Exception, _idx: int, _total: int
            ) -> None:
                self._handle_compile_failure(
                    {"name": job.plate_name}, job.plate_path, error
                )

            def _on_wait_start(
                _job: CompileJob, _idx: int, total: int
            ) -> None:
                nonlocal waiting_announced
                if waiting_announced:
                    return
                waiting_announced = True
                self.host.emit_status(
                    f"Queued {total} compilation job(s). Waiting for completion..."
                )

            def _on_wait_finally(
                job: CompileJob, _idx: int, _total: int
            ) -> None:
                nonlocal completed_count
                self.host.plate_compile_pending.discard(job.plate_path)
                self.host.update_item_list()
                completed_count += 1
                self.host.emit_progress_updated(completed_count)

            compile_policy = self._make_compile_policy(
                zmq_client=zmq_client,
                loop=loop,
                fail_fast_submit=False,
                fail_fast_wait=False,
                on_submit_error=lambda job, error, _idx, _total: self._handle_compile_failure(
                    {"name": job.plate_name}, job.plate_path, error
                ),
                on_wait_start=_on_wait_start,
                on_wait_success=_on_wait_success,
                on_wait_error=_on_wait_error,
                on_wait_finally=_on_wait_finally,
            )
            await self._compile_batch_engine.run(compile_jobs, compile_policy)
        finally:
            if self.host.execution_state != "running":
                await self.client_service.disconnect()

        self.host.emit_progress_finished()
        self.host.emit_status(
            f"Compilation completed for {len(selected_items)} plate(s)"
        )
        self.host.update_button_states()

    async def run_plates(self, ready_items: List[Dict]) -> None:
        """Run selected plates using compile-all then execute-all workflow."""
        loop = asyncio.get_event_loop()
        try:
            plate_paths = [str(item["path"]) for item in ready_items]
            logger.info("Starting ZMQ execution for %d plates", len(plate_paths))

            self._reset_progress_for_new_batch()
            self.host.emit_clear_logs()

            await self.client_service.disconnect()
            await self.client_service.connect(
                progress_callback=self._on_progress, persistent=True, timeout=15
            )

            self.host.plate_execution_ids.clear()
            self.host.plate_execution_states.clear()
            self.host.plate_progress.clear()

            from objectstate import ObjectStateRegistry

            for item in ready_items:
                plate_path = str(item["path"])
                self.host.plate_execution_states[plate_path] = "queued"
                orchestrator = ObjectStateRegistry.get_object(plate_path)
                if orchestrator is not None:
                    orchestrator._state = OrchestratorState.EXECUTING
                    self.host.emit_orchestrator_state(
                        plate_path, OrchestratorState.EXECUTING.value
                    )

            self.host.execution_state = "running"
            self.host.emit_status(
                f"Compiling {len(ready_items)} plate(s) before execution..."
            )
            self.host.update_button_states()
            self.host.update_item_list()

            run_specs = [self._build_run_spec(plate_path) for plate_path in plate_paths]
            compile_artifacts = await self._compile_plates_before_execution(
                run_specs=run_specs,
                loop=loop,
            )

            self.host.emit_status(
                f"Compilation complete. Submitting {len(run_specs)} plate(s) for execution..."
            )
            for run_spec in run_specs:
                plate_path = run_spec["plate_path"]
                await self._submit_plate(
                    run_spec=run_spec,
                    compile_artifact_id=compile_artifacts[plate_path],
                    loop=loop,
                )
        except Exception as error:
            logger.error("Failed to execute plates via ZMQ: %s", error, exc_info=True)
            self.host.emit_error(f"Failed to execute: {error}")
            await self._handle_execution_failure(loop)

    async def _compile_plates_before_execution(
        self, run_specs: List[Dict[str, Any]], loop
    ) -> Dict[str, str]:
        """Compile all selected plates before submitting execution jobs."""
        if self.client_service.zmq_client is None:
            raise RuntimeError("ZMQ client is not connected")

        zmq_client = self.client_service.zmq_client
        compile_jobs = [
            self._build_compile_job_from_run_spec(run_spec) for run_spec in run_specs
        ]
        waiting_announced = False

        def _on_wait_start(job: CompileJob, _idx: int, _total: int) -> None:
            nonlocal waiting_announced
            if not waiting_announced:
                waiting_announced = True
                self.host.emit_status(
                    f"Queued {len(compile_jobs)} compile job(s) before execution. Waiting for completion..."
                )
            self.host.plate_execution_states[job.plate_path] = "compiling"
            self.host.update_item_list()

        def _on_wait_success(
            job: CompileJob, _execution_id: str, index: int, total: int
        ) -> None:
            self.host.plate_execution_states[job.plate_path] = "queued"
            self.host.emit_status(f"Compiled {index}/{total}: {job.plate_path}")
            self.host.update_item_list()

        def _on_wait_error(
            job: CompileJob, error: Exception, _idx: int, _total: int
        ) -> None:
            self._mark_execution_compile_failed(job.plate_path, error)

        compile_policy = self._make_compile_policy(
            zmq_client=zmq_client,
            loop=loop,
            fail_fast_submit=True,
            fail_fast_wait=True,
            on_submit_error=lambda job, error, _idx, _total: self._mark_execution_compile_failed(
                job.plate_path, error
            ),
            on_wait_start=_on_wait_start,
            on_wait_success=_on_wait_success,
            on_wait_error=_on_wait_error,
        )
        compile_artifacts = await self._compile_batch_engine.run(
            compile_jobs, compile_policy
        )
        return compile_artifacts

    def _build_compile_job_from_plate_data(self, plate_data: Dict[str, Any]) -> CompileJob:
        plate_path = str(plate_data["path"])
        definition_pipeline = self.host.get_pipeline_definition(plate_path)
        if not definition_pipeline:
            logger.warning(
                "No pipeline defined for %s, using empty pipeline",
                plate_data["name"],
            )
            definition_pipeline = []

        self._validate_pipeline_steps(definition_pipeline)
        pipeline_config = resolve_pipeline_config_for_plate(self.host, plate_path)
        return CompileJob(
            plate_path=plate_path,
            plate_name=str(plate_data["name"]),
            definition_pipeline=definition_pipeline,
            pipeline_config=pipeline_config,
        )

    @staticmethod
    def _build_compile_job_from_run_spec(run_spec: Dict[str, Any]) -> CompileJob:
        plate_path = str(run_spec["plate_path"])
        return CompileJob(
            plate_path=plate_path,
            plate_name=plate_path,
            definition_pipeline=run_spec["definition_pipeline"],
            pipeline_config=run_spec["pipeline_config"],
        )

    def _make_compile_policy(
        self,
        *,
        zmq_client,
        loop,
        fail_fast_submit: bool,
        fail_fast_wait: bool,
        on_submit_error: Callable[[CompileJob, Exception, int, int], None] | None = None,
        on_wait_start: Callable[[CompileJob, int, int], None] | None = None,
        on_wait_success: Callable[[CompileJob, str, int, int], None] | None = None,
        on_wait_error: Callable[[CompileJob, Exception, int, int], None] | None = None,
        on_wait_finally: Callable[[CompileJob, int, int], None] | None = None,
    ) -> CallbackBatchSubmitWaitPolicy[CompileJob]:
        return CallbackBatchSubmitWaitPolicy(
            submit_fn=lambda job: self._submit_compile_job(
                job=job,
                zmq_client=zmq_client,
                loop=loop,
            ),
            wait_fn=lambda submission_id, job: self._wait_compile_job(
                submission_id=submission_id,
                job=job,
                zmq_client=zmq_client,
                loop=loop,
            ),
            job_key_fn=lambda job: job.plate_path,
            fail_fast_submit_value=fail_fast_submit,
            fail_fast_wait_value=fail_fast_wait,
            on_submit_error_fn=on_submit_error,
            on_wait_start_fn=on_wait_start,
            on_wait_success_fn=on_wait_success,
            on_wait_error_fn=on_wait_error,
            on_wait_finally_fn=on_wait_finally,
        )

    async def _submit_compile_job(self, *, job: CompileJob, zmq_client, loop) -> str:
        response = await self._submit_compile_request(
            zmq_client=zmq_client,
            loop=loop,
            plate_path=job.plate_path,
            definition_pipeline=job.definition_pipeline,
            pipeline_config=job.pipeline_config,
        )
        execution_id = response["execution_id"]
        self._register_compile_submission_placeholder(
            execution_id=execution_id,
            plate_id=job.plate_path,
        )
        return execution_id

    async def _wait_compile_job(
        self, *, submission_id: str, job: CompileJob, zmq_client, loop
    ) -> None:
        await self._wait_for_compile_completion(
            zmq_client=zmq_client,
            loop=loop,
            execution_id=submission_id,
            plate_path=job.plate_path,
        )

    def _mark_execution_compile_failed(self, plate_path: str, error: Exception) -> None:
        logger.error(
            "Compile-before-execution failed for %s: %s", plate_path, error, exc_info=True
        )
        self.host.plate_execution_states[plate_path] = "failed"
        self.host.emit_error(f"Compile failed for {plate_path}: {error}")
        self.host.update_item_list()

    def _register_compile_submission_placeholder(
        self, *, execution_id: str, plate_id: str
    ) -> None:
        event = ProgressEvent(
            execution_id=execution_id,
            plate_id=plate_id,
            axis_id="",
            step_name="compilation",
            phase=ProgressPhase.COMPILE,
            status=ProgressStatus.RUNNING,
            percent=0.0,
            completed=0,
            total=1,
            timestamp=time.time(),
            pid=os.getpid(),
        )
        self.host._progress_tracker.register_event(execution_id, event)

    async def _submit_compile_request(
        self,
        *,
        zmq_client,
        loop,
        plate_path: str,
        definition_pipeline: List,
        pipeline_config,
    ) -> Dict[str, Any]:
        def _submit_compile() -> Dict[str, Any]:
            return zmq_client.submit_compile(
                plate_id=plate_path,
                pipeline_steps=definition_pipeline,
                global_config=self.host.global_config,
                pipeline_config=pipeline_config,
            )

        response = await self._run_blocking(loop, _submit_compile)
        if response.get("status") != "accepted":
            raise RuntimeError(
                f"Compile submission failed for {plate_path}: "
                f"{response.get('message', 'Unknown error')}"
            )
        execution_id = response.get("execution_id")
        if not execution_id:
            raise RuntimeError(f"Compile submission missing execution_id for {plate_path}")
        return {"execution_id": execution_id, "response": response}

    async def _wait_for_compile_completion(
        self,
        *,
        zmq_client,
        loop,
        execution_id: str,
        plate_path: str,
    ) -> None:
        wait_result = await self._run_blocking(
            loop,
            lambda: zmq_client.wait_for_completion(execution_id),
        )
        if wait_result.get("status") != "complete":
            raise RuntimeError(
                f"Compilation failed for {plate_path}: "
                f"{wait_result.get('message', 'Unknown error')}"
            )

    def _build_run_spec(self, plate_path: str) -> Dict[str, Any]:
        plate_path = str(plate_path)
        compiled_data = self.host.plate_compiled_data[plate_path]
        definition_pipeline = compiled_data["definition_pipeline"]
        pipeline_config = resolve_pipeline_config_for_plate(self.host, plate_path)
        return {
            "plate_path": plate_path,
            "definition_pipeline": definition_pipeline,
            "global_config": self.host.global_config,
            "pipeline_config": pipeline_config,
        }

    async def _submit_plate(
        self, run_spec: Dict[str, Any], compile_artifact_id: str, loop
    ) -> None:
        if self.client_service.zmq_client is None:
            raise RuntimeError("ZMQ client is not connected")
        plate_path = run_spec["plate_path"]
        logger.info("Executing plate: %s", plate_path)

        def _submit() -> Dict[str, Any]:
            return self.client_service.zmq_client.submit_pipeline(
                plate_id=plate_path,
                pipeline_steps=run_spec["definition_pipeline"],
                global_config=run_spec["global_config"],
                pipeline_config=run_spec["pipeline_config"],
                compile_artifact_id=compile_artifact_id,
            )

        response = await self._run_blocking(loop, _submit)

        execution_id = response.get("execution_id")
        if execution_id:
            self.host.plate_execution_ids[plate_path] = execution_id
            self.host.current_execution_id = execution_id

        status = response.get("status")
        if status == "accepted":
            self.host.emit_status(f"Submitted {plate_path} (queued on server)")
            if execution_id:
                self._start_completion_poller(execution_id, plate_path)
            return

        error_msg = response.get("message", "Unknown error")
        logger.error("Plate %s submission failed: %s", plate_path, error_msg)
        self.host.emit_error(f"Submission failed for {plate_path}: {error_msg}")
        self.host.plate_execution_states[plate_path] = "failed"
        from objectstate import ObjectStateRegistry

        orchestrator = ObjectStateRegistry.get_object(plate_path)
        if orchestrator is not None:
            orchestrator._state = OrchestratorState.EXEC_FAILED
            self.host.emit_orchestrator_state(
                plate_path, OrchestratorState.EXEC_FAILED.value
            )

    async def _handle_execution_failure(self, loop) -> None:
        from objectstate import ObjectStateRegistry

        for plate_path in self.host.plate_execution_states.keys():
            self.host.plate_execution_states[plate_path] = "failed"
            orchestrator = ObjectStateRegistry.get_object(plate_path)
            if orchestrator is not None:
                orchestrator._state = OrchestratorState.EXEC_FAILED
                self.host.emit_orchestrator_state(
                    plate_path, OrchestratorState.EXEC_FAILED.value
                )

        self.host.execution_state = "idle"
        await self._disconnect_client(loop)
        self.host.current_execution_id = None
        self.host.update_button_states()

    async def _disconnect_client(self, loop) -> None:
        if self.client_service.zmq_client is None:
            return
        try:
            await self.client_service.disconnect()
        except Exception as error:
            logger.warning("Error disconnecting old client: %s", error)

    @staticmethod
    async def _run_blocking(loop, func: Callable[[], T]) -> T:
        return await loop.run_in_executor(None, func)

    def _start_completion_poller(self, execution_id: str, plate_path: str) -> None:
        class _ClientDisconnected(RuntimeError):
            pass

        def _poll_status(polled_execution_id: str) -> Dict[str, Any]:
            if self.client_service.zmq_client is None:
                raise _ClientDisconnected("ZMQ client disconnected")
            return self.client_service.zmq_client.get_status(polled_execution_id)

        def _on_running(_execution_id: str, _execution_payload: Dict[str, Any]) -> None:
            self.host.plate_execution_states[plate_path] = "running"
            self.host.update_item_list()
            self.host.emit_status(f"▶️ Running {plate_path}")

        def _on_terminal(
            _execution_id: str, terminal_status: str, execution_payload: Dict[str, Any]
        ) -> None:
            result = self._build_terminal_result(
                terminal_status=terminal_status,
                execution_id=execution_id,
                execution_payload=execution_payload,
            )
            self.host.on_plate_completed(plate_path, terminal_status, result)
            self._check_all_completed()

        def _on_status_error(_execution_id: str, message: str) -> None:
            self.host.on_plate_completed(
                plate_path,
                "failed",
                {
                    "status": "failed",
                    "execution_id": execution_id,
                    "message": message,
                },
            )
            self._check_all_completed()

        def _on_poll_exception(_execution_id: str, error: Exception) -> bool:
            if isinstance(error, _ClientDisconnected):
                return False
            logger.warning("Error polling status for %s: %s", plate_path, error)
            return True

        policy = CallbackExecutionStatusPollPolicy(
            poll_status_fn=_poll_status,
            poll_interval_seconds_value=0.5,
            on_running_fn=_on_running,
            on_terminal_fn=_on_terminal,
            on_status_error_fn=_on_status_error,
            on_poll_exception_fn=_on_poll_exception,
        )

        def poll_completion() -> None:
            try:
                self._execution_status_poller.run(execution_id, policy)
            except Exception as error:
                logger.error(
                    "Error in completion poller for %s: %s", plate_path, error, exc_info=True
                )
                self.host.emit_error(f"{plate_path}: {error}")

        threading.Thread(target=poll_completion, daemon=True).start()

    @staticmethod
    def _build_terminal_result(
        *,
        terminal_status: str,
        execution_id: str,
        execution_payload: Dict[str, Any],
    ) -> Dict[str, Any]:
        if terminal_status == "complete":
            results_summary = execution_payload.get("results_summary", {}) or {}
            output_plate_root = None
            auto_add_output_plate = None
            if isinstance(results_summary, dict):
                output_plate_root = results_summary.get("output_plate_root")
                auto_add_output_plate = results_summary.get(
                    "auto_add_output_plate_to_plate_manager"
                )
            return {
                "status": "complete",
                "execution_id": execution_id,
                "results": results_summary,
                "output_plate_root": output_plate_root,
                "auto_add_output_plate_to_plate_manager": auto_add_output_plate,
            }
        if terminal_status == "failed":
            return {
                "status": "error",
                "execution_id": execution_id,
                "message": execution_payload.get("error", "Unknown error"),
                "traceback": execution_payload.get("traceback", ""),
            }
        if terminal_status == "cancelled":
            return {
                "status": "cancelled",
                "execution_id": execution_id,
                "message": "Execution was cancelled",
            }
        raise ValueError(f"Unknown terminal status '{terminal_status}'")

    def _coalesced_progress_update(self) -> None:
        if self.client_service.zmq_client is not None:
            self._server_info_poller.tick()
        if not self._progress_dirty:
            return
        self._progress_dirty = False
        self._runtime_projection = build_execution_runtime_projection_from_registry(
            self.host._progress_tracker
        )
        self.host.set_runtime_progress_projection(self._runtime_projection)
        self.host.set_execution_server_info(self._get_server_info_snapshot())
        self._emit_execution_server_status()
        self.host.update_item_list()

    def _on_progress(self, message: dict) -> None:
        try:
            event = ProgressEvent.from_dict(message)
            self.host._progress_tracker.register_event(event.execution_id, event)
        except Exception as error:
            logger.warning("Failed to parse/register progress event: %s", error)
        finally:
            self._mark_progress_dirty()

    def _on_registry_event(self, _execution_id: str, _event: ProgressEvent) -> None:
        """Mark projection dirty when shared registry changes from any producer."""
        self._mark_progress_dirty()

    def _emit_execution_server_status(self) -> None:
        status_view = self._server_status_presenter.build_status_text(
            projection=self._runtime_projection,
            server_info=self._get_server_info_snapshot(),
        )
        self.host.emit_status(status_view.text)

    def _get_server_info_snapshot(self) -> ExecutionServerInfo | None:
        return self._server_info_poller.get_snapshot_copy()

    def _fetch_server_info_snapshot(self) -> ExecutionServerInfo:
        if self.client_service.zmq_client is None:
            raise RuntimeError("ZMQ client is not connected")
        pong = self.client_service.zmq_client.get_server_info_snapshot()
        parsed = self._server_info_parser.parse(pong.to_dict())
        if not isinstance(parsed, ExecutionServerInfo):
            raise ValueError(
                f"Expected ExecutionServerInfo, got {type(parsed).__name__}"
            )
        return parsed

    def _mark_progress_dirty(self) -> None:
        self._progress_dirty = True

    def _check_all_completed(self) -> None:
        all_done = all(
            state in ("completed", "failed")
            for state in self.host.plate_execution_states.values()
        )
        if not all_done:
            return
        completed = sum(
            1 for state in self.host.plate_execution_states.values() if state == "completed"
        )
        failed = sum(
            1 for state in self.host.plate_execution_states.values() if state == "failed"
        )
        self.host.on_all_plates_completed(completed, failed)

    def stop_execution(self, force: bool = False) -> None:
        port = self.port

        def kill_server() -> None:
            try:
                plan = ServerKillPlan(
                    graceful=not force,
                    strict_failures=True,
                    emit_signal_on_failure=False,
                    success_message=f"Stopped execution server on port {port}",
                )
                success, message = self._server_kill_service.kill_ports(
                    ports=[port],
                    plan=plan,
                    on_server_killed=lambda _port: self._emit_cancelled_for_all_plates(),
                    log_info=logger.info,
                    log_warning=logger.warning,
                    log_error=logger.error,
                )
                if not success:
                    self.host.emit_error(message)
                    return
            except Exception as error:
                logger.error("Error stopping server: %s", error)
                self.host.emit_error(f"Error stopping execution: {error}")

        threading.Thread(target=kill_server, daemon=True).start()

    def _emit_cancelled_for_all_plates(self) -> None:
        for plate_path in list(self.host.plate_execution_states.keys()):
            self.host.emit_execution_complete({"status": "cancelled"}, plate_path)

    def disconnect(self) -> None:
        if self.client_service.zmq_client is None:
            return
        try:
            self.client_service.disconnect_sync()
        except Exception as error:
            logger.warning("Error disconnecting ZMQ client: %s", error)

    def _validate_pipeline_steps(self, pipeline: List) -> None:
        for step in pipeline:
            if step.func is None:
                raise AttributeError(
                    f"Step '{step.name}' has func=None. "
                    "This usually means the pipeline was loaded from a compiled state."
                )

    @staticmethod
    def _set_orchestrator_state(plate_path: str, state: OrchestratorState) -> None:
        from objectstate import ObjectStateRegistry

        orchestrator = ObjectStateRegistry.get_object(plate_path)
        if orchestrator is not None:
            orchestrator._state = state

    def _handle_compile_failure(
        self, plate_data: Dict[str, Any], plate_path: str, error: Exception
    ) -> None:
        logger.error("COMPILATION ERROR: %s: %s", plate_path, error, exc_info=True)
        plate_data["error"] = str(error)
        self._set_orchestrator_state(plate_path, OrchestratorState.COMPILE_FAILED)
        self.host.plate_compile_pending.discard(plate_path)
        self.host.update_item_list()
        self.host.emit_orchestrator_state(plate_path, "COMPILE_FAILED")
        self.host.emit_compilation_error(plate_data["name"], str(error))

    def _reset_progress_for_new_batch(self) -> None:
        self._runtime_projection = reset_progress_views_for_new_batch(
            self.host,
            projection=ExecutionRuntimeProjection(),
        )
        self._server_info_poller.reset()
        self._mark_progress_dirty()
