"""
ZMQ Execution Service - Manages ZMQ client lifecycle and plate execution.

Extracted from PlateManagerWidget to reduce widget complexity.
The service handles:
- ZMQ client connection/disconnection
- Pipeline submission to ZMQ server
- Execution polling and status tracking
- Graceful/force shutdown
"""

import logging
import threading
import asyncio
from typing import Dict, Optional, Callable, Any, List

from openhcs.core.orchestrator.orchestrator import OrchestratorState
from openhcs.pyqt_gui.widgets.shared.services.zmq_client_service import (
    ZMQClientService,
)

logger = logging.getLogger(__name__)


class ZMQExecutionService:
    """
    Service for managing ZMQ execution of pipelines.

    Handles client lifecycle, submission, polling, and shutdown.
    Delegates UI updates back to host widget via signals.
    """

    def __init__(
        self,
        host,
        port: int = 7777,
        client_service: ZMQClientService | None = None,
    ):
        self.host = host
        self.port = port
        self.client_service = client_service or ZMQClientService(port=port)

    async def run_plates(self, ready_items: List[Dict]) -> None:
        """Run plates using ZMQ execution client."""
        loop = asyncio.get_event_loop()
        try:
            plate_paths = [str(item["path"]) for item in ready_items]
            logger.info(f"Starting ZMQ execution for {len(plate_paths)} plates")

            self.host.emit_clear_logs()

            # Cleanup old client and connect
            await self.client_service.disconnect()
            logger.info("🔌 Creating new ZMQ client")
            await self.client_service.connect(
                progress_callback=self._on_progress, persistent=True, timeout=15
            )

            # Initialize execution tracking
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
                f"Submitting {len(ready_items)} plate(s) to ZMQ server..."
            )
            self.host.update_button_states()

            # Submit each plate
            for plate_path in plate_paths:
                await self._submit_plate(plate_path, loop)

        except Exception as e:
            logger.error(f"Failed to execute plates via ZMQ: {e}", exc_info=True)
            self.host.emit_error(f"Failed to execute: {e}")
            await self._handle_execution_failure(loop)

    async def _disconnect_client(self, loop) -> None:
        """Disconnect existing ZMQ client if any."""
        if self.client_service.zmq_client is not None:
            logger.info("🧹 Disconnecting previous ZMQ client")
            try:
                await self.client_service.disconnect()
            except Exception as e:
                logger.warning(f"Error disconnecting old client: {e}")

    async def _submit_plate(self, plate_path: str, loop) -> None:
        """Submit a single plate for execution."""
        plate_path = str(plate_path)
        compiled_data = self.host.plate_compiled_data[plate_path]
        definition_pipeline = compiled_data["definition_pipeline"]

        # Get config
        # IMPORTANT: read the per-plate PipelineConfig from ObjectState (saved+resolved)
        # rather than from the live orchestrator instance. The orchestrator uses
        # ObjectState delegation to store editable config on pipeline_config.
        from objectstate import ObjectStateRegistry

        global_config = self.host.global_config
        state = ObjectStateRegistry.get_by_scope(plate_path)
        if state is not None:
            pipeline_config = state.to_object(update_delegate=False)
        else:
            # Fallback (should be rare): no ObjectState present
            orchestrator = ObjectStateRegistry.get_object(plate_path)
            if orchestrator is not None:
                pipeline_config = orchestrator.pipeline_config
            else:
                from openhcs.core.config import PipelineConfig

                pipeline_config = PipelineConfig()

        logger.info(f"Executing plate: {plate_path}")

        def _submit():
            return self.client_service.zmq_client.submit_pipeline(
                plate_id=str(plate_path),
                pipeline_steps=definition_pipeline,
                global_config=global_config,
                pipeline_config=pipeline_config,
            )

        response = await loop.run_in_executor(None, _submit)

        execution_id = response.get("execution_id")
        if execution_id:
            self.host.plate_execution_ids[plate_path] = execution_id
            self.host.current_execution_id = execution_id

        logger.info(f"Plate {plate_path} submission response: {response.get('status')}")

        status = response.get("status")
        if status == "accepted":
            logger.info(
                f"Plate {plate_path} execution submitted successfully, ID={execution_id}"
            )
            self.host.emit_status(f"Submitted {plate_path} (queued on server)")
            if execution_id:
                self._start_completion_poller(execution_id, plate_path)
        else:
            error_msg = response.get("message", "Unknown error")
            logger.error(f"Plate {plate_path} submission failed: {error_msg}")
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
        """Handle execution failure - mark plates and cleanup."""
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

    def _start_completion_poller(self, execution_id: str, plate_path: str) -> None:
        """Start background thread to poll for plate execution completion."""
        import time

        def poll_completion():
            try:
                previous_status = "queued"
                while True:
                    time.sleep(0.5)

                    if self.client_service.zmq_client is None:
                        logger.debug(
                            f"ZMQ client disconnected, stopping poller for {plate_path}"
                        )
                        break

                    try:
                        status_response = self.client_service.zmq_client.get_status(
                            execution_id
                        )

                        if status_response.get("status") == "ok":
                            execution = status_response.get("execution", {})
                            exec_status = execution.get("status")

                            # Detect queued → running transition
                            if exec_status == "running" and previous_status == "queued":
                                logger.info(
                                    f"🔄 Detected transition: {plate_path} queued → running"
                                )
                                self.host.plate_execution_states[plate_path] = "running"
                                self.host.update_item_list()
                                self.host.emit_status(f"▶️ Running {plate_path}")
                                previous_status = "running"

                            # Check completion
                            if exec_status == "complete":
                                logger.info(f"✅ Execution complete: {plate_path}")
                                results_summary = (
                                    execution.get("results_summary", {}) or {}
                                )
                                logger.info(
                                    "Completion results_summary for %s: %s",
                                    plate_path,
                                    results_summary,
                                )
                                output_plate_root = (
                                    results_summary.get("output_plate_root")
                                    if isinstance(results_summary, dict)
                                    else None
                                )
                                auto_add_output_plate = (
                                    results_summary.get(
                                        "auto_add_output_plate_to_plate_manager"
                                    )
                                    if isinstance(results_summary, dict)
                                    else None
                                )
                                result = {
                                    "status": "complete",
                                    "execution_id": execution_id,
                                    "results": results_summary,
                                    "output_plate_root": output_plate_root,
                                    "auto_add_output_plate_to_plate_manager": auto_add_output_plate,
                                }
                                self.host.on_plate_completed(
                                    plate_path, "complete", result
                                )
                                self._check_all_completed()
                                break
                            elif exec_status == "failed":
                                error_msg = execution.get("error", "Unknown error")
                                traceback_str = execution.get("traceback", "")

                                # Log full traceback if available
                                if traceback_str:
                                    logger.error(
                                        f"❌ Execution failed: {plate_path}\n{traceback_str}"
                                    )
                                else:
                                    logger.error(
                                        f"❌ Execution failed: {plate_path}: {error_msg}"
                                    )

                                result = {
                                    "status": "error",
                                    "execution_id": execution_id,
                                    "message": error_msg,
                                    "traceback": traceback_str,
                                }
                                self.host.on_plate_completed(
                                    plate_path, "failed", result
                                )
                                self._check_all_completed()
                                break
                            elif exec_status == "cancelled":
                                logger.info(f"🚫 Execution cancelled: {plate_path}")
                                result = {
                                    "status": "cancelled",
                                    "execution_id": execution_id,
                                    "message": "Execution was cancelled",
                                }
                                self.host.on_plate_completed(
                                    plate_path, "cancelled", result
                                )
                                self._check_all_completed()
                                break
                        else:
                            error_msg = status_response.get(
                                "error", "Execution status unavailable"
                            )
                            logger.warning(
                                "Execution status error for %s: %s",
                                plate_path,
                                error_msg,
                            )
                            self.host.on_plate_completed(
                                plate_path,
                                "failed",
                                {
                                    "status": "failed",
                                    "execution_id": execution_id,
                                    "message": error_msg,
                                },
                            )
                            self._check_all_completed()
                            break
                    except Exception as poll_error:
                        logger.warning(
                            f"Error polling status for {plate_path}: {poll_error}"
                        )

            except Exception as e:
                logger.error(
                    f"Error in completion poller for {plate_path}: {e}", exc_info=True
                )
                self.host.emit_error(f"{plate_path}: {e}")

        thread = threading.Thread(target=poll_completion, daemon=True)
        thread.start()

    def _on_progress(self, message: dict) -> None:
        """Handle progress updates from ZMQ execution server."""
        plate_id = str(message["plate_id"])
        axis_id = message["axis_id"]
        step_name = message["step_name"]
        phase = message["phase"]
        status = message["status"]
        percent = message["percent"]

        self.host.plate_progress[plate_id] = {
            "axis_id": axis_id,
            "step_name": step_name,
            "phase": phase,
            "status": status,
            "percent": percent,
        }
        self.host.emit_status(
            f"{plate_id} [{axis_id}] {step_name} {percent:.0f}% {phase}"
        )
        self.host.update_item_list()

    def _check_all_completed(self) -> None:
        """Check if all plates are completed and call host hook if so."""
        all_done = all(
            state in ("completed", "failed")
            for state in self.host.plate_execution_states.values()
        )
        if all_done:
            logger.info("All plates completed")
            completed = sum(
                1 for s in self.host.plate_execution_states.values() if s == "completed"
            )
            failed = sum(
                1 for s in self.host.plate_execution_states.values() if s == "failed"
            )
            self.host.on_all_plates_completed(completed, failed)

    def stop_execution(self, force: bool = False) -> None:
        """Stop execution - graceful or force kill."""
        port = self.port

        def kill_server():
            from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
            from zmqruntime.client import ZMQClient

            try:
                graceful = not force
                logger.info(
                    f"🛑 {'Gracefully' if graceful else 'Force'} killing server on port {port}..."
                )
                success = ZMQClient.kill_server_on_port(
                    port, graceful=graceful, config=OPENHCS_ZMQ_CONFIG
                )

                if success:
                    logger.info(
                        f"✅ Successfully {'quit' if graceful else 'force killed'} server"
                    )
                    for plate_path in list(self.host.plate_execution_states.keys()):
                        self.host.emit_execution_complete(
                            {"status": "cancelled"}, plate_path
                        )
                else:
                    logger.warning(f"❌ Failed to stop server on port {port}")
                    self.host.emit_error(f"Failed to stop execution on port {port}")
            except Exception as e:
                logger.error(f"❌ Error stopping server: {e}")
                self.host.emit_error(f"Error stopping execution: {e}")

        thread = threading.Thread(target=kill_server, daemon=True)
        thread.start()

    def disconnect(self) -> None:
        """Disconnect ZMQ client (for cleanup)."""
        if self.client_service.zmq_client is not None:
            try:
                self.client_service.disconnect_sync()
            except Exception as e:
                logger.warning(f"Error disconnecting ZMQ client: {e}")
