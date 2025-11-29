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
from typing import Dict, Optional, Callable, Any, Protocol, List

from openhcs.core.orchestrator.orchestrator import OrchestratorState

logger = logging.getLogger(__name__)


class ExecutionHost(Protocol):
    """Protocol for the widget that hosts ZMQ execution."""

    # State attributes
    execution_state: str
    plate_execution_ids: Dict[str, str]
    plate_execution_states: Dict[str, str]
    orchestrators: Dict[str, Any]
    plate_compiled_data: Dict[str, Any]
    global_config: Any
    current_execution_id: Optional[str]

    # Signal emission methods
    def emit_status(self, msg: str) -> None: ...
    def emit_error(self, msg: str) -> None: ...
    def emit_orchestrator_state(self, plate_path: str, state: str) -> None: ...
    def emit_execution_complete(self, result: dict, plate_path: str) -> None: ...
    def emit_clear_logs(self) -> None: ...
    def update_button_states(self) -> None: ...
    def update_item_list(self) -> None: ...

    # Execution completion hooks
    def on_plate_completed(self, plate_path: str, status: str, result: dict) -> None: ...
    def on_all_plates_completed(self, completed_count: int, failed_count: int) -> None: ...


class ZMQExecutionService:
    """
    Service for managing ZMQ execution of pipelines.
    
    Handles client lifecycle, submission, polling, and shutdown.
    Delegates UI updates back to host widget via signals.
    """
    
    def __init__(self, host: ExecutionHost, port: int = 7777):
        self.host = host
        self.port = port
        self.zmq_client = None
    
    async def run_plates(self, ready_items: List[Dict]) -> None:
        """Run plates using ZMQ execution client."""
        try:
            from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
            
            plate_paths = [item['path'] for item in ready_items]
            logger.info(f"Starting ZMQ execution for {len(plate_paths)} plates")
            
            self.host.emit_clear_logs()
            loop = asyncio.get_event_loop()
            
            # Cleanup old client
            await self._disconnect_client(loop)
            
            # Create new client
            logger.info("🔌 Creating new ZMQ client")
            self.zmq_client = ZMQExecutionClient(
                port=self.port,
                persistent=True,
                progress_callback=self._on_progress
            )
            
            # Connect
            connected = await loop.run_in_executor(None, lambda: self.zmq_client.connect(timeout=15))
            if not connected:
                raise RuntimeError("Failed to connect to ZMQ execution server")
            logger.info("✅ Connected to ZMQ execution server")
            
            # Initialize execution tracking
            self.host.plate_execution_ids.clear()
            self.host.plate_execution_states.clear()
            
            for item in ready_items:
                plate_path = item['path']
                self.host.plate_execution_states[plate_path] = "queued"
                if plate_path in self.host.orchestrators:
                    self.host.orchestrators[plate_path]._state = OrchestratorState.EXECUTING
                    self.host.emit_orchestrator_state(plate_path, OrchestratorState.EXECUTING.value)
            
            self.host.execution_state = "running"
            self.host.emit_status(f"Submitting {len(ready_items)} plate(s) to ZMQ server...")
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
        if self.zmq_client is not None:
            logger.info("🧹 Disconnecting previous ZMQ client")
            try:
                await loop.run_in_executor(None, self.zmq_client.disconnect)
            except Exception as e:
                logger.warning(f"Error disconnecting old client: {e}")
            finally:
                self.zmq_client = None

    async def _submit_plate(self, plate_path: str, loop) -> None:
        """Submit a single plate for execution."""
        compiled_data = self.host.plate_compiled_data[plate_path]
        definition_pipeline = compiled_data['definition_pipeline']

        # Get config
        if plate_path in self.host.orchestrators:
            global_config = self.host.global_config
            pipeline_config = self.host.orchestrators[plate_path].pipeline_config
        else:
            global_config = self.host.global_config
            from openhcs.core.config import PipelineConfig
            pipeline_config = PipelineConfig()

        logger.info(f"Executing plate: {plate_path}")

        def _submit():
            return self.zmq_client.submit_pipeline(
                plate_id=str(plate_path),
                pipeline_steps=definition_pipeline,
                global_config=global_config,
                pipeline_config=pipeline_config
            )

        response = await loop.run_in_executor(None, _submit)

        execution_id = response.get('execution_id')
        if execution_id:
            self.host.plate_execution_ids[plate_path] = execution_id
            self.host.current_execution_id = execution_id

        logger.info(f"Plate {plate_path} submission response: {response.get('status')}")

        status = response.get('status')
        if status == 'accepted':
            logger.info(f"Plate {plate_path} execution submitted successfully, ID={execution_id}")
            self.host.emit_status(f"Submitted {plate_path} (queued on server)")
            if execution_id:
                self._start_completion_poller(execution_id, plate_path)
        else:
            error_msg = response.get('message', 'Unknown error')
            logger.error(f"Plate {plate_path} submission failed: {error_msg}")
            self.host.emit_error(f"Submission failed for {plate_path}: {error_msg}")
            self.host.plate_execution_states[plate_path] = "failed"
            if plate_path in self.host.orchestrators:
                self.host.orchestrators[plate_path]._state = OrchestratorState.EXEC_FAILED
                self.host.emit_orchestrator_state(plate_path, OrchestratorState.EXEC_FAILED.value)

    async def _handle_execution_failure(self, loop) -> None:
        """Handle execution failure - mark plates and cleanup."""
        for plate_path in self.host.plate_execution_states.keys():
            self.host.plate_execution_states[plate_path] = "failed"
            if plate_path in self.host.orchestrators:
                self.host.orchestrators[plate_path]._state = OrchestratorState.EXEC_FAILED
                self.host.emit_orchestrator_state(plate_path, OrchestratorState.EXEC_FAILED.value)

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

                    if self.zmq_client is None:
                        logger.debug(f"ZMQ client disconnected, stopping poller for {plate_path}")
                        break

                    try:
                        status_response = self.zmq_client.get_status(execution_id)

                        if status_response.get('status') == 'ok':
                            execution = status_response.get('execution', {})
                            exec_status = execution.get('status')

                            # Detect queued → running transition
                            if exec_status == 'running' and previous_status == 'queued':
                                logger.info(f"🔄 Detected transition: {plate_path} queued → running")
                                self.host.plate_execution_states[plate_path] = "running"
                                self.host.update_item_list()
                                self.host.emit_status(f"▶️ Running {plate_path}")
                                previous_status = "running"

                            # Check completion
                            if exec_status == 'complete':
                                logger.info(f"✅ Execution complete: {plate_path}")
                                result = {'status': 'complete', 'execution_id': execution_id,
                                          'results': execution.get('results_summary', {})}
                                self.host.on_plate_completed(plate_path, 'complete', result)
                                self._check_all_completed()
                                break
                            elif exec_status == 'failed':
                                logger.info(f"❌ Execution failed: {plate_path}")
                                result = {'status': 'error', 'execution_id': execution_id,
                                          'message': execution.get('error')}
                                self.host.on_plate_completed(plate_path, 'failed', result)
                                self._check_all_completed()
                                break
                            elif exec_status == 'cancelled':
                                logger.info(f"🚫 Execution cancelled: {plate_path}")
                                result = {'status': 'cancelled', 'execution_id': execution_id,
                                          'message': 'Execution was cancelled'}
                                self.host.on_plate_completed(plate_path, 'cancelled', result)
                                self._check_all_completed()
                                break
                    except Exception as poll_error:
                        logger.warning(f"Error polling status for {plate_path}: {poll_error}")

            except Exception as e:
                logger.error(f"Error in completion poller for {plate_path}: {e}", exc_info=True)
                self.host.emit_error(f"{plate_path}: {e}")

        thread = threading.Thread(target=poll_completion, daemon=True)
        thread.start()

    def _on_progress(self, message: dict) -> None:
        """Handle progress updates from ZMQ execution server."""
        try:
            well_id = message.get('well_id', 'unknown')
            step = message.get('step', 'unknown')
            status = message.get('status', 'unknown')
            self.host.emit_status(f"[{well_id}] {step}: {status}")
        except Exception as e:
            logger.warning(f"Failed to handle progress update: {e}")

    def _check_all_completed(self) -> None:
        """Check if all plates are completed and call host hook if so."""
        all_done = all(
            state in ("completed", "failed")
            for state in self.host.plate_execution_states.values()
        )
        if all_done:
            logger.info("All plates completed")
            completed = sum(1 for s in self.host.plate_execution_states.values() if s == "completed")
            failed = sum(1 for s in self.host.plate_execution_states.values() if s == "failed")
            self.host.on_all_plates_completed(completed, failed)

    def stop_execution(self, force: bool = False) -> None:
        """Stop execution - graceful or force kill."""
        if self.zmq_client is None:
            return

        port = self.port

        def kill_server():
            from openhcs.runtime.zmq_base import ZMQClient
            try:
                graceful = not force
                logger.info(f"🛑 {'Gracefully' if graceful else 'Force'} killing server on port {port}...")
                success = ZMQClient.kill_server_on_port(port, graceful=graceful)

                if success:
                    logger.info(f"✅ Successfully {'quit' if graceful else 'force killed'} server")
                    for plate_path in list(self.host.plate_execution_states.keys()):
                        self.host.emit_execution_complete({'status': 'cancelled'}, plate_path)
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
        if self.zmq_client is not None:
            try:
                self.zmq_client.disconnect()
            except Exception as e:
                logger.warning(f"Error disconnecting ZMQ client: {e}")
            finally:
                self.zmq_client = None

