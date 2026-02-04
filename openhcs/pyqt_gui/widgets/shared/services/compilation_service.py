"""
Compilation service for plate pipeline compilation.

Extracts compilation logic from PlateManagerWidget into a reusable service.
"""

import asyncio
import logging
from typing import Dict, List, Any

from openhcs.pyqt_gui.widgets.shared.services.zmq_client_service import (
    ZMQClientService,
)
from openhcs.core.orchestrator.orchestrator import OrchestratorState

logger = logging.getLogger(__name__)


class CompilationService:
    """
    Service for compiling plate pipelines.

    Handles:
    - Orchestrator initialization
    - Pipeline compilation with context setup
    - Progress reporting via host callbacks
    """

    def __init__(self, host, client_service: ZMQClientService | None = None):
        self.host = host
        self.client_service = client_service or ZMQClientService()

    async def compile_plates(self, selected_items: List[Dict]) -> None:
        """
        Compile pipelines for selected plates.

        Args:
            selected_items: List of plate data dicts with 'path' and 'name' keys
        """
        self.host.emit_progress_started(len(selected_items))
        loop = asyncio.get_event_loop()
        zmq_client = None

        try:
            zmq_client = await self.client_service.connect(persistent=True, timeout=15)

            for i, plate_data in enumerate(selected_items):
                plate_path = str(plate_data["path"])

                # Get definition pipeline
                definition_pipeline = self.host.get_pipeline_definition(plate_path)
                if not definition_pipeline:
                    logger.warning(
                        f"No pipeline defined for {plate_data['name']}, using empty pipeline"
                    )
                    definition_pipeline = []

                # Validate func attributes
                self._validate_pipeline_steps(definition_pipeline)

                try:
                    self.host.plate_compile_pending.add(plate_path)
                    self.host.update_item_list()
                    pipeline_config = self._get_pipeline_config(plate_path)
                    response = await loop.run_in_executor(
                        None,
                        lambda: zmq_client.submit_compile(
                            plate_id=str(plate_path),
                            pipeline_steps=definition_pipeline,
                            global_config=self.host.global_config,
                            pipeline_config=pipeline_config,
                        ),
                    )
                    status = response.get("status")
                    if status != "accepted":
                        error_msg = response.get("message", "Unknown error")
                        raise RuntimeError(
                            f"Compilation submission failed: {error_msg}"
                        )

                    execution_id = response.get("execution_id")
                    if not execution_id:
                        raise RuntimeError("Compilation did not return an execution_id")

                    result = await loop.run_in_executor(
                        None, lambda: zmq_client.wait_for_completion(execution_id)
                    )
                    if result.get("status") != "complete":
                        error_msg = result.get("message", "Compilation failed")
                        raise RuntimeError(error_msg)

                    # Store results (compile success marker for UI/run button)
                    self.host.plate_compiled_data[plate_path] = {
                        "definition_pipeline": definition_pipeline,
                    }
                    self._set_orchestrator_state(plate_path, OrchestratorState.COMPILED)
                    self.host.plate_compile_pending.remove(plate_path)
                    self.host.update_item_list()
                    logger.info(f"Successfully compiled {plate_path}")
                    self.host.emit_orchestrator_state(plate_path, "COMPILED")

                except Exception as e:
                    logger.error(f"COMPILATION ERROR: {plate_path}: {e}", exc_info=True)
                    plate_data["error"] = str(e)
                    self._set_orchestrator_state(
                        plate_path, OrchestratorState.COMPILE_FAILED
                    )
                    self.host.plate_compile_pending.remove(plate_path)
                    self.host.update_item_list()
                    self.host.emit_orchestrator_state(plate_path, "COMPILE_FAILED")
                    self.host.emit_compilation_error(plate_data["name"], str(e))

                self.host.emit_progress_updated(i + 1)
        finally:
            if self.host.execution_state != "running":
                await self.client_service.disconnect()

        self.host.emit_progress_finished()
        self.host.emit_status(
            f"Compilation completed for {len(selected_items)} plate(s)"
        )
        self.host.update_button_states()

    def _validate_pipeline_steps(self, pipeline: List) -> None:
        """Validate that steps have required func attribute."""
        for i, step in enumerate(pipeline):
            func = step.func
            if func is None:
                raise AttributeError(
                    f"Step '{step.name}' has func=None. "
                    "This usually means the pipeline was loaded from a compiled state."
                )

    def _get_pipeline_config(self, plate_path: str):
        """Resolve pipeline config for a plate without local compilation."""
        from objectstate import ObjectStateRegistry
        from openhcs.core.config import PipelineConfig

        # IMPORTANT: read the per-plate PipelineConfig from ObjectState (saved+resolved)
        # rather than from the live orchestrator instance.
        state = ObjectStateRegistry.get_by_scope(plate_path)
        if state is not None:
            return state.to_object(update_delegate=False)

        orchestrator = ObjectStateRegistry.get_object(plate_path)
        if orchestrator is not None:
            return orchestrator.pipeline_config

        saved_config = self.host.plate_configs.get(str(plate_path))
        if saved_config:
            return saved_config

        return PipelineConfig()

    def _set_orchestrator_state(
        self, plate_path: str, state: OrchestratorState
    ) -> None:
        from objectstate import ObjectStateRegistry

        orchestrator = ObjectStateRegistry.get_object(plate_path)
        if orchestrator is not None:
            orchestrator._state = state

    # Local compilation removed: compile now validates via ZMQ execution server
