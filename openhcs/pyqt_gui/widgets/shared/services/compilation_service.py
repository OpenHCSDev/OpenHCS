"""
Compilation service for plate pipeline compilation.

Extracts compilation logic from PlateManagerWidget into a reusable service.
"""
import copy
import asyncio
import logging
from typing import Dict, List, Any, Protocol, runtime_checkable

from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline import Pipeline
from openhcs.constants.constants import VariableComponents

logger = logging.getLogger(__name__)


@runtime_checkable
class CompilationHost(Protocol):
    """Protocol for widgets that host the compilation service."""
    
    # State attributes the service needs access to
    global_config: Any
    orchestrators: Dict[str, PipelineOrchestrator]
    plate_configs: Dict[str, Dict]
    plate_compiled_data: Dict[str, Any]
    
    # Methods the service calls back to
    def emit_progress_started(self, count: int) -> None: ...
    def emit_progress_updated(self, value: int) -> None: ...
    def emit_progress_finished(self) -> None: ...
    def emit_orchestrator_state(self, plate_path: str, state: str) -> None: ...
    def emit_compilation_error(self, plate_name: str, error: str) -> None: ...
    def emit_status(self, msg: str) -> None: ...
    def get_pipeline_definition(self, plate_path: str) -> List: ...
    def update_button_states(self) -> None: ...


class CompilationService:
    """
    Service for compiling plate pipelines.
    
    Handles:
    - Orchestrator initialization
    - Pipeline compilation with context setup
    - Progress reporting via host callbacks
    """
    
    def __init__(self, host: CompilationHost):
        self.host = host
    
    async def compile_plates(self, selected_items: List[Dict]) -> None:
        """
        Compile pipelines for selected plates.
        
        Args:
            selected_items: List of plate data dicts with 'path' and 'name' keys
        """
        # Set up global context in worker thread
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        from openhcs.core.config import GlobalPipelineConfig
        ensure_global_config_context(GlobalPipelineConfig, self.host.global_config)
        
        self.host.emit_progress_started(len(selected_items))
        
        for i, plate_data in enumerate(selected_items):
            plate_path = plate_data['path']
            
            # Get definition pipeline
            definition_pipeline = self.host.get_pipeline_definition(plate_path)
            if not definition_pipeline:
                logger.warning(f"No pipeline defined for {plate_data['name']}, using empty pipeline")
                definition_pipeline = []
            
            # Validate func attributes
            self._validate_pipeline_steps(definition_pipeline)
            
            try:
                # Get or create orchestrator
                orchestrator = await self._get_or_create_orchestrator(plate_path)
                
                # Make fresh copy for compilation
                execution_pipeline = copy.deepcopy(definition_pipeline)
                self._fix_step_ids(execution_pipeline)
                
                # Compile
                compiled_data = await self._compile_pipeline(
                    orchestrator, definition_pipeline, execution_pipeline
                )
                
                # Store results
                self.host.plate_compiled_data[plate_path] = compiled_data
                logger.info(f"Successfully compiled {plate_path}")
                self.host.emit_orchestrator_state(plate_path, "COMPILED")
                
            except Exception as e:
                logger.error(f"COMPILATION ERROR: {plate_path}: {e}", exc_info=True)
                plate_data['error'] = str(e)
                self.host.emit_orchestrator_state(plate_path, "COMPILE_FAILED")
                self.host.emit_compilation_error(plate_data['name'], str(e))
            
            self.host.emit_progress_updated(i + 1)
        
        self.host.emit_progress_finished()
        self.host.emit_status(f"Compilation completed for {len(selected_items)} plate(s)")
        self.host.update_button_states()
    
    def _validate_pipeline_steps(self, pipeline: List) -> None:
        """Validate that steps have required func attribute."""
        for i, step in enumerate(pipeline):
            if not hasattr(step, 'func'):
                raise AttributeError(
                    f"Step '{step.name}' is missing 'func' attribute. "
                    "This usually means the pipeline was loaded from a compiled state."
                )

    async def _get_or_create_orchestrator(self, plate_path: str) -> PipelineOrchestrator:
        """Get existing orchestrator or create and initialize a new one."""
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        from openhcs.core.config import GlobalPipelineConfig

        if plate_path in self.host.orchestrators:
            orchestrator = self.host.orchestrators[plate_path]
            if not orchestrator.is_initialized():
                def initialize_with_context():
                    ensure_global_config_context(GlobalPipelineConfig, self.host.global_config)
                    return orchestrator.initialize()

                loop = asyncio.get_event_loop()
                await loop.run_in_executor(None, initialize_with_context)
        else:
            # Create new orchestrator with isolated registry
            from openhcs.io.base import _create_storage_registry
            plate_registry = _create_storage_registry()

            orchestrator = PipelineOrchestrator(
                plate_path=plate_path,
                storage_registry=plate_registry
            )

            saved_config = self.host.plate_configs.get(str(plate_path))
            if saved_config:
                orchestrator.apply_pipeline_config(saved_config)

            def initialize_with_context():
                ensure_global_config_context(GlobalPipelineConfig, self.host.global_config)
                return orchestrator.initialize()

            loop = asyncio.get_event_loop()
            await loop.run_in_executor(None, initialize_with_context)
            self.host.orchestrators[plate_path] = orchestrator

        self.host.orchestrators[plate_path] = orchestrator
        return orchestrator

    def _fix_step_ids(self, pipeline: List) -> None:
        """Fix step IDs after deep copy and ensure variable_components."""
        from dataclasses import replace

        for step in pipeline:
            step.step_id = str(id(step))

            # Ensure variable_components is never None
            if step.processing_config.variable_components is None or not step.processing_config.variable_components:
                if step.processing_config.variable_components is None:
                    logger.warning(f"Step '{step.name}' has None variable_components, setting default")
                step.processing_config = replace(
                    step.processing_config,
                    variable_components=[VariableComponents.SITE]
                )

    async def _compile_pipeline(
        self,
        orchestrator: PipelineOrchestrator,
        definition_pipeline: List,
        execution_pipeline: List
    ) -> Dict:
        """Compile pipeline and return compiled data dict."""
        from openhcs.config_framework.lazy_factory import ensure_global_config_context
        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.constants import MULTIPROCESSING_AXIS

        pipeline_obj = Pipeline(steps=execution_pipeline)
        loop = asyncio.get_event_loop()

        # Get wells
        wells = await loop.run_in_executor(
            None,
            lambda: orchestrator.get_component_keys(MULTIPROCESSING_AXIS)
        )

        # Compile with context
        def compile_with_context():
            ensure_global_config_context(GlobalPipelineConfig, self.host.global_config)
            return orchestrator.compile_pipelines(pipeline_obj.steps, wells)

        compilation_result = await loop.run_in_executor(None, compile_with_context)
        compiled_contexts = compilation_result['compiled_contexts']

        return {
            'definition_pipeline': definition_pipeline,
            'execution_pipeline': execution_pipeline,
            'compiled_contexts': compiled_contexts
        }

