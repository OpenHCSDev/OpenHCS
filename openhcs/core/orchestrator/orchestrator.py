"""
Consolidated orchestrator module for OpenHCS.

This module provides a unified PipelineOrchestrator class that implements
a two-phase (compile-all-then-execute-all) pipeline execution model.

Doctrinal Clauses:
- Clause 12 — Absolute Clean Execution
- Clause 66 — Immutability After Construction
- Clause 88 — No Inferred Capabilities
- Clause 293 — GPU Pre-Declaration Enforcement
- Clause 295 — GPU Scheduling Affinity
"""

import logging
import concurrent.futures
import multiprocessing
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Union, Set

from openhcs.constants.constants import Backend, DEFAULT_WORKSPACE_DIR_SUFFIX, DEFAULT_IMAGE_EXTENSIONS, GroupBy, OrchestratorState, get_openhcs_config, AllComponents, VariableComponents
from openhcs.constants import Microscope
from openhcs.core.config import GlobalPipelineConfig, get_default_global_config, PipelineConfig, set_current_global_config, set_current_pipeline_config
from openhcs.core.metadata_cache import get_metadata_cache, MetadataCache
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.pipeline.step_attribute_stripper import StepAttributeStripper
from openhcs.core.steps.abstract import AbstractStep, get_step_id
from openhcs.core.components.validation import convert_enum_by_value
from openhcs.core.pipeline_config import PipelineConfig as CorePipelineConfig
from openhcs.core.lazy_config import resolve_lazy_configurations_for_serialization
from openhcs.io.exceptions import StorageWriteError
from openhcs.io.filemanager import FileManager
from openhcs.io.base import storage_registry
from openhcs.io.zarr import ZarrStorageBackend
from openhcs.microscopes import create_microscope_handler
from openhcs.microscopes.microscope_base import MicroscopeHandler

from openhcs.processing.backends.analysis.consolidate_analysis_results import consolidate_analysis_results

# Import generic component system - required for orchestrator functionality
from openhcs.core.components.multiprocessing import MultiprocessingCoordinator

# Optional napari import for visualization
try:
    from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer
    NapariVisualizerType = NapariStreamVisualizer
except ImportError:
    # Create a placeholder type for type hints when napari is not available
    NapariStreamVisualizer = None
    NapariVisualizerType = Any  # Use Any for type hints when napari is not available

# Optional GPU memory management imports
try:
    from openhcs.core.memory.gpu_cleanup import log_gpu_memory_usage, cleanup_all_gpu_frameworks
except ImportError:
    log_gpu_memory_usage = None
    cleanup_all_gpu_frameworks = None


logger = logging.getLogger(__name__)


def _execute_single_axis_static(
    pipeline_definition: List[AbstractStep],
    frozen_context: 'ProcessingContext',
    visualizer: Optional['NapariVisualizerType']
) -> Dict[str, Any]:
    """
    Static version of _execute_single_axis for multiprocessing compatibility.

    This function is identical to PipelineOrchestrator._execute_single_axis but doesn't
    require an orchestrator instance, making it safe for pickling in ProcessPoolExecutor.
    """
    axis_id = frozen_context.axis_id
    logger.info(f"🔥 SINGLE_AXIS: Starting execution for axis {axis_id}")

    # NUCLEAR VALIDATION
    if not frozen_context.is_frozen():
        error_msg = f"🔥 SINGLE_AXIS ERROR: Context for axis {axis_id} is not frozen before execution"
        logger.error(error_msg)
        raise RuntimeError(error_msg)

    if not pipeline_definition:
        error_msg = f"🔥 SINGLE_AXIS ERROR: Empty pipeline_definition for axis {axis_id}"
        logger.error(error_msg)
        raise RuntimeError(error_msg)

    # Execute each step in the pipeline
    for step_index, step in enumerate(pipeline_definition):
        step_name = getattr(step, 'name', 'N/A') if hasattr(step, 'name') else 'N/A'

        logger.info(f"🔥 SINGLE_AXIS: Executing step {step_index+1}/{len(pipeline_definition)} - {step_name} for axis {axis_id}")

        if not hasattr(step, 'process'):
            error_msg = f"🔥 SINGLE_AXIS ERROR: Step {step_index+1} missing process method for axis {axis_id}"
            logger.error(error_msg)
            raise RuntimeError(error_msg)

        step.process(frozen_context, step_index)
        logger.info(f"🔥 SINGLE_AXIS: Step {step_index+1}/{len(pipeline_definition)} - {step_name} completed for axis {axis_id}")

        # Handle visualization if requested
        if visualizer:
            step_plan = frozen_context.step_plans[step_index]
            if step_plan['visualize']:
                output_dir = step_plan['output_dir']
                write_backend = step_plan['write_backend']
                if output_dir:
                    logger.debug(f"Visualizing output for step {step_index} from path {output_dir} (backend: {write_backend}) for axis {axis_id}")
                    visualizer.visualize_path(
                        step_id=f"step_{step_index}",
                        path=str(output_dir),
                        backend=write_backend,
                        axis_id=axis_id
                    )
                else:
                    logger.warning(f"Step {step_index} in axis {axis_id} flagged for visualization but 'output_dir' is missing in its plan.")

    logger.info(f"🔥 SINGLE_AXIS: Pipeline execution completed successfully for axis {axis_id}")
    return {"status": "success", "axis_id": axis_id}


def _configure_worker_logging(log_file_base: str):
    """
    Configure logging and import hook for worker process.

    This function is called once per worker process when it starts.
    Each worker will get its own log file with a unique identifier.

    Args:
        log_file_base: Base path for worker log files
    """
    import os
    import logging
    import time

    # CRITICAL: Skip function registry initialization for fast worker startup
    # The environment variable is inherited from the subprocess runner
    # Note: We don't log this yet because logging isn't configured

    # Note: Import hook system was removed - using existing comprehensive registries

    # Create unique worker identifier using PID and timestamp
    worker_pid = os.getpid()
    worker_timestamp = int(time.time() * 1000000)  # Microsecond precision for uniqueness
    worker_id = f"{worker_pid}_{worker_timestamp}"
    worker_log_file = f"{log_file_base}_worker_{worker_id}.log"

    # Configure root logger to capture ALL logs from worker process
    root_logger = logging.getLogger()
    root_logger.handlers.clear()  # Clear any inherited handlers

    # Create file handler for worker logs
    file_handler = logging.FileHandler(worker_log_file)
    file_handler.setFormatter(logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s'))
    root_logger.addHandler(file_handler)
    root_logger.setLevel(logging.INFO)

    # Ensure all OpenHCS module logs are captured
    logging.getLogger("openhcs").setLevel(logging.INFO)

    # Get worker logger
    worker_logger = logging.getLogger("openhcs.worker")
    worker_logger.info(f"🔥 WORKER: Process {worker_pid} (ID: {worker_id}) logging configured")
    worker_logger.info(f"🔥 WORKER: All logs writing to: {worker_log_file}")

    # Log import hook installation status
    worker_logger.info(f"🔥 WORKER: Import hook installed for auto-discovered functions")


# Global variable to store log file base for worker processes
_worker_log_file_base = None





class PipelineOrchestrator:
    """
    Updated orchestrator supporting both global and per-orchestrator configuration.

    Global configuration: Updates all orchestrators (existing behavior)
    Per-orchestrator configuration: Affects only this orchestrator instance

    The orchestrator first compiles the pipeline for all specified axis values,
    creating frozen, immutable ProcessingContexts using `compile_plate_for_processing()`.
    Then, it executes the (now stateless) pipeline definition against these contexts,
    potentially in parallel, using `execute_compiled_plate()`.
    """

    def __init__(
        self,
        plate_path: Union[str, Path],
        workspace_path: Optional[Union[str, Path]] = None,
        *,
        global_config: Optional[GlobalPipelineConfig] = None,
        pipeline_config: Optional[PipelineConfig] = None,
        storage_registry: Optional[Any] = None, # Optional StorageRegistry instance
    ):
        # Lock removed - was orphaned code never used

        if global_config is None:
            self.global_config = get_default_global_config()
            logger.info("PipelineOrchestrator using default global configuration.")
        else:
            self.global_config = global_config

        # Initialize per-orchestrator configuration
        # Always ensure orchestrator has a pipeline config - create default if none provided
        if pipeline_config is None:
            self.pipeline_config = CorePipelineConfig()
            logger.info("PipelineOrchestrator created default pipeline configuration.")
        else:
            self.pipeline_config = pipeline_config



        # Set current pipeline config for MaterializationPathConfig defaults
        set_current_pipeline_config(self.global_config)

        if plate_path is None:
            # This case should ideally be prevented by TUI logic if plate_path is mandatory
            # for an orchestrator instance tied to a specific plate.
            # If workspace_path is also None, this will be caught later.
            pass
        elif isinstance(plate_path, str):
            plate_path = Path(plate_path)
        elif not isinstance(plate_path, Path):
            raise ValueError(f"Invalid plate_path type: {type(plate_path)}. Must be str or Path.")
        
        if plate_path:
            if not plate_path.is_absolute():
                raise ValueError(f"Plate path must be absolute: {plate_path}")
            if not plate_path.exists():
                raise FileNotFoundError(f"Plate path does not exist: {plate_path}")
            if not plate_path.is_dir():
                raise NotADirectoryError(f"Plate path is not a directory: {plate_path}")

        # Initialize _plate_path_frozen first to allow plate_path to be set during initialization
        object.__setattr__(self, '_plate_path_frozen', False)

        self.plate_path = plate_path
        self.workspace_path = workspace_path

        if self.plate_path is None and self.workspace_path is None:
            raise ValueError("Either plate_path or workspace_path must be provided for PipelineOrchestrator.")

        # Freeze plate_path immediately after setting it to prove immutability
        object.__setattr__(self, '_plate_path_frozen', True)
        logger.info(f"🔒 PLATE_PATH FROZEN: {self.plate_path} is now immutable")

        if storage_registry:
            self.registry = storage_registry
            logger.info("PipelineOrchestrator using provided StorageRegistry instance.")
        else:
            # Create a copy of the global registry to avoid modifying shared state
            from openhcs.io.base import storage_registry as global_storage_registry
            self.registry = global_storage_registry.copy()
            logger.info("PipelineOrchestrator created its own StorageRegistry instance (copy of global).")

        # Override zarr backend with orchestrator's config
        zarr_backend_with_config = ZarrStorageBackend(self.global_config.zarr)
        self.registry[Backend.ZARR.value] = zarr_backend_with_config
        logger.info(f"Orchestrator zarr backend configured with {self.global_config.zarr.compressor.value} compression")

        # Orchestrator always creates its own FileManager, using the determined registry
        self.filemanager = FileManager(self.registry)
        self.input_dir: Optional[Path] = None
        self.microscope_handler: Optional[MicroscopeHandler] = None
        self.default_pipeline_definition: Optional[List[AbstractStep]] = None
        self._initialized: bool = False
        self._state: OrchestratorState = OrchestratorState.CREATED

        # Component keys cache for fast access - uses AllComponents (includes multiprocessing axis)
        self._component_keys_cache: Dict['AllComponents', List[str]] = {}

        # Metadata cache service
        self._metadata_cache_service = get_metadata_cache()

    def __setattr__(self, name: str, value: Any) -> None:
        """
        Set an attribute, preventing modification of plate_path after it's frozen.

        This proves that plate_path is truly immutable after initialization.
        """
        if name == 'plate_path' and getattr(self, '_plate_path_frozen', False):
            import traceback
            stack_trace = ''.join(traceback.format_stack())
            error_msg = (
                f"🚫 IMMUTABLE PLATE_PATH VIOLATION: Cannot modify plate_path after freezing!\n"
                f"Current value: {getattr(self, 'plate_path', 'UNSET')}\n"
                f"Attempted new value: {value}\n"
                f"Stack trace:\n{stack_trace}"
            )
            logger.error(error_msg)
            raise AttributeError(error_msg)
        super().__setattr__(name, value)

    @property
    def state(self) -> OrchestratorState:
        """Get the current orchestrator state."""
        return self._state

    def initialize_microscope_handler(self):
        """Initializes the microscope handler."""
        if self.microscope_handler is not None:
            logger.debug("Microscope handler already initialized.")
            return
#        if self.input_dir is None:
#            raise RuntimeError("Workspace (and input_dir) must be initialized before microscope handler.")

        logger.info(f"Initializing microscope handler using input directory: {self.input_dir}...")
        try:
            # Use configured microscope type or auto-detect
            microscope_type = self.global_config.microscope.value if self.global_config.microscope != Microscope.AUTO else 'auto'
            self.microscope_handler = create_microscope_handler(
                plate_folder=str(self.plate_path),
                filemanager=self.filemanager,
                microscope_type=microscope_type,
            )
            logger.info(f"Initialized microscope handler: {type(self.microscope_handler).__name__}")
        except Exception as e:
            error_msg = f"Failed to create microscope handler: {e}"
            logger.error(error_msg)
            raise RuntimeError(error_msg) from e

    def initialize(self, workspace_path: Optional[Union[str, Path]] = None) -> 'PipelineOrchestrator':
        """
        Initializes all required components for the orchestrator.
        Must be called before other processing methods.
        Returns self for chaining.
        """
        if self._initialized:
            logger.info("Orchestrator already initialized.")
            return self

        try:
            self.initialize_microscope_handler()

            # Delegate workspace initialization to microscope handler
            logger.info("Initializing workspace with microscope handler...")
            actual_image_dir = self.microscope_handler.initialize_workspace(
                self.plate_path, workspace_path, self.filemanager
            )

            # Use the actual image directory returned by the microscope handler
            self.input_dir = Path(actual_image_dir)
            logger.info(f"Set input directory to: {self.input_dir}")

            # Set workspace_path based on what the handler returned
            if actual_image_dir != self.plate_path:
                # Handler created a workspace
                self.workspace_path = Path(actual_image_dir).parent if Path(actual_image_dir).name != "workspace" else Path(actual_image_dir)
            else:
                # Handler used plate directly (like OpenHCS)
                self.workspace_path = None

            # Mark as initialized BEFORE caching to avoid chicken-and-egg problem
            self._initialized = True
            self._state = OrchestratorState.READY

            # Auto-cache component keys and metadata for instant access
            logger.info("Caching component keys and metadata...")
            self.cache_component_keys()
            self._metadata_cache_service.cache_metadata(
                self.microscope_handler,
                self.plate_path,
                self._component_keys_cache
            )

            logger.info("PipelineOrchestrator fully initialized with cached component keys and metadata.")
            return self
        except Exception as e:
            self._state = OrchestratorState.INIT_FAILED
            logger.error(f"Failed to initialize orchestrator: {e}")
            raise

    def is_initialized(self) -> bool:
        return self._initialized

    def create_context(self, axis_id: str) -> ProcessingContext:
        """Creates a ProcessingContext for a given multiprocessing axis value."""
        if not self.is_initialized():
            raise RuntimeError("Orchestrator must be initialized before calling create_context().")
        if not axis_id:
            raise ValueError("Axis identifier must be provided.")
        if self.input_dir is None:
             raise RuntimeError("Orchestrator input_dir is not set; initialize orchestrator first.")

        context = ProcessingContext(
            global_config=self.get_effective_config(),
            axis_id=axis_id,
            filemanager=self.filemanager
        )
        # Orchestrator reference removed - was orphaned and unpickleable
        context.microscope_handler = self.microscope_handler
        context.input_dir = self.input_dir
        context.workspace_path = self.workspace_path
        context.plate_path = self.plate_path  # Add plate_path for path planner
        # Pass metadata cache for OpenHCS metadata creation
        context.metadata_cache = {}  # Initialize empty - metadata cache is not pickled
        return context

    def compile_pipelines(
        self,
        pipeline_definition: List[AbstractStep],
        well_filter: Optional[List[str]] = None,
        enable_visualizer_override: bool = False
    ) -> Dict[str, ProcessingContext]:
        """Compile pipelines for axis values (well_filter name preserved for UI compatibility)."""
        return PipelineCompiler.compile_pipelines(
            orchestrator=self,
            pipeline_definition=pipeline_definition,
            axis_filter=well_filter,  # Translate well_filter to axis_filter for generic backend
            enable_visualizer_override=enable_visualizer_override
        )

    def _execute_single_axis(
        self,
        pipeline_definition: List[AbstractStep],
        frozen_context: ProcessingContext,
        visualizer: Optional[NapariVisualizerType]
    ) -> Dict[str, Any]:
        """Executes the pipeline for a single well using its frozen context."""
        axis_id = frozen_context.axis_id
        logger.info(f"🔥 SINGLE_AXIS: Starting execution for axis {axis_id}")

        # NUCLEAR VALIDATION
        if not frozen_context.is_frozen():
            error_msg = f"🔥 SINGLE_AXIS ERROR: Context for axis {axis_id} is not frozen before execution"
            logger.error(error_msg)
            raise RuntimeError(error_msg)

        if not pipeline_definition:
            error_msg = f"🔥 SINGLE_AXIS ERROR: Empty pipeline_definition for axis {axis_id}"
            logger.error(error_msg)
            raise RuntimeError(error_msg)

        # Step IDs are consistent since pipeline_definition comes from UI (no remapping needed)

        logger.info(f"🔥 SINGLE_AXIS: Processing {len(pipeline_definition)} steps for axis {axis_id}")

        for step_index, step in enumerate(pipeline_definition):
            step_name = getattr(step, 'name', 'N/A') if hasattr(step, 'name') else 'N/A'

            logger.info(f"🔥 SINGLE_AXIS: Executing step {step_index+1}/{len(pipeline_definition)} - {step_name} for axis {axis_id}")

            if not hasattr(step, 'process'):
                error_msg = f"🔥 SINGLE_AXIS ERROR: Step {step_index+1} missing process method for axis {axis_id}"
                logger.error(error_msg)
                raise RuntimeError(error_msg)

            step.process(frozen_context, step_index)
            logger.info(f"🔥 SINGLE_AXIS: Step {step_index+1}/{len(pipeline_definition)} - {step_name} completed for axis {axis_id}")

    #        except Exception as step_error:
    #            import traceback
    #            full_traceback = traceback.format_exc()
    #            error_msg = f"🔥 SINGLE_AXIS ERROR: Step {step_index+1} ({step_id}) failed for axis {axis_id}: {step_error}"
    #            logger.error(error_msg, exc_info=True)
    #            logger.error(f"🔥 SINGLE_AXIS TRACEBACK for axis {axis_id}, step {step_index+1} ({step_id}):\n{full_traceback}")
    #            raise RuntimeError(error_msg) from step_error

            if visualizer:
                step_plan = frozen_context.step_plans[step_index]
                if step_plan['visualize']:
                    output_dir = step_plan['output_dir']
                    write_backend = step_plan['write_backend']
                    if output_dir:
                        logger.debug(f"Visualizing output for step {step_index} from path {output_dir} (backend: {write_backend}) for axis {axis_id}")
                        visualizer.visualize_path(
                            step_id=f"step_{step_index}",
                            path=str(output_dir),
                            backend=write_backend,
                            axis_id=axis_id
                        )
                    else:
                        logger.warning(f"Step {step_index} in axis {axis_id} flagged for visualization but 'output_dir' is missing in its plan.")
        
        logger.info(f"🔥 SINGLE_AXIS: Pipeline execution completed successfully for axis {axis_id}")
        return {"status": "success", "axis_id": axis_id}

    def execute_compiled_plate(
        self,
        pipeline_definition: List[AbstractStep],
        compiled_contexts: Dict[str, ProcessingContext],
        max_workers: Optional[int] = None,
        visualizer: Optional[NapariVisualizerType] = None,
        log_file_base: Optional[str] = None
    ) -> Dict[str, Dict[str, Any]]:
        """
        Execute-all phase: Runs the stateless pipeline against compiled contexts.

        Args:
            pipeline_definition: The stateless list of AbstractStep objects.
            compiled_contexts: Dict of axis_id to its compiled, frozen ProcessingContext.
                               Obtained from `compile_plate_for_processing`.
            max_workers: Maximum number of worker threads for parallel execution.
            visualizer: Optional instance of NapariStreamVisualizer for real-time visualization
                        (requires napari to be installed; must be initialized with orchestrator's filemanager by the caller).
            log_file_base: Base path for worker process log files (without extension).
                          Each worker will create its own log file: {log_file_base}_worker_{pid}.log

        Returns:
            A dictionary mapping well IDs to their execution status (success/error and details).
        """
        if not self.is_initialized():
             raise RuntimeError("Orchestrator must be initialized before executing.")
        if not pipeline_definition:
            raise ValueError("A valid (stateless) pipeline definition must be provided.")
        if not compiled_contexts:
            logger.warning("No compiled contexts provided for execution.")
            return {}
        
        # Use effective config (includes pipeline config) instead of global config directly
        actual_max_workers = max_workers if max_workers is not None else self.get_effective_config().num_workers
        if actual_max_workers <= 0: # Ensure positive number of workers
            actual_max_workers = 1

        self._state = OrchestratorState.EXECUTING
        logger.info(f"Starting execution for {len(compiled_contexts)} axis values with max_workers={actual_max_workers}.")

        # 🔍 VRAM TRACKING: Log initial memory state
        try:
            if log_gpu_memory_usage:
                log_gpu_memory_usage("plate execution start")
        except Exception:
            pass

        try:
            execution_results: Dict[str, Dict[str, Any]] = {}

            # CUDA COMPATIBILITY: Set spawn method for multiprocessing to support CUDA
            try:
                # Check if spawn method is available and set it if not already set
                current_method = multiprocessing.get_start_method(allow_none=True)
                if current_method != 'spawn':
                    logger.info(f"🔥 CUDA: Setting multiprocessing start method from '{current_method}' to 'spawn' for CUDA compatibility")
                    multiprocessing.set_start_method('spawn', force=True)
                else:
                    logger.debug("🔥 CUDA: Multiprocessing start method already set to 'spawn'")
            except RuntimeError as e:
                # Start method may already be set, which is fine
                logger.debug(f"🔥 CUDA: Start method already configured: {e}")

            # Choose executor type based on effective config for debugging support
            effective_config = self.get_effective_config()
            executor_type = "ThreadPoolExecutor" if effective_config.use_threading else "ProcessPoolExecutor"
            logger.info(f"🔥 ORCHESTRATOR: Creating {executor_type} with {actual_max_workers} workers")

            # DEATH DETECTION: Mark executor creation
            logger.info(f"🔥 DEATH_MARKER: BEFORE_{executor_type.upper()}_CREATION")

            # Choose appropriate executor class and configure worker logging
            if effective_config.use_threading:
                logger.info("🔥 DEBUG MODE: Using ThreadPoolExecutor for easier debugging")
                executor = concurrent.futures.ThreadPoolExecutor(max_workers=actual_max_workers)
            else:
                logger.info("🔥 PRODUCTION MODE: Using ProcessPoolExecutor for true parallelism")
                if log_file_base:
                    logger.info(f"🔥 WORKER LOGGING: Configuring worker processes with log base: {log_file_base}")
                    executor = concurrent.futures.ProcessPoolExecutor(
                        max_workers=actual_max_workers,
                        initializer=_configure_worker_logging,
                        initargs=(log_file_base,)
                    )
                else:
                    logger.info("🔥 WORKER LOGGING: No log base provided, workers will inherit logging")
                    executor = concurrent.futures.ProcessPoolExecutor(max_workers=actual_max_workers)

            logger.info(f"🔥 DEATH_MARKER: ENTERING_{executor_type.upper()}_CONTEXT")
            with executor:
                logger.info(f"🔥 DEATH_MARKER: {executor_type.upper()}_CREATED_SUCCESSFULLY")
                logger.info(f"🔥 ORCHESTRATOR: {executor_type} created, submitting {len(compiled_contexts)} tasks")

                # NUCLEAR ERROR TRACING: Create snapshot of compiled_contexts to prevent iteration issues
                contexts_snapshot = dict(compiled_contexts.items())
                logger.info(f"🔥 ORCHESTRATOR: Created contexts snapshot with {len(contexts_snapshot)} items")

                # CRITICAL FIX: Resolve all lazy dataclass instances before multiprocessing
                # This ensures that the contexts are safe for pickling in ProcessPoolExecutor
                # Note: Don't resolve pipeline_definition as it may overwrite collision-resolved configs
                logger.info("🔥 ORCHESTRATOR: Resolving lazy dataclasses for multiprocessing compatibility")
                contexts_snapshot = resolve_lazy_configurations_for_serialization(contexts_snapshot)
                logger.info("🔥 ORCHESTRATOR: Lazy dataclass resolution completed")

                logger.info("🔥 DEATH_MARKER: BEFORE_TASK_SUBMISSION_LOOP")
                future_to_axis_id = {}
                config = get_openhcs_config()
                if not config:
                    raise RuntimeError("Component configuration is required for orchestrator execution")
                axis_name = config.multiprocessing_axis.value
                for axis_id, context in contexts_snapshot.items():
                    try:
                        logger.info(f"🔥 DEATH_MARKER: SUBMITTING_TASK_FOR_{axis_name.upper()}_{axis_id}")
                        logger.info(f"🔥 ORCHESTRATOR: Submitting task for {axis_name} {axis_id}")
                        # Resolve all arguments before passing to ProcessPoolExecutor
                        resolved_context = resolve_lazy_configurations_for_serialization(context)
                        resolved_visualizer = resolve_lazy_configurations_for_serialization(visualizer)

                        # Use static function to avoid pickling the orchestrator instance
                        # Note: Use original pipeline_definition to preserve collision-resolved configs
                        future = executor.submit(_execute_single_axis_static, pipeline_definition, resolved_context, resolved_visualizer)
                        future_to_axis_id[future] = axis_id
                        logger.info(f"🔥 ORCHESTRATOR: Task submitted for {axis_name} {axis_id}")
                        logger.info(f"🔥 DEATH_MARKER: TASK_SUBMITTED_FOR_{axis_name.upper()}_{axis_id}")
                    except Exception as submit_error:
                        error_msg = f"🔥 ORCHESTRATOR ERROR: Failed to submit task for {axis_name} {axis_id}: {submit_error}"
                        logger.error(error_msg, exc_info=True)
                        # FAIL-FAST: Re-raise task submission errors immediately
                        raise

                logger.info("🔥 DEATH_MARKER: TASK_SUBMISSION_LOOP_COMPLETED")

                logger.info(f"🔥 ORCHESTRATOR: All {len(future_to_axis_id)} tasks submitted, waiting for completion")
                logger.info("🔥 DEATH_MARKER: BEFORE_COMPLETION_LOOP")

                completed_count = 0
                logger.info("🔥 DEATH_MARKER: ENTERING_AS_COMPLETED_LOOP")
                for future in concurrent.futures.as_completed(future_to_axis_id):
                    axis_id = future_to_axis_id[future]
                    completed_count += 1
                    logger.info(f"🔥 DEATH_MARKER: PROCESSING_COMPLETED_TASK_{completed_count}_{axis_name.upper()}_{axis_id}")
                    logger.info(f"🔥 ORCHESTRATOR: Task {completed_count}/{len(future_to_axis_id)} completed for {axis_name} {axis_id}")

                    try:
                        logger.info(f"🔥 DEATH_MARKER: CALLING_FUTURE_RESULT_FOR_{axis_name.upper()}_{axis_id}")
                        result = future.result()
                        logger.info(f"🔥 DEATH_MARKER: FUTURE_RESULT_SUCCESS_FOR_{axis_name.upper()}_{axis_id}")
                        logger.info(f"🔥 ORCHESTRATOR: {axis_name.title()} {axis_id} result: {result}")
                        execution_results[axis_id] = result
                        logger.info(f"🔥 DEATH_MARKER: RESULT_STORED_FOR_{axis_name.upper()}_{axis_id}")
                    except Exception as exc:
                        import traceback
                        full_traceback = traceback.format_exc()
                        error_msg = f"{axis_name.title()} {axis_id} generated an exception during execution: {exc}"
                        logger.error(f"🔥 ORCHESTRATOR ERROR: {error_msg}", exc_info=True)
                        logger.error(f"🔥 ORCHESTRATOR FULL TRACEBACK for {axis_name} {axis_id}:\n{full_traceback}")
                        # FAIL-FAST: Re-raise immediately instead of storing error
                        raise

                logger.info("🔥 DEATH_MARKER: COMPLETION_LOOP_FINISHED")

                logger.info(f"🔥 ORCHESTRATOR: All tasks completed, {len(execution_results)} results collected")


            # 🔥 GPU CLEANUP: Clear GPU memory after plate execution
            try:
                if cleanup_all_gpu_frameworks:
                    cleanup_all_gpu_frameworks()
                    logger.debug("🔥 GPU CLEANUP: Cleared all GPU frameworks after plate execution")
            except Exception as cleanup_error:
                logger.warning(f"Failed to cleanup GPU memory after plate execution: {cleanup_error}")



            logger.info(f"🔥 ORCHESTRATOR: Plate execution completed, checking for analysis consolidation")
            # Run automatic analysis consolidation if enabled
            if self.global_config.analysis_consolidation.enabled:
                try:
                    # Get results directory from compiled contexts (Option 2: use existing paths)
                    results_dir = None
                    for axis_id, context in compiled_contexts.items():
                        # Look for any step that has an output_dir - this is where materialization happens
                        for step_index, step_plan in context.step_plans.items():
                            if 'output_dir' in step_plan:
                                # Found an output directory, check if it has a results subdirectory
                                potential_results_dir = Path(step_plan['output_dir']) / self.global_config.materialization_results_path
                                if potential_results_dir.exists():
                                    results_dir = potential_results_dir
                                    logger.info(f"🔍 CONSOLIDATION: Found results directory from step {step_index}: {results_dir}")
                                    break
                        if results_dir:
                            break

                    if results_dir and results_dir.exists():
                        # Check if there are actually CSV files (materialized results)
                        csv_files = list(results_dir.glob("*.csv"))
                        if csv_files:
                            logger.info(f"🔄 CONSOLIDATION: Found {len(csv_files)} CSV files, running consolidation")
                            # Get well IDs from compiled contexts
                            axis_ids = list(compiled_contexts.keys())
                            logger.info(f"🔄 CONSOLIDATION: Using well IDs: {axis_ids}")

                            consolidate_analysis_results(
                                results_directory=str(results_dir),
                                axis_ids=axis_ids,
                                consolidation_config=self.global_config.analysis_consolidation,
                                plate_metadata_config=self.global_config.plate_metadata
                            )
                            logger.info("✅ CONSOLIDATION: Completed successfully")
                        else:
                            logger.info(f"⏭️ CONSOLIDATION: No CSV files found in {results_dir}, skipping")
                    else:
                        logger.info(f"⏭️ CONSOLIDATION: No results directory found in compiled contexts")
                except Exception as e:
                    logger.error(f"❌ CONSOLIDATION: Failed: {e}")
            
            # Update state based on execution results
            if all(result.get("status") == "success" for result in execution_results.values()):
                self._state = OrchestratorState.COMPLETED
            else:
                self._state = OrchestratorState.EXEC_FAILED

            logger.info(f"🔥 ORCHESTRATOR: Plate execution finished. Results: {execution_results}")

            return execution_results
        except Exception as e:
            self._state = OrchestratorState.EXEC_FAILED
            logger.error(f"Failed to execute compiled plate: {e}")
            raise

    def get_component_keys(self, component: Union['AllComponents', 'VariableComponents'], component_filter: Optional[List[Union[str, int]]] = None) -> List[str]:
        """
        Generic method to get component keys using VariableComponents directly.

        Returns the discovered component values as strings to match the pattern
        detection system format.

        Tries metadata cache first, falls back to filename parsing cache if metadata is empty.

        Args:
            component: AllComponents or VariableComponents enum specifying which component to extract
                      (also accepts GroupBy enum which will be converted to AllComponents)
            component_filter: Optional list of component values to filter by

        Returns:
            List of component values as strings, sorted

        Raises:
            RuntimeError: If orchestrator is not initialized
        """
        if not self.is_initialized():
            raise RuntimeError("Orchestrator must be initialized before getting component keys.")

        # Convert GroupBy to AllComponents using OpenHCS generic utility
        if isinstance(component, GroupBy) and component.value is None:
            raise ValueError("Cannot get component keys for GroupBy.NONE")

        # Convert to AllComponents for cache lookup (includes multiprocessing axis)
        component = convert_enum_by_value(component, AllComponents) or component

        # Use component directly - let natural errors occur for wrong types
        component_name = component.value

        # Try metadata cache first (preferred source)
        cached_metadata = self._metadata_cache_service.get_cached_metadata(component)
        if cached_metadata:
            all_components = list(cached_metadata.keys())
            logger.debug(f"Using metadata cache for {component_name}: {len(all_components)} components")
        else:
            # Fall back to filename parsing cache
            all_components = self._component_keys_cache[component]  # Let KeyError bubble up naturally

            if not all_components:
                logger.warning(f"No {component_name} values found in input directory: {self.input_dir}")
                return []

            logger.debug(f"Using filename parsing cache for {component.value}: {len(all_components)} components")

        if component_filter:
            str_component_filter = {str(c) for c in component_filter}
            selected_components = [comp for comp in all_components if comp in str_component_filter]
            if not selected_components:
                component_name = group_by.value
                logger.warning(f"No {component_name} values from {all_components} match the filter: {component_filter}")
            return selected_components
        else:
            return all_components

    def cache_component_keys(self, components: Optional[List['AllComponents']] = None) -> None:
        """
        Pre-compute and cache component keys for fast access using single-pass parsing.

        This method performs expensive file listing and parsing operations once,
        extracting all component types in a single pass for maximum efficiency.

        Args:
            components: Optional list of AllComponents to cache.
                       If None, caches all components in the AllComponents enum.
        """
        if not self.is_initialized():
            raise RuntimeError("Orchestrator must be initialized before caching component keys.")

        if components is None:
            components = list(AllComponents)  # Cache all enum values including multiprocessing axis

        logger.info(f"Caching component keys for: {[comp.value for comp in components]}")

        # Initialize component sets for all requested components
        component_sets: Dict['AllComponents', Set[Union[str, int]]] = {}
        for component in components:
            component_sets[component] = set()

        # Single pass through all filenames - extract all components at once
        try:
            filenames = self.filemanager.list_files(str(self.input_dir), Backend.DISK.value, extensions=DEFAULT_IMAGE_EXTENSIONS)
            logger.debug(f"Parsing {len(filenames)} filenames in single pass...")

            for filename in filenames:
                parsed_info = self.microscope_handler.parser.parse_filename(str(filename))
                if parsed_info:
                    # Extract all requested components from this filename
                    for component in component_sets:
                        component_name = component.value
                        if component_name in parsed_info and parsed_info[component_name] is not None:
                            component_sets[component].add(parsed_info[component_name])
                else:
                    logger.warning(f"Could not parse filename: {filename}")

        except Exception as e:
            logger.error(f"Error listing files or parsing filenames from {self.input_dir}: {e}", exc_info=True)
            # Initialize empty sets for failed parsing
            for component in component_sets:
                component_sets[component] = set()

        # Convert sets to sorted lists and store in cache
        for component, component_set in component_sets.items():
            sorted_components = [str(comp) for comp in sorted(list(component_set))]
            self._component_keys_cache[component] = sorted_components
            logger.debug(f"Cached {len(sorted_components)} {component.value} keys")

            if not sorted_components:
                logger.warning(f"No {component.value} values found in input directory: {self.input_dir}")

        logger.info(f"Component key caching complete. Cached {len(component_sets)} component types in single pass.")

    def clear_component_cache(self, components: Optional[List['AllComponents']] = None) -> None:
        """
        Clear cached component keys to force recomputation.

        Use this when the input directory contents have changed and you need
        to refresh the component key cache.

        Args:
            components: Optional list of AllComponents to clear from cache.
                       If None, clears entire cache.
        """
        if components is None:
            self._component_keys_cache.clear()
            logger.info("Cleared entire component keys cache")
        else:
            for component in components:
                if component in self._component_keys_cache:
                    del self._component_keys_cache[component]
                    logger.debug(f"Cleared cache for {component.value}")
            logger.info(f"Cleared cache for {len(components)} component types")

    @property
    def metadata_cache(self) -> MetadataCache:
        """Access to metadata cache service."""
        return self._metadata_cache_service



    # Global config management removed - handled by UI layer

    def apply_pipeline_config(self, pipeline_config: PipelineConfig) -> None:
        """
        Apply per-orchestrator configuration using thread-local storage.

        This method sets the orchestrator's effective config in thread-local storage
        for step-level lazy configurations to resolve against.
        """
        if not isinstance(pipeline_config, PipelineConfig):
            raise TypeError(f"Expected PipelineConfig, got {type(pipeline_config)}")

        self.pipeline_config = pipeline_config

        # Set up thread-local context for sibling inheritance
        # The existing lazy config system already handles sibling inheritance automatically
        # We just need to provide the pipeline config instance as the context
        from dataclasses import fields

        # Create a merged config that combines global defaults with pipeline overrides
        # This provides the context for the existing sibling inheritance system
        merged_config_values = {}

        for field in fields(GlobalPipelineConfig):
            try:
                # Get raw value from pipeline config
                raw_value = object.__getattribute__(pipeline_config, field.name)
                if raw_value is not None:
                    # Use the override value
                    merged_config_values[field.name] = raw_value
                else:
                    # Use global default for None values
                    merged_config_values[field.name] = getattr(self.global_config, field.name)
            except AttributeError:
                # Field doesn't exist in pipeline config, use global default
                merged_config_values[field.name] = getattr(self.global_config, field.name)

        # Create merged config for thread-local context
        # The existing sibling inheritance system will handle the rest automatically
        merged_config = GlobalPipelineConfig(**merged_config_values)
        set_current_global_config(GlobalPipelineConfig, merged_config)

        # CRITICAL FIX: Do NOT overwrite context with effective_config
        # The merged_config preserves None values needed for sibling inheritance
        # Overwriting with effective_config resolves None values to concrete values,
        # breaking the inheritance chain (materialization_defaults → path_planning)

        logger.info(f"Applied orchestrator config for plate: {self.plate_path}")

    def get_effective_config(self) -> GlobalPipelineConfig:
        """Get effective configuration for this orchestrator."""
        if self.pipeline_config:
            # Thread-local context should already be set up by apply_pipeline_config()
            # Don't override it here as it may contain merged config for sibling inheritance
            return self.pipeline_config.to_base_config()
        return self.global_config

    def clear_pipeline_config(self) -> None:
        """Clear per-orchestrator configuration."""
        # Reset thread-local storage to global config
        if self.pipeline_config is not None:
            set_current_global_config(GlobalPipelineConfig, self.global_config)

        self.pipeline_config = None
        logger.info(f"Cleared per-orchestrator config for plate: {self.plate_path}")

    def cleanup_pipeline_config(self) -> None:
        """Clean up orchestrator context when done (for backward compatibility)."""
        self.clear_pipeline_config()

    def __del__(self):
        """Ensure config cleanup on orchestrator destruction."""
        try:
            # Clear any stored configuration references
            self.clear_pipeline_config()
        except Exception:
            # Ignore errors during cleanup in destructor to prevent cascading failures
            pass
