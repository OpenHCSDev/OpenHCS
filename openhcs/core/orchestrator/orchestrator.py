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
from dataclasses import fields
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Union, Set

from openhcs.constants.constants import Backend, DEFAULT_IMAGE_EXTENSIONS, GroupBy, OrchestratorState, get_openhcs_config, AllComponents, VariableComponents
from openhcs.constants import Microscope
from openhcs.core.config import GlobalPipelineConfig
from openhcs.config_framework.global_config import get_current_global_config
from openhcs.config_framework.lazy_factory import ContextProvider


from openhcs.core.metadata_cache import get_metadata_cache, MetadataCache
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.components.validation import convert_enum_by_value
from openhcs.core.orchestrator.execution_result import ExecutionResult, ExecutionStatus
from openhcs.io.filemanager import FileManager
# Zarr backend is CPU-only; always import it (even in subprocess/no-GPU mode)
import os
from openhcs.io.zarr import ZarrStorageBackend
# PipelineConfig now imported directly above
from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization
from openhcs.microscopes import create_microscope_handler
from openhcs.microscopes.microscope_base import MicroscopeHandler

# Lazy import of consolidate_analysis_results to avoid blocking GUI startup
# This function imports GPU libraries, so we defer it until first use
def _get_consolidate_analysis_results():
    """Lazy import of consolidate_analysis_results function."""
    if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
        # Subprocess runner mode - create placeholder
        def consolidate_analysis_results(*args, **kwargs):
            """Placeholder for subprocess runner mode."""
            raise RuntimeError("Analysis consolidation not available in subprocess runner mode")
        return consolidate_analysis_results
    else:
        from openhcs.processing.backends.analysis.consolidate_analysis_results import consolidate_analysis_results
        return consolidate_analysis_results

# Import generic component system - required for orchestrator functionality

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
    from openhcs.core.memory.gpu_cleanup import cleanup_all_gpu_frameworks
except ImportError:
    cleanup_all_gpu_frameworks = None


logger = logging.getLogger(__name__)


def _merge_nested_dataclass(pipeline_value, global_value):
    """
    Recursively merge nested dataclass configs.

    For each field in the dataclass:
    - If pipeline value is not None, use it
    - Otherwise, use global value

    This ensures that None values in nested configs resolve to global config values.
    """
    from dataclasses import is_dataclass, fields as dataclass_fields

    if not is_dataclass(pipeline_value) or not is_dataclass(global_value):
        # Not dataclasses, return pipeline value as-is
        return pipeline_value

    # Both are dataclasses - merge field by field
    merged_values = {}
    for field in dataclass_fields(type(pipeline_value)):
        pipeline_field_value = getattr(pipeline_value, field.name)
        global_field_value = getattr(global_value, field.name)

        if pipeline_field_value is not None:
            # Pipeline has a value - check if it's a nested dataclass that needs merging
            if is_dataclass(pipeline_field_value) and is_dataclass(global_field_value):
                merged_values[field.name] = _merge_nested_dataclass(pipeline_field_value, global_field_value)
            else:
                merged_values[field.name] = pipeline_field_value
        else:
            # Pipeline value is None - use global value
            merged_values[field.name] = global_field_value

    # Create new instance with merged values
    return type(pipeline_value)(**merged_values)


def _create_merged_config(pipeline_config: 'PipelineConfig', global_config: GlobalPipelineConfig) -> GlobalPipelineConfig:
    """
    Pure function for creating merged config that preserves None values for sibling inheritance.

    Follows OpenHCS stateless architecture principles - no side effects, explicit dependencies.
    Extracted from apply_pipeline_config to eliminate code duplication.
    """
    logger.debug(f"Starting merge with pipeline_config={type(pipeline_config)} and global_config={type(global_config)}")

    merged_config_values = {}
    for field in fields(GlobalPipelineConfig):
        # CRITICAL: Access raw stored value from __dict__ to avoid lazy resolution fallback to MRO defaults
        # For lazy dataclasses, getattr() triggers resolution which falls back to GlobalPipelineConfig defaults
        # We need the actual None value to know if it should inherit from global config
        pipeline_value = pipeline_config.__dict__.get(field.name)

        if pipeline_value is not None:
            # CRITICAL FIX: For lazy configs, merge with global config BEFORE converting to base
            # This ensures None values in lazy configs resolve to global values
            # Then convert to base config to store in thread-local context
            if hasattr(pipeline_value, 'to_base_config'):
                # This is a lazy config - merge with global config first
                global_value = getattr(global_config, field.name)
                from dataclasses import is_dataclass
                if is_dataclass(global_value):
                    # Merge lazy config with global config to resolve None values
                    merged_lazy = _merge_nested_dataclass(pipeline_value, global_value)
                    # Now convert merged result to base config
                    converted_value = merged_lazy.to_base_config() if hasattr(merged_lazy, 'to_base_config') else merged_lazy
                    merged_config_values[field.name] = converted_value
                else:
                    # No global value to merge with, just convert to base
                    converted_value = pipeline_value.to_base_config()
                    merged_config_values[field.name] = converted_value
            else:
                # CRITICAL FIX: For base dataclass configs, merge nested fields
                # This ensures None values in nested configs resolve to global values
                global_value = getattr(global_config, field.name)
                from dataclasses import is_dataclass
                if is_dataclass(pipeline_value) and is_dataclass(global_value):
                    merged_config_values[field.name] = _merge_nested_dataclass(pipeline_value, global_value)
                else:
                    # Regular value - use as-is
                    merged_config_values[field.name] = pipeline_value
        else:
            global_value = getattr(global_config, field.name)
            merged_config_values[field.name] = global_value

    result = GlobalPipelineConfig(**merged_config_values)
    return result


def _execute_axis_with_sequential_combinations(
    pipeline_definition: List[AbstractStep],
    axis_contexts: List[tuple],  # List of (context_key, frozen_context) tuples
    visualizer: Optional['NapariVisualizerType']
) -> ExecutionResult:
    """
    Execute all sequential combinations for a single axis in order.

    This function runs in a worker process and handles VFS clearing between combinations.
    Multiple axes can run in parallel, but combinations within an axis are sequential.

    Args:
        pipeline_definition: List of pipeline steps to execute
        axis_contexts: List of (context_key, frozen_context) tuples for this axis
        visualizer: Optional Napari visualizer (not used in multiprocessing)

    Returns:
        ExecutionResult with status for the entire axis (all combinations)
    """
    # Precondition: axis_contexts must not be empty
    if not axis_contexts:
        raise ValueError("axis_contexts cannot be empty - this indicates a bug in the caller")

    # Extract axis_id from first context
    first_context_key, first_context = axis_contexts[0]
    axis_id = first_context.axis_id

    logger.info(f"🔄 WORKER: Processing {len(axis_contexts)} combination(s) for axis {axis_id}")

    for combo_idx, (context_key, frozen_context) in enumerate(axis_contexts):
        logger.info(f"🔄 WORKER: Processing combination {combo_idx + 1}/{len(axis_contexts)}: {context_key}")

        # Execute this combination
        result = _execute_single_axis_static(pipeline_definition, frozen_context, visualizer)

        # Check if this combination failed
        if not result.is_success():
            logger.error(f"🔄 WORKER: Combination {context_key} failed for axis {axis_id}")
            return ExecutionResult.error(
                axis_id=axis_id,
                failed_combination=context_key,
                error_message=result.error_message
            )

        # Clear VFS after each combination to prevent memory accumulation
        # This is critical when worker processes handle multiple wells sequentially
        from openhcs.io.base import reset_memory_backend
        from openhcs.core.memory.gpu_cleanup import cleanup_all_gpu_frameworks

        logger.info(f"🔄 WORKER: Clearing VFS after combination {combo_idx + 1}/{len(axis_contexts)}")
        reset_memory_backend()
        if cleanup_all_gpu_frameworks:
            cleanup_all_gpu_frameworks()

    logger.info(f"🔄 WORKER: Completed all {len(axis_contexts)} combination(s) for axis {axis_id}")
    return ExecutionResult.success(axis_id=axis_id)


def _execute_single_axis_static(
    pipeline_definition: List[AbstractStep],
    frozen_context: 'ProcessingContext',
    visualizer: Optional['NapariVisualizerType']
) -> ExecutionResult:
    """
    Static version of _execute_single_axis for multiprocessing compatibility.

    This function is identical to PipelineOrchestrator._execute_single_axis but doesn't
    require an orchestrator instance, making it safe for pickling in ProcessPoolExecutor.

    Args:
        pipeline_definition: List of pipeline steps to execute
        frozen_context: Frozen processing context for this axis
        visualizer: Optional Napari visualizer (not used in multiprocessing)

    Returns:
        ExecutionResult with status for this axis
    """
    axis_id = frozen_context.axis_id

    # NUCLEAR VALIDATION
    if not frozen_context.is_frozen():
        error_msg = f"Context for axis {axis_id} is not frozen before execution"
        logger.error(error_msg)
        raise RuntimeError(error_msg)

    if not pipeline_definition:
        error_msg = f"Empty pipeline_definition for axis {axis_id}"
        logger.error(error_msg)
        raise RuntimeError(error_msg)

    # Execute each step in the pipeline
    for step_index, step in enumerate(pipeline_definition):
        step_name = frozen_context.step_plans[step_index]["step_name"]

        # Verify step has process method (should always be true for AbstractStep subclasses)
        # This check is acceptable because AbstractStep is an abstract base class
        if not hasattr(step, 'process'):
            error_msg = f"Step {step_index+1} missing process method for axis {axis_id}"
            logger.error(error_msg)
            raise RuntimeError(error_msg)

        # Call process method on step instance
        step.process(frozen_context, step_index)

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
    return ExecutionResult.success(axis_id=axis_id)


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


def _configure_worker_with_gpu(log_file_base: str, global_config_dict: dict):
    """
    Configure logging, function registry, and GPU registry for worker process.

    This function is called once per worker process when it starts.
    It sets up logging, function registry, and GPU registry initialization.

    Args:
        log_file_base: Base path for worker log files (empty string if no logging)
        global_config_dict: Serialized global configuration for GPU registry setup
    """
    import logging
    import os

    # Workers should be allowed to import GPU libs if available.
    # The parent subprocess runner may set OPENHCS_SUBPROCESS_NO_GPU=1 to stay lean,
    # but that flag must not leak into worker processes.
    os.environ.pop('OPENHCS_SUBPROCESS_NO_GPU', None)

    # Configure logging only if log_file_base is provided
    if log_file_base:
        _configure_worker_logging(log_file_base)
        worker_logger = logging.getLogger("openhcs.worker")
    else:
        # Set up basic logging for worker messages
        logging.basicConfig(level=logging.INFO)
        worker_logger = logging.getLogger("openhcs.worker")

    # Initialize function registry for this worker process
    try:
        # Import and initialize function registry (will auto-discover all libraries)
        import openhcs.processing.func_registry as func_registry_module

        # Force initialization if not already done (workers need full registry)
        with func_registry_module._registry_lock:
            if not func_registry_module._registry_initialized:
                func_registry_module._auto_initialize_registry()

    except Exception as e:
        # Don't raise - let worker continue, registry will auto-init on first function call
        pass

    # Initialize GPU registry for this worker process
    try:
        # Reconstruct global config from dict
        from openhcs.core.config import GlobalPipelineConfig
        global_config = GlobalPipelineConfig(**global_config_dict)

        # Initialize GPU registry for this worker
        from openhcs.core.orchestrator.gpu_scheduler import setup_global_gpu_registry
        setup_global_gpu_registry(global_config)

    except Exception as e:
        # Don't raise - let worker continue without GPU if needed
        pass


# Global variable to store log file base for worker processes
_worker_log_file_base = None





class PipelineOrchestrator(ContextProvider):
    """
    Updated orchestrator supporting both global and per-orchestrator configuration.

    Global configuration: Updates all orchestrators (existing behavior)
    Per-orchestrator configuration: Affects only this orchestrator instance

    The orchestrator first compiles the pipeline for all specified axis values,
    creating frozen, immutable ProcessingContexts using `compile_plate_for_processing()`.
    Then, it executes the (now stateless) pipeline definition against these contexts,
    potentially in parallel, using `execute_compiled_plate()`.
    """
    _context_type = "orchestrator"  # Register as orchestrator context provider

    def __init__(
        self,
        plate_path: Union[str, Path],
        workspace_path: Optional[Union[str, Path]] = None,
        *,
        pipeline_config: Optional['PipelineConfig'] = None,
        storage_registry: Optional[Any] = None,
        progress_callback: Optional[Callable[[str, str, str, Dict[str, Any]], None]] = None,
    ):
        # Lock removed - was orphaned code never used

        # Validate shared global context exists
        if get_current_global_config(GlobalPipelineConfig) is None:
            raise RuntimeError(
                "No global configuration context found. "
                "Ensure application startup has called ensure_global_config_context()."
            )

        # Track executor for cancellation support
        self._executor = None

        # Initialize auto-sync control for pipeline config
        self._pipeline_config = None
        self._auto_sync_enabled = True

        # Context management now handled by contextvars-based system

        # Initialize per-orchestrator configuration
        # DUAL-AXIS FIX: Always create a PipelineConfig instance to make orchestrator detectable as context provider
        # This ensures the orchestrator has a dataclass attribute for stack introspection
        # PipelineConfig is already the lazy version of GlobalPipelineConfig
        from openhcs.core.config import PipelineConfig
        if pipeline_config is None:
            # CRITICAL FIX: Create pipeline config that inherits from global config
            # This ensures the orchestrator's pipeline_config has the global values for resolution
            pipeline_config = PipelineConfig()

        # CRITICAL FIX: Do NOT apply global config inheritance during initialization
        # PipelineConfig should always have None values that resolve through lazy resolution
        # Copying concrete values breaks the placeholder system and makes all fields appear "explicitly set"

        self.pipeline_config = pipeline_config

        # CRITICAL FIX: Expose pipeline config as public attribute for dual-axis resolver discovery
        # The resolver's _is_context_provider method only finds public attributes (skips _private)
        # This allows the resolver to discover the orchestrator's pipeline config during context resolution
        self.pipeline_config = pipeline_config
        logger.info("PipelineOrchestrator initialized with PipelineConfig for context discovery.")

        # REMOVED: Unnecessary thread-local modification
        # The orchestrator should not modify thread-local storage during initialization
        # Global config is already available through the dual-axis resolver fallback

        # Convert to Path and validate
        if plate_path:
            plate_path = Path(plate_path)

            # Validate filesystem paths (skip for OMERO virtual paths)
            if not str(plate_path).startswith("/omero/"):
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
            # Use the global registry directly (don't copy) so that reset_memory_backend() works correctly
            # The global registry is a singleton, and VFS clearing needs to clear the same instance
            from openhcs.io.base import storage_registry as global_storage_registry, ensure_storage_registry
            # Ensure registry is initialized
            ensure_storage_registry()
            self.registry = global_storage_registry
            logger.info("PipelineOrchestrator using global StorageRegistry instance.")

        # Override zarr backend with orchestrator's config
        shared_context = get_current_global_config(GlobalPipelineConfig)
        zarr_backend_with_config = ZarrStorageBackend(shared_context.zarr_config)
        self.registry[Backend.ZARR.value] = zarr_backend_with_config
        logger.info(f"Orchestrator zarr backend configured with {shared_context.zarr_config.compressor.value} compression")

        # Orchestrator always creates its own FileManager, using the determined registry
        self.filemanager = FileManager(self.registry)
        self.input_dir: Optional[Path] = None
        self.microscope_handler: Optional[MicroscopeHandler] = None
        self.default_pipeline_definition: Optional[List[AbstractStep]] = None
        self._initialized: bool = False
        self._state: OrchestratorState = OrchestratorState.CREATED

        # Progress callback for real-time execution updates
        self.progress_callback = progress_callback
        if progress_callback:
            logger.info("PipelineOrchestrator initialized with progress callback")

        # Component keys cache for fast access - uses AllComponents (includes multiprocessing axis)
        self._component_keys_cache: Dict['AllComponents', List[str]] = {}

        # Metadata cache service - per-orchestrator instance (not global singleton)
        from openhcs.core.metadata_cache import MetadataCache
        self._metadata_cache_service = MetadataCache()

        # Viewer management - shared between pipeline execution and image browser
        self._visualizers = {}  # Dict[(backend_name, port)] -> visualizer instance


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

    def get_or_create_visualizer(self, config, vis_config=None):
        """
        Get existing visualizer or create a new one for the given config.

        This method is shared between pipeline execution and image browser to avoid
        duplicating viewer instances. Viewers are tracked by (backend_name, port) key.

        Args:
            config: Streaming config (any StreamingConfig subclass)
            vis_config: Optional visualizer config (can be None for image browser)

        Returns:
            Visualizer instance
        """
        from openhcs.core.config import StreamingConfig

        # Generic streaming config handling using polymorphic attributes
        if isinstance(config, StreamingConfig):
            # Start global ack listener (must be before viewers connect)
            from openhcs.runtime.zmq_base import start_global_ack_listener
            start_global_ack_listener(config.transport_mode)

            # Pre-create queue tracker using polymorphic attributes
            from openhcs.runtime.queue_tracker import GlobalQueueTrackerRegistry
            registry = GlobalQueueTrackerRegistry()
            registry.get_or_create_tracker(config.port, config.viewer_type)
            logger.info(f"🔬 ORCHESTRATOR: Pre-created queue tracker for {config.viewer_type} on port {config.port}")

            key = (config.viewer_type, config.port)
        else:
            backend_name = config.backend.name if hasattr(config, 'backend') else 'unknown'
            key = (backend_name,)

        # Check if we already have a visualizer for this key
        if key in self._visualizers:
            vis = self._visualizers[key]
            if vis.is_running:
                return vis
            else:
                del self._visualizers[key]

        # Create new visualizer using polymorphic create_visualizer method
        vis = config.create_visualizer(self.filemanager, vis_config)

        # Start viewer asynchronously for streaming configs
        if isinstance(config, StreamingConfig):
            vis.start_viewer(async_mode=True)

            # Ping server to set ready state (background thread to avoid blocking)
            import threading
            def ping_server():
                import time
                time.sleep(1.0)  # Give server time to start
                if hasattr(vis, '_wait_for_server_ready'):
                    vis._wait_for_server_ready(timeout=10.0)

            thread = threading.Thread(target=ping_server, daemon=True)
            thread.start()
        else:
            vis.start_viewer()

        # Store in cache
        self._visualizers[key] = vis

        return vis

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
            shared_context = get_current_global_config(GlobalPipelineConfig)
            microscope_type = shared_context.microscope.value if shared_context.microscope != Microscope.AUTO else 'auto'
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
        logger.info(f"🔥 INIT: initialize() called for plate: {self.plate_path}")
        if self._initialized:
            logger.info("Orchestrator already initialized.")
            return self

        try:
            logger.info(f"🔥 INIT: About to call initialize_microscope_handler()")
            self.initialize_microscope_handler()

            # Delegate workspace initialization to microscope handler
            logger.info("Initializing workspace with microscope handler...")
            actual_image_dir = self.microscope_handler.initialize_workspace(
                self.plate_path, self.filemanager
            )

            # Use the actual image directory returned by the microscope handler
            # All handlers now return Path (including OMERO with virtual paths)
            self.input_dir = Path(actual_image_dir)
            logger.info(f"Set input directory to: {self.input_dir}")

            # Set workspace_path based on what the handler returned
            if actual_image_dir != self.plate_path:
                # Handler created a workspace (or virtual path for OMERO)
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

            # Ensure complete OpenHCS metadata exists
            self._ensure_openhcs_metadata()

            logger.info("PipelineOrchestrator fully initialized with cached component keys and metadata.")
            return self
        except Exception as e:
            self._state = OrchestratorState.INIT_FAILED
            logger.error(f"Failed to initialize orchestrator: {e}")
            raise

    def is_initialized(self) -> bool:
        return self._initialized

    def _ensure_openhcs_metadata(self) -> None:
        """Ensure complete OpenHCS metadata exists for the plate.

        Uses the same context creation logic as pipeline execution to get full metadata
        with channel names from metadata files (HTD, Index.xml, etc).

        Skips OMERO and other non-disk-based microscope handlers since they don't have
        real disk directories.
        """
        from openhcs.microscopes.openhcs import OpenHCSMetadataGenerator

        # Skip metadata creation for OMERO and other non-disk-based handlers
        # OMERO uses virtual paths like /omero/plate_1 which are not real directories
        if self.microscope_handler.microscope_type == 'omero':
            logger.debug("Skipping metadata creation for OMERO plate (uses virtual paths)")
            return

        # For plates with virtual workspace, metadata is already created by _build_virtual_mapping()
        # We just need to add the component metadata to the existing "." subdirectory
        from openhcs.io.metadata_writer import get_subdirectory_name
        subdir_name = get_subdirectory_name(self.input_dir, self.plate_path)

        # Create context using SAME logic as create_context() to get full metadata
        context = self.create_context(axis_id="metadata_init")

        # Create metadata (will skip if already complete)
        generator = OpenHCSMetadataGenerator(self.filemanager)
        generator.create_metadata(
            context,
            str(self.input_dir),
            "disk",
            is_main=True,
            plate_root=str(self.plate_path),
            sub_dir=subdir_name,
            skip_if_complete=True
        )

    def get_results_path(self) -> Path:
        """Get the results directory path for this orchestrator's plate.

        Uses the same logic as PathPlanner._get_results_path() to ensure consistency.
        This is the single source of truth for where results are stored.

        Returns:
            Path to results directory (absolute or relative to output plate root)
        """
        from openhcs.core.pipeline.path_planner import PipelinePathPlanner

        # Get materialization_results_path from global config
        materialization_path = self.global_config.materialization_results_path

        # If absolute, use as-is
        if Path(materialization_path).is_absolute():
            return Path(materialization_path)

        # If relative, resolve relative to output plate root
        # Use path_planning_config from global config
        path_config = self.global_config.path_planning_config
        output_plate_root = PipelinePathPlanner.build_output_plate_root(
            self.plate_path,
            path_config,
            is_per_step_materialization=False
        )

        return output_plate_root / materialization_path

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

        # CRITICAL: Pass metadata cache for OpenHCS metadata creation
        # Extract cached metadata from service and convert to dict format expected by OpenHCSMetadataGenerator
        metadata_dict = {}
        for component in AllComponents:
            cached_metadata = self._metadata_cache_service.get_cached_metadata(component)
            if cached_metadata:
                metadata_dict[component] = cached_metadata
        context.metadata_cache = metadata_dict

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

        # Send progress: axis started
        if self.progress_callback:
            try:
                self.progress_callback(axis_id, 'pipeline', 'started', {
                    'total_steps': len(pipeline_definition)
                })
            except Exception as e:
                logger.warning(f"Progress_callback failed for axis {axis_id} start: {e}")

        # NUCLEAR VALIDATION
        if not frozen_context.is_frozen():
            error_msg = f"🔥 SINGLE_AXIS ERROR: Context for axis {axis_id} is not frozen before execution"
            logger.error(error_msg)
            raise RuntimeError(error_msg)

        if not pipeline_definition:
            error_msg = f"🔥 SINGLE_AXIS ERROR: Empty pipeline_definition for axis {axis_id}"
            logger.error(error_msg)
            raise RuntimeError(error_msg)

        # Debug: Log sequential mode status
        logger.info(f"🔍 DISPATCH: axis={axis_id}, pipeline_sequential_mode={frozen_context.pipeline_sequential_mode}, "
                   f"combinations={frozen_context.pipeline_sequential_combinations}")

        # All execution goes through step-sequential now
        # Sequential combinations are handled by compiling separate contexts
        return self._execute_step_sequential(pipeline_definition, frozen_context, visualizer)

    def _execute_step_sequential(
        self,
        pipeline_definition: List[AbstractStep],
        frozen_context: ProcessingContext,
        visualizer: Optional[NapariVisualizerType]
    ) -> Dict[str, Any]:
        """Execute pipeline with step-wide sequential processing (current behavior)."""
        axis_id = frozen_context.axis_id
        logger.info(f"🔥 SINGLE_AXIS: Processing {len(pipeline_definition)} steps for axis {axis_id} (step-wide sequential)")

        for step_index, step in enumerate(pipeline_definition):
            step_name = frozen_context.step_plans[step_index]["step_name"]
            logger.info(f"🔥 SINGLE_AXIS: Executing step {step_index+1}/{len(pipeline_definition)} - {step_name} for axis {axis_id}")

            # Send progress: step started
            if self.progress_callback:
                try:
                    self.progress_callback(axis_id, step_name, 'started', {
                        'step_index': step_index,
                        'total_steps': len(pipeline_definition)
                    })
                except Exception as e:
                    logger.warning(f"Progress callback failed for axis {axis_id} step {step_name} start: {e}")

            # Verify step has process method
            if not hasattr(step, 'process'):
                error_msg = f"🔥 SINGLE_AXIS ERROR: Step {step_index+1} missing process method for axis {axis_id}"
                logger.error(error_msg)
                raise RuntimeError(error_msg)

            # Call process method on step instance
            step.process(frozen_context, step_index)
            logger.info(f"🔥 SINGLE_AXIS: Step {step_index+1}/{len(pipeline_definition)} - {step_name} completed for axis {axis_id}")

            # Send progress: step completed
            if self.progress_callback:
                try:
                    self.progress_callback(axis_id, step_name, 'completed', {
                        'step_index': step_index,
                        'total_steps': len(pipeline_definition)
                    })
                except Exception as e:
                    logger.warning(f"Progress callback failed for axis {axis_id} step {step_name} completion: {e}")

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

        # Send progress: axis completed
        if self.progress_callback:
            try:
                self.progress_callback(axis_id, 'pipeline', 'completed', {
                    'total_steps': len(pipeline_definition)
                })
            except Exception as e:
                logger.warning(f"Progress callback failed for axis {axis_id} completion: {e}")

        return {"status": "success", "axis_id": axis_id}

    def _execute_pipeline_sequential(
        self,
        pipeline_definition: List[AbstractStep],
        frozen_context: ProcessingContext,
        visualizer: Optional[NapariVisualizerType]
    ) -> Dict[str, Any]:
        """Execute pipeline with pipeline-wide sequential processing.

        Combinations are precomputed at compile time and stored in context.pipeline_sequential_combinations.
        Loop: combinations → steps (process one combo through all steps before moving to next).
        VFS is cleared between combinations to prevent memory accumulation.
        """
        axis_id = frozen_context.axis_id

        # Combinations were precomputed at compile time
        combinations = frozen_context.pipeline_sequential_combinations or []

        if not combinations:
            logger.warning(f"Pipeline sequential mode enabled but no combinations found for axis {axis_id}")
            # Fallback to normal execution
            for step_index, step in enumerate(pipeline_definition):
                step.process(frozen_context, step_index)
        else:
            logger.info(f"🔄 PIPELINE_SEQUENTIAL: {len(combinations)} combinations for axis {axis_id}")

            # Loop: combinations → steps
            for combo_idx, combo in enumerate(combinations):
                frozen_context.current_sequential_combination = combo
                logger.info(f"🔄 ORCHESTRATOR: Set current_sequential_combination = {combo}")
                logger.info(f"🔄 ORCHESTRATOR: Verify frozen_context.current_sequential_combination = {frozen_context.current_sequential_combination}")
                logger.info(f"🔄 Processing combination {combo_idx + 1}/{len(combinations)}: {combo}")

                # Process all steps for this combination
                for step_index, step in enumerate(pipeline_definition):
                    step.process(frozen_context, step_index)

                # Clear VFS after each combination to prevent memory accumulation
                try:
                    from openhcs.io.base import reset_memory_backend
                    from openhcs.core.memory.gpu_cleanup import cleanup_all_gpu_frameworks

                    logger.info(f"🔄 SEQUENTIAL: Clearing VFS after combination {combo}")
                    reset_memory_backend()
                    cleanup_all_gpu_frameworks()
                    logger.info(f"🔄 SEQUENTIAL: VFS cleared, ready for next combination")
                except Exception as e:
                    logger.warning(f"Failed to clear VFS after combination {combo}: {e}")

        frozen_context.current_sequential_combination = None

        if self.progress_callback:
            try:
                self.progress_callback(axis_id, 'pipeline', 'completed', {'total_steps': len(pipeline_definition)})
            except Exception as e:
                logger.warning(f"Progress callback failed: {e}")

        return {"status": "success", "axis_id": axis_id}

    def cancel_execution(self):
        """
        Cancel ongoing execution by shutting down the executor.

        This gracefully cancels pending futures and shuts down worker processes
        without killing all child processes (preserving Napari viewers, etc.).
        """
        if self._executor:
            try:
                logger.info("🔥 ORCHESTRATOR: Cancelling execution - shutting down executor")
                self._executor.shutdown(wait=False, cancel_futures=True)
                logger.info("🔥 ORCHESTRATOR: Executor shutdown initiated")
            except Exception as e:
                logger.warning(f"🔥 ORCHESTRATOR: Failed to cancel executor: {e}")

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

        # CRITICAL FIX: Use resolved pipeline definition from compilation if available
        # For subprocess runner, use the parameter directly since it receives pre-compiled contexts
        resolved_pipeline = getattr(self, '_resolved_pipeline_definition', None)
        if resolved_pipeline is not None:
            logger.info(f"🔥 EXECUTION: Using resolved pipeline definition with {len(resolved_pipeline)} steps (from compilation)")
            pipeline_definition = resolved_pipeline
        else:
            logger.info(f"🔥 EXECUTION: Using parameter pipeline definition with {len(pipeline_definition)} steps (subprocess mode)")
            # In subprocess mode, the pipeline_definition parameter should already be resolved
        if not self.is_initialized():
             raise RuntimeError("Orchestrator must be initialized before executing.")
        if not pipeline_definition:
            raise ValueError("A valid (stateless) pipeline definition must be provided.")
        if not compiled_contexts:
            logger.warning("No compiled contexts provided for execution.")
            return {}
        
        # Access num_workers from effective config (merged pipeline + global config)
        actual_max_workers = max_workers or self.get_effective_config().num_workers
        if actual_max_workers <= 0: # Ensure positive number of workers
            actual_max_workers = 1

        # 🔬 AUTOMATIC VISUALIZER CREATION: Create visualizers if compiler detected streaming
        visualizers = []
        if visualizer is None:
            from openhcs.core.config import StreamingConfig

            # Collect unique configs (deduplicate by viewer_type + port)
            unique_configs = {}
            for ctx in compiled_contexts.values():
                for visualizer_info in ctx.required_visualizers:
                    config = visualizer_info['config']
                    key = (config.viewer_type, config.port) if isinstance(config, StreamingConfig) else (config.backend.name,)
                    if key not in unique_configs:
                        unique_configs[key] = (config, ctx.visualizer_config)

            # Create visualizers
            for config, vis_config in unique_configs.values():
                visualizers.append(self.get_or_create_visualizer(config, vis_config))

            # Wait for all streaming viewers to be ready before starting pipeline
            # This ensures viewers are available to receive images
            if visualizers:
                logger.info(f"🔬 ORCHESTRATOR: Waiting for {len(visualizers)} streaming viewer(s) to be ready...")
                import time
                max_wait = 30.0  # Maximum wait time in seconds
                start_time = time.time()

                while time.time() - start_time < max_wait:
                    all_ready = all(v.is_running for v in visualizers)
                    if all_ready:
                        logger.info("🔬 ORCHESTRATOR: All streaming viewers are ready!")
                        break
                    time.sleep(0.2)  # Check every 200ms
                else:
                    # Timeout - log which viewers aren't ready (use generic port attribute)
                    not_ready = [v.port for v in visualizers if not v.is_running]
                    logger.warning(f"🔬 ORCHESTRATOR: Timeout waiting for streaming viewers. Not ready: {not_ready}")

                # Clear viewer state for new pipeline run to prevent accumulation
                logger.info("🔬 ORCHESTRATOR: Clearing streaming viewer state for new pipeline run...")
                for vis in visualizers:
                    if hasattr(vis, 'clear_viewer_state'):
                        success = vis.clear_viewer_state()
                        if success:
                            logger.info(f"🔬 ORCHESTRATOR: Cleared state for viewer on port {vis.port}")
                        else:
                            logger.warning(f"🔬 ORCHESTRATOR: Failed to clear state for viewer on port {vis.port}")

            # For backwards compatibility, set visualizer to the first one
            visualizer = visualizers[0] if visualizers else None

        self._state = OrchestratorState.EXECUTING
        logger.info(f"Starting execution for {len(compiled_contexts)} axis values with max_workers={actual_max_workers}.")

        try:
            execution_results: Dict[str, ExecutionResult] = {}

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
                # CRITICAL FIX: Use _configure_worker_with_gpu to ensure workers have function registry
                # Workers need the function registry to access decorated functions with memory types
                global_config = get_current_global_config(GlobalPipelineConfig)
                global_config_dict = global_config.__dict__ if global_config else {}

                if log_file_base:
                    logger.info("🔥 WORKER SETUP: Configuring worker processes with function registry and logging")
                    executor = concurrent.futures.ProcessPoolExecutor(
                        max_workers=actual_max_workers,
                        initializer=_configure_worker_with_gpu,
                        initargs=(log_file_base, global_config_dict)
                    )
                else:
                    logger.info("🔥 WORKER SETUP: Configuring worker processes with function registry (no logging)")
                    executor = concurrent.futures.ProcessPoolExecutor(
                        max_workers=actual_max_workers,
                        initializer=_configure_worker_with_gpu,
                        initargs=("", global_config_dict)  # Empty string for no logging
                    )

            logger.info(f"🔥 DEATH_MARKER: ENTERING_{executor_type.upper()}_CONTEXT")
            # Store executor for cancellation support
            self._executor = executor
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

                # Group contexts by axis to detect sequential combinations
                from collections import defaultdict
                contexts_by_axis = defaultdict(list)
                for context_key, context in contexts_snapshot.items():
                    # Extract axis_id from context_key (either "axis_id" or "axis_id__combo_N")
                    if "__combo_" in context_key:
                        axis_id = context_key.split("__combo_")[0]
                        contexts_by_axis[axis_id].append((context_key, context))
                    else:
                        contexts_by_axis[context_key].append((context_key, context))

                logger.info(f"🔄 ORCHESTRATOR: Processing {len(contexts_by_axis)} {axis_name}s with {len(contexts_snapshot)} total contexts")

                # Submit one task per axis (each task handles its own sequential combinations)
                for axis_id, axis_contexts in contexts_by_axis.items():
                    logger.info(f"🔄 ORCHESTRATOR: Axis {axis_id} has {len(axis_contexts)} context(s)")

                    try:
                        # Resolve all contexts for this axis
                        resolved_axis_contexts = [
                            (context_key, resolve_lazy_configurations_for_serialization(context))
                            for context_key, context in axis_contexts
                        ]

                        logger.info(f"🔥 DEATH_MARKER: SUBMITTING_TASK_FOR_{axis_name.upper()}_{axis_id}")
                        logger.info(f"🔥 ORCHESTRATOR: Submitting task for {axis_name} {axis_id} with {len(resolved_axis_contexts)} combination(s)")

                        # Submit task that will handle all combinations for this axis sequentially
                        future = executor.submit(
                            _execute_axis_with_sequential_combinations,
                            pipeline_definition,
                            resolved_axis_contexts,
                            None  # visualizer
                        )
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

                # Explicitly shutdown executor INSIDE the with block to avoid hang on context exit
                logger.info("🔥 ORCHESTRATOR: Explicitly shutting down executor")
                executor.shutdown(wait=True, cancel_futures=False)
                logger.info("🔥 ORCHESTRATOR: Executor shutdown complete")

            # Determine if we're using multiprocessing (ProcessPoolExecutor) or threading
            effective_config = self.get_effective_config()
            use_multiprocessing = not effective_config.use_threading
            logger.info(f"🔥 ORCHESTRATOR: About to start GPU cleanup (use_multiprocessing={use_multiprocessing})")

            # 🔥 GPU CLEANUP: Skip in multiprocessing mode - workers handle their own cleanup
            # In multiprocessing mode, GPU cleanup in the main process can hang because
            # GPU contexts are owned by worker processes, not the orchestrator process
            try:
                if cleanup_all_gpu_frameworks and not use_multiprocessing:
                    logger.info("🔥 ORCHESTRATOR: Running GPU cleanup...")
                    cleanup_all_gpu_frameworks()
                    logger.info("🔥 GPU CLEANUP: Cleared all GPU frameworks after plate execution")
                elif use_multiprocessing:
                    logger.info("🔥 GPU CLEANUP: Skipped in multiprocessing mode (workers handle their own cleanup)")
            except Exception as cleanup_error:
                logger.warning(f"Failed to cleanup GPU memory after plate execution: {cleanup_error}")

            logger.info("🔥 ORCHESTRATOR: GPU cleanup section finished")

            logger.info("🔥 ORCHESTRATOR: Plate execution completed, checking for analysis consolidation")
            # Run automatic analysis consolidation if enabled
            shared_context = get_current_global_config(GlobalPipelineConfig)
            logger.info(f"🔥 ORCHESTRATOR: Analysis consolidation enabled={shared_context.analysis_consolidation_config.enabled}")
            if shared_context.analysis_consolidation_config.enabled:
                try:
                    logger.info("🔥 ORCHESTRATOR: Starting consolidation - finding results directory")
                    # Get results directory from compiled contexts (path planner already determined it)
                    results_dir = None
                    for axis_id, context in compiled_contexts.items():
                        # Check if context has step plans with special outputs
                        for step_plan in context.step_plans:
                            special_outputs = step_plan.get('special_outputs', {})
                            if special_outputs:
                                # Extract results directory from first special output path
                                first_output = next(iter(special_outputs.values()))
                                output_path = Path(first_output['path'])
                                potential_results_dir = output_path.parent

                                if potential_results_dir.exists():
                                    results_dir = potential_results_dir
                                    logger.info(f"🔍 CONSOLIDATION: Found results directory from special outputs: {results_dir}")
                                    break

                        if results_dir:
                            break

                    if results_dir and results_dir.exists():
                        logger.info(f"🔥 ORCHESTRATOR: Results directory exists: {results_dir}")
                        # Check if there are actually CSV files (materialized results)
                        logger.info("🔥 ORCHESTRATOR: Checking for CSV files...")
                        csv_files = list(results_dir.glob("*.csv"))
                        logger.info(f"🔥 ORCHESTRATOR: Found {len(csv_files)} CSV files")
                        if csv_files:
                            logger.info(f"🔄 CONSOLIDATION: Found {len(csv_files)} CSV files, running consolidation")
                            # Get well IDs from compiled contexts
                            axis_ids = list(compiled_contexts.keys())
                            logger.info(f"🔄 CONSOLIDATION: Using well IDs: {axis_ids}")

                            logger.info("🔥 ORCHESTRATOR: Calling consolidate_analysis_results()...")
                            consolidate_fn = _get_consolidate_analysis_results()
                            consolidate_fn(
                                results_directory=str(results_dir),
                                well_ids=axis_ids,
                                consolidation_config=shared_context.analysis_consolidation_config,
                                plate_metadata_config=shared_context.plate_metadata_config
                            )
                            logger.info("✅ CONSOLIDATION: Completed successfully")
                        else:
                            logger.info(f"⏭️ CONSOLIDATION: No CSV files found in {results_dir}, skipping")
                    else:
                        logger.info("⏭️ CONSOLIDATION: No results directory found in compiled contexts")
                except Exception as e:
                    logger.error(f"❌ CONSOLIDATION: Failed: {e}")
            else:
                logger.info("🔥 ORCHESTRATOR: Analysis consolidation disabled, skipping")

            # Update state based on execution results
            logger.info("🔥 ORCHESTRATOR: Updating orchestrator state based on execution results")
            if all(result.is_success() for result in execution_results.values()):
                self._state = OrchestratorState.COMPLETED
            else:
                self._state = OrchestratorState.EXEC_FAILED
            logger.info(f"🔥 ORCHESTRATOR: State updated to {self._state}")

            # 🔬 VISUALIZER CLEANUP: Stop all visualizers if they were auto-created and not persistent
            logger.info(f"🔬 ORCHESTRATOR: Starting visualizer cleanup for {len(visualizers)} visualizers")
            for idx, vis in enumerate(visualizers):
                try:
                    logger.info(f"🔬 ORCHESTRATOR: Processing visualizer {idx+1}/{len(visualizers)}, persistent={vis.persistent}")
                    if not vis.persistent:
                        logger.info(f"🔬 ORCHESTRATOR: Calling stop_viewer() for non-persistent visualizer {idx+1}")
                        vis.stop_viewer()
                        logger.info(f"🔬 ORCHESTRATOR: Stopped non-persistent visualizer {idx+1}")
                    else:
                        logger.info("🔬 ORCHESTRATOR: Keeping persistent visualizer alive (no cleanup needed)")
                        # Persistent visualizers stay alive across executions - no cleanup needed
                        # The ZMQ connection will be reused for the next execution
                except Exception as e:
                    logger.warning(f"🔬 ORCHESTRATOR: Failed to cleanup visualizer {idx+1}: {e}")
            logger.info("🔬 ORCHESTRATOR: Visualizer cleanup complete")

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
            # Use primary backend from microscope handler
            backend_to_use = self.microscope_handler.get_primary_backend(self.input_dir, self.filemanager)
            logger.debug(f"Using backend '{backend_to_use}' for file listing based on available backends")

            filenames = self.filemanager.list_files(str(self.input_dir), backend_to_use, extensions=DEFAULT_IMAGE_EXTENSIONS)
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

    @property
    def pipeline_config(self) -> Optional['PipelineConfig']:
        """Get current pipeline configuration."""
        return self._pipeline_config

    @pipeline_config.setter
    def pipeline_config(self, value: Optional['PipelineConfig']) -> None:
        """Set pipeline configuration with auto-sync to thread-local context."""
        self._pipeline_config = value
        # CRITICAL FIX: Also update public attribute for dual-axis resolver discovery
        # This ensures the resolver can always find the current pipeline config
        if hasattr(self, '__dict__'):  # Avoid issues during __init__
            self.__dict__['pipeline_config'] = value
        if self._auto_sync_enabled and value is not None:
            self._sync_to_thread_local()

    def _sync_to_thread_local(self) -> None:
        """Internal method to sync current pipeline_config to thread-local context."""
        if self._pipeline_config and hasattr(self, 'plate_path'):
            self.apply_pipeline_config(self._pipeline_config)

    def apply_pipeline_config(self, pipeline_config: 'PipelineConfig') -> None:
        """
        Apply per-orchestrator configuration using thread-local storage.

        This method sets the orchestrator's effective config in thread-local storage
        for step-level lazy configurations to resolve against.
        """
        # Import PipelineConfig at runtime for isinstance check
        from openhcs.core.config import PipelineConfig
        if not isinstance(pipeline_config, PipelineConfig):
            raise TypeError(f"Expected PipelineConfig, got {type(pipeline_config)}")

        # Temporarily disable auto-sync to prevent recursion
        self._auto_sync_enabled = False
        try:
            self._pipeline_config = pipeline_config
        finally:
            self._auto_sync_enabled = True

        # CRITICAL FIX: Do NOT contaminate thread-local context during PipelineConfig editing
        # The orchestrator should maintain its own internal context without modifying
        # the global thread-local context. This prevents reset operations from showing
        # orchestrator's saved values instead of original thread-local defaults.
        #
        # The merged config is computed internally and used by get_effective_config()
        # but should NOT be set as the global thread-local context.

        logger.info(f"Applied orchestrator config for plate: {self.plate_path}")

    def get_effective_config(self, *, for_serialization: bool = False) -> GlobalPipelineConfig:
        """
        Get effective configuration for this orchestrator.

        Args:
            for_serialization: If True, resolves all values for pickling/storage.
                              If False, preserves None values for sibling inheritance.
        """

        if for_serialization:
            result = self.pipeline_config.to_base_config()
            return result
        else:
            # Reuse existing merged config logic from apply_pipeline_config
            shared_context = get_current_global_config(GlobalPipelineConfig)
            if not shared_context:
                raise RuntimeError("No global configuration context available for merging")

            result = _create_merged_config(self.pipeline_config, shared_context)
            return result



    def clear_pipeline_config(self) -> None:
        """Clear per-orchestrator configuration."""
        # REMOVED: Thread-local modification - dual-axis resolver handles context automatically
        # No need to modify thread-local storage when clearing orchestrator config
        self.pipeline_config = None
        # Clear metadata cache for this orchestrator
        if hasattr(self, '_metadata_cache_service') and self._metadata_cache_service:
            self._metadata_cache_service.clear_cache()
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
