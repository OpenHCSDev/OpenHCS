"""
Pipeline module for OpenHCS.

This module provides the core pipeline compilation components for OpenHCS.
The PipelineCompiler is responsible for preparing step_plans within a ProcessingContext.

Doctrinal Clauses:
- Clause 12 — Absolute Clean Execution
- Clause 17 — VFS Exclusivity (FileManager is the only component that uses VirtualPath)
- Clause 17-B — Path Format Discipline
- Clause 66 — Immutability After Construction
- Clause 88 — No Inferred Capabilities
- Clause 101 — Memory Type Declaration
- Clause 245 — Path Declaration
- Clause 273 — Backend Authorization Doctrine
- Clause 281 — Context-Bound Identifiers
- Clause 293 — GPU Pre-Declaration Enforcement
- Clause 295 — GPU Scheduling Affinity
- Clause 504 — Pipeline Preparation Modifications
- Clause 524 — Step = Declaration = ID = Runtime Authority
"""

import inspect
import logging
import dataclasses
from pathlib import Path
from typing import Callable, Dict, List, Optional
from collections import OrderedDict # For special_outputs and special_inputs order (used by PathPlanner)

from openhcs.constants.constants import VALID_GPU_MEMORY_TYPES, READ_BACKEND, WRITE_BACKEND, Backend
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.config import MaterializationBackend, PathPlanningConfig, WellFilterMode
from openhcs.core.pipeline.funcstep_contract_validator import \
    FuncStepContractValidator
from openhcs.core.pipeline.materialization_flag_planner import \
    MaterializationFlagPlanner
from openhcs.core.pipeline.path_planner import PipelinePathPlanner
from openhcs.core.pipeline.gpu_memory_validator import \
    GPUMemoryTypeValidator
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.steps.function_step import FunctionStep # Used for isinstance check
from dataclasses import dataclass
logger = logging.getLogger(__name__)


@dataclass(frozen=True)
class FunctionReference:
    """
    A picklable reference to a function in the registry.

    This replaces raw function objects in compiled step definitions to ensure
    picklability while allowing workers to resolve functions from their registry.
    """
    function_name: str
    registry_name: str
    memory_type: str  # The memory type for get_function_by_name() (e.g., "numpy", "pyclesperanto")
    composite_key: str  # The full registry key (e.g., "pyclesperanto:gaussian_blur")

    def resolve(self) -> Callable:
        """Resolve this reference to the actual decorated function from registry."""
        if self.registry_name == "openhcs":
            # For OpenHCS functions, use RegistryService directly with composite key
            from openhcs.processing.backends.lib_registry.registry_service import RegistryService
            all_functions = RegistryService.get_all_functions_with_metadata()
            if self.composite_key in all_functions:
                return all_functions[self.composite_key].func
            else:
                raise RuntimeError(f"OpenHCS function {self.composite_key} not found in registry")
        else:
            # For external library functions, use the memory type for lookup
            from openhcs.processing.func_registry import get_function_by_name
            return get_function_by_name(self.function_name, self.memory_type)


def _refresh_function_objects_in_steps(pipeline_definition: List[AbstractStep]) -> None:
    """
    Refresh all function objects in pipeline steps to ensure they're picklable.

    This recreates function objects by importing them fresh from their original modules,
    similar to how code mode works, which avoids unpicklable closures from registry wrapping.
    """
    for step in pipeline_definition:
        if hasattr(step, 'func') and step.func is not None:
            step.func = _refresh_function_object(step.func)


def _refresh_function_object(func_value):
    """Convert function objects to picklable FunctionReference objects."""
    try:
        if callable(func_value) and hasattr(func_value, '__module__'):
            # Single function → FunctionReference
            return _get_function_reference(func_value)

        elif isinstance(func_value, tuple) and len(func_value) == 2:
            # Function with parameters tuple → (FunctionReference, params)
            func, params = func_value
            if callable(func):
                func_ref = _refresh_function_object(func)
                return (func_ref, params)

        elif isinstance(func_value, list):
            # List of functions → List of FunctionReferences
            return [_refresh_function_object(item) for item in func_value]

        elif isinstance(func_value, dict):
            # Dict of functions → Dict of FunctionReferences
            return {key: _refresh_function_object(value) for key, value in func_value.items()}

    except Exception as e:
        import logging
        logger = logging.getLogger(__name__)
        logger.warning(f"Failed to create function reference for {func_value}: {e}")
        # If we can't create a reference, return original (may fail later)
        return func_value

    return func_value


def _get_function_reference(func):
    """Convert a function to a picklable FunctionReference."""
    try:
        from openhcs.processing.backends.lib_registry.registry_service import RegistryService

        # Get all function metadata to find this function
        all_functions = RegistryService.get_all_functions_with_metadata()

        # Find the metadata for this function by matching name and module
        for composite_key, metadata in all_functions.items():
            if (metadata.func.__name__ == func.__name__ and
                metadata.func.__module__ == func.__module__):
                # Create a picklable reference instead of the function object
                return FunctionReference(
                    function_name=func.__name__,
                    registry_name=metadata.registry.library_name,
                    memory_type=metadata.registry.MEMORY_TYPE,
                    composite_key=composite_key
                )

    except Exception as e:
        import logging
        logger = logging.getLogger(__name__)
        logger.warning(f"Failed to create function reference for {func.__name__}: {e}")

    # If we can't create a reference, this function isn't in the registry
    # This should not happen for properly registered functions
    raise RuntimeError(f"Function {func.__name__} not found in registry - cannot create reference")


def _normalize_step_attributes(pipeline_definition: List[AbstractStep]) -> None:
    """Backwards compatibility: Set missing step attributes to constructor defaults."""
    sig = inspect.signature(AbstractStep.__init__)
    # Include ALL parameters with defaults, even None values
    defaults = {name: param.default for name, param in sig.parameters.items()
                if name != 'self' and param.default is not inspect.Parameter.empty}

    # Add attributes that are set manually in AbstractStep.__init__ but not constructor parameters
    manual_attributes = {
        '__input_dir__': None,
        '__output_dir__': None,
    }

    for i, step in enumerate(pipeline_definition):
        # Set missing constructor parameters
        for attr_name, default_value in defaults.items():
            if not hasattr(step, attr_name):
                setattr(step, attr_name, default_value)

        # Set missing manual attributes (for backwards compatibility with older serialized steps)
        for attr_name, default_value in manual_attributes.items():
            if not hasattr(step, attr_name):
                setattr(step, attr_name, default_value)


class PipelineCompiler:
    """
    Compiles a pipeline by populating step plans within a ProcessingContext.

    This class provides static methods that are called sequentially by the
    PipelineOrchestrator for each well's ProcessingContext. Each method
    is responsible for a specific part of the compilation process, such as
    path planning, special I/O resolution, materialization flag setting,
    memory contract validation, and GPU resource assignment.
    """

    @staticmethod
    def initialize_step_plans_for_context(
        context: ProcessingContext,
        steps_definition: List[AbstractStep],
        orchestrator,
        metadata_writer: bool = False,
        plate_path: Optional[Path] = None
        # base_input_dir and axis_id parameters removed, will use from context
    ) -> None:
        """
        Initializes step_plans by calling PipelinePathPlanner.prepare_pipeline_paths,
        which handles primary paths, special I/O path planning and linking, and chainbreaker status.
        Then, this method supplements the plans with non-I/O FunctionStep-specific attributes.

        Args:
            context: ProcessingContext to initialize step plans for
            steps_definition: List of AbstractStep objects defining the pipeline
            orchestrator: Orchestrator instance for well filter resolution
            metadata_writer: If True, this well is responsible for creating OpenHCS metadata files
            plate_path: Path to plate root for zarr conversion detection
        """
        # NOTE: This method is called within config_context() wrapper in compile_pipelines()
        if context.is_frozen():
            raise AttributeError("Cannot initialize step plans in a frozen ProcessingContext.")

        if not hasattr(context, 'step_plans') or context.step_plans is None:
            context.step_plans = {} # Ensure step_plans dict exists

        # === VISUALIZER CONFIG EXTRACTION ===
        # Extract visualizer config from orchestrator.pipeline_config
        # The caller has already set up config_context(orchestrator.pipeline_config)
        # so we can just access the field directly - lazy resolution happens automatically
        context.visualizer_config = orchestrator.pipeline_config.visualizer_config

        # === BACKWARDS COMPATIBILITY PREPROCESSING ===
        # Ensure all steps have complete attribute sets based on AbstractStep constructor
        # This must happen before any other compilation logic to eliminate defensive programming
        logger.debug("🔧 BACKWARDS COMPATIBILITY: Normalizing step attributes...")
        _normalize_step_attributes(steps_definition)



        # Pre-initialize step_plans with basic entries for each step
        # Use step index as key instead of step_id for multiprocessing compatibility
        for step_index, step in enumerate(steps_definition):
            if step_index not in context.step_plans:
                context.step_plans[step_index] = {
                    "step_name": step.name,
                    "step_type": step.__class__.__name__,
                    "axis_id": context.axis_id,
                }

        # === INPUT CONVERSION DETECTION ===
        # Check if first step needs zarr conversion
        if steps_definition and plate_path:
            first_step = steps_definition[0]
            # Access config directly from orchestrator.pipeline_config (lazy resolution via config_context)
            vfs_config = orchestrator.pipeline_config.vfs_config

            # Only convert if default materialization backend is ZARR
            wants_zarr_conversion = (
                vfs_config.materialization_backend == MaterializationBackend.ZARR
            )

            if wants_zarr_conversion:
                # Check if input plate is already zarr format
                available_backends = context.microscope_handler.get_available_backends(plate_path)
                already_zarr = Backend.ZARR in available_backends

                if not already_zarr:
                    # Determine if input uses virtual workspace
                    from openhcs.microscopes.openhcs import OpenHCSMetadataHandler
                    openhcs_metadata_handler = OpenHCSMetadataHandler(context.filemanager)
                    metadata = openhcs_metadata_handler._load_metadata_dict(plate_path)
                    subdirs = metadata["subdirectories"]
                    # Get actual subdirectory from input_dir (e.g., "TimePoint_1" for ImageXpress)
                    original_subdir = Path(context.input_dir).name
                    uses_virtual_workspace = Backend.VIRTUAL_WORKSPACE.value in subdirs[original_subdir]["available_backends"]

                    zarr_subdir = "zarr" if uses_virtual_workspace else original_subdir
                    conversion_dir = plate_path / zarr_subdir

                    context.step_plans[0]["input_conversion_dir"] = str(conversion_dir)
                    context.step_plans[0]["input_conversion_backend"] = MaterializationBackend.ZARR.value
                    context.step_plans[0]["input_conversion_uses_virtual_workspace"] = uses_virtual_workspace
                    context.step_plans[0]["input_conversion_original_subdir"] = original_subdir
                    logger.debug(f"Input conversion to zarr enabled for first step: {first_step.name}")

        # The axis_id and base_input_dir are available from the context object.
        # Path planning now gets config directly from orchestrator.pipeline_config parameter
        PipelinePathPlanner.prepare_pipeline_paths(
            context,
            steps_definition,
            orchestrator.pipeline_config
        )

        # === FUNCTION OBJECT REFRESH ===
        # CRITICAL FIX: Refresh all function objects to ensure they're picklable
        # This prevents multiprocessing pickling errors by ensuring clean function objects
        logger.debug("🔧 FUNCTION REFRESH: Refreshing all function objects for picklability...")
        _refresh_function_objects_in_steps(steps_definition)

        # === LAZY CONFIG RESOLUTION ===
        # Resolve each step's lazy configs with proper nested context
        # This ensures step-level configs inherit from pipeline-level configs
        # Architecture: GlobalPipelineConfig -> PipelineConfig -> Step (same as UI)
        logger.debug("🔧 LAZY CONFIG RESOLUTION: Resolving lazy configs with nested step contexts...")
        from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization
        from openhcs.config_framework.context_manager import config_context

        # Resolve each step individually with nested context (pipeline -> step)
        # NOTE: The caller has already set up config_context(orchestrator.pipeline_config)
        # We add step-level context on top for each step
        resolved_steps = []
        for step in steps_definition:
            with config_context(step):  # Step-level context on top of pipeline context
                resolved_step = resolve_lazy_configurations_for_serialization(step)
                resolved_steps.append(resolved_step)
        steps_definition = resolved_steps

        # Loop to supplement step_plans with non-I/O, non-path attributes
        # after PipelinePathPlanner has fully populated them with I/O info.
        for step_index, step in enumerate(steps_definition):
            if step_index not in context.step_plans:
                logger.error(
                    f"Critical error: Step {step.name} (index: {step_index}) "
                    f"not found in step_plans after path planning phase. Clause 504."
                )
                # Create a minimal error plan
                context.step_plans[step_index] = {
                     "step_name": step.name,
                     "step_type": step.__class__.__name__,
                     "axis_id": context.axis_id, # Use context.axis_id
                     "error": "Missing from path planning phase by PipelinePathPlanner",
                     "create_openhcs_metadata": metadata_writer # Set metadata writer responsibility flag
                }
                continue

            current_plan = context.step_plans[step_index]

            # Ensure basic metadata (PathPlanner should set most of this)
            current_plan["step_name"] = step.name
            current_plan["step_type"] = step.__class__.__name__
            current_plan["axis_id"] = context.axis_id # Use context.axis_id; PathPlanner should also use context.axis_id
            current_plan.setdefault("visualize", False) # Ensure visualize key exists
            current_plan["create_openhcs_metadata"] = metadata_writer # Set metadata writer responsibility flag

            # The special_outputs and special_inputs are now fully handled by PipelinePathPlanner.
            # The block for planning special_outputs (lines 134-148 in original) is removed.
            # Ensure these keys exist as OrderedDicts if PathPlanner doesn't guarantee it
            # (PathPlanner currently creates them as dicts, OrderedDict might not be strictly needed here anymore)
            current_plan.setdefault("special_inputs", OrderedDict())
            current_plan.setdefault("special_outputs", OrderedDict())
            current_plan.setdefault("chainbreaker", False) # PathPlanner now sets this.

            # Add step-specific attributes (non-I/O, non-path related)
            current_plan["variable_components"] = step.variable_components
            current_plan["group_by"] = step.group_by
            # Lazy configs were already resolved at the beginning of compilation
            resolved_step = step

            # DEBUG: Check what the resolved napari config actually has
            if hasattr(resolved_step, 'napari_streaming_config') and resolved_step.napari_streaming_config:
                logger.debug(f"resolved_step.napari_streaming_config.well_filter = {resolved_step.napari_streaming_config.well_filter}")
            if hasattr(resolved_step, 'step_well_filter_config') and resolved_step.step_well_filter_config:
                logger.debug(f"resolved_step.step_well_filter_config.well_filter = {resolved_step.step_well_filter_config.well_filter}")
            if hasattr(resolved_step, 'step_materialization_config') and resolved_step.step_materialization_config:
                logger.debug(f"resolved_step.step_materialization_config.sub_dir = '{resolved_step.step_materialization_config.sub_dir}' (type: {type(resolved_step.step_materialization_config).__name__})")

            # Store WellFilterConfig instances only if they match the current axis
            from openhcs.core.config import WellFilterConfig, StreamingConfig, WellFilterMode
            has_streaming = False
            required_visualizers = getattr(context, 'required_visualizers', [])

            # CRITICAL FIX: Ensure required_visualizers is always set on context
            # This prevents AttributeError during execution phase
            if not hasattr(context, 'required_visualizers'):
                context.required_visualizers = []

            # Get step axis filters for this step
            step_axis_filters = getattr(context, 'step_axis_filters', {}).get(step_index, {})

            logger.debug(f"Processing step '{step.name}' with attributes: {[attr for attr in dir(resolved_step) if not attr.startswith('_') and 'config' in attr]}")
            if step.name == "Image Enhancement Processing":
                logger.debug(f"All attributes for {step.name}: {[attr for attr in dir(resolved_step) if not attr.startswith('_')]}")

            for attr_name in dir(resolved_step):
                if not attr_name.startswith('_'):
                    config = getattr(resolved_step, attr_name, None)
                    # Configs are already resolved to base configs at line 277
                    # No need to call to_base_config() again - that's legacy code

                    # Unified handling: compute inclusion for any WellFilterConfig (StreamingConfig subclasses it)
                    is_streaming = config is not None and isinstance(config, StreamingConfig)
                    is_wellfilter = config is not None and isinstance(config, WellFilterConfig)

                    include_config = False
                    if is_wellfilter:
                        # Check if this config has a well filter and if current axis matches
                        should_include_config = True
                        if config.well_filter is not None:
                            config_filter = step_axis_filters.get(attr_name)
                            if config_filter:
                                # Apply axis filter logic
                                axis_in_filter = context.axis_id in config_filter['resolved_axis_values']
                                should_include_config = (
                                    axis_in_filter if config_filter['filter_mode'] == WellFilterMode.INCLUDE
                                    else not axis_in_filter
                                )
                        if should_include_config:
                            include_config = True

                    # Only add the config to the plan if it's included (or not a WellFilterConfig)
                    if include_config or (not is_wellfilter and config is not None):
                        current_plan[attr_name] = config

                    # Streaming extras only apply if the streaming config is included
                    if is_streaming and include_config:
                        # Validate that the visualizer can actually be created
                        try:
                            # Only validate configs that actually have a backend (real streaming configs)
                            if not hasattr(config, 'backend'):
                                continue

                            # Test visualizer creation without actually creating it
                            if hasattr(config, 'create_visualizer'):
                                # For napari, check if napari is available and environment supports GUI
                                if config.backend.name == 'NAPARI_STREAM':
                                    from openhcs.utils.import_utils import optional_import
                                    import os

                                    # Check if running in headless/CI environment
                                    # CPU-only mode does NOT imply headless - you can run CPU mode with napari
                                    is_headless = (
                                        os.getenv('CI', 'false').lower() == 'true' or
                                        os.getenv('OPENHCS_HEADLESS', 'false').lower() == 'true' or
                                        os.getenv('DISPLAY') is None
                                    )

                                    if is_headless:
                                        logger.info(f"Napari streaming disabled for step '{step.name}': running in headless environment (CI or no DISPLAY)")
                                        continue  # Skip this streaming config

                                    napari = optional_import("napari")
                                    if napari is None:
                                        logger.warning(f"Napari streaming disabled for step '{step.name}': napari not installed. Install with: pip install 'openhcs[viz]' or pip install napari")
                                        continue  # Skip this streaming config

                            has_streaming = True
                            # Collect visualizer info
                            visualizer_info = {
                                'backend': config.backend.name,
                                'config': config
                            }
                            if visualizer_info not in required_visualizers:
                                required_visualizers.append(visualizer_info)
                        except Exception as e:
                            logger.warning(f"Streaming disabled for step '{step.name}': {e}")
                            continue  # Skip this streaming config

            # Set visualize flag for orchestrator if any streaming is enabled
            current_plan["visualize"] = has_streaming
            context.required_visualizers = required_visualizers

        # Add FunctionStep specific attributes
        if isinstance(step, FunctionStep):

                # 🎯 SEMANTIC COHERENCE FIX: Prevent group_by/variable_components conflict
                # When variable_components contains the same value as group_by,
                # set group_by to None to avoid EZStitcher heritage rule violation
                if (step.variable_components and step.group_by and
                    step.group_by in step.variable_components):
                    logger.debug(f"Step {step.name}: Detected group_by='{step.group_by}' in variable_components={step.variable_components}. "
                                f"Setting group_by=None to maintain semantic coherence.")
                    current_plan["group_by"] = None

                # func attribute is guaranteed in FunctionStep.__init__
                current_plan["func_name"] = getattr(step.func, '__name__', str(step.func))

                # Memory type hints from step instance (set in FunctionStep.__init__ if provided)
                # These are initial hints; FuncStepContractValidator will set final types.
                if hasattr(step, 'input_memory_type_hint'): # From FunctionStep.__init__
                    current_plan['input_memory_type_hint'] = step.input_memory_type_hint
                if hasattr(step, 'output_memory_type_hint'): # From FunctionStep.__init__
                    current_plan['output_memory_type_hint'] = step.output_memory_type_hint

    # The resolve_special_input_paths_for_context static method is DELETED (lines 181-238 of original)
    # as this functionality is now handled by PipelinePathPlanner.prepare_pipeline_paths.

    # _prepare_materialization_flags is removed as MaterializationFlagPlanner.prepare_pipeline_flags
    # now modifies context.step_plans in-place and takes context directly.

    @staticmethod
    def declare_zarr_stores_for_context(
        context: ProcessingContext,
        steps_definition: List[AbstractStep],
        orchestrator
    ) -> None:
        """
        Declare zarr store creation functions for runtime execution.

        This method runs after path planning but before materialization flag planning
        to declare which steps need zarr stores and provide the metadata needed
        for runtime store creation.

        Args:
            context: ProcessingContext for current well
            steps_definition: List of AbstractStep objects
            orchestrator: Orchestrator instance for accessing all wells
        """
        from openhcs.constants import MULTIPROCESSING_AXIS

        all_wells = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)

        # Access config directly from orchestrator.pipeline_config (lazy resolution via config_context)
        vfs_config = orchestrator.pipeline_config.vfs_config

        for step_index, step in enumerate(steps_definition):
            step_plan = context.step_plans[step_index]

            will_use_zarr = (
                vfs_config.materialization_backend == MaterializationBackend.ZARR and
                step_index == len(steps_definition) - 1
            )

            if will_use_zarr:
                step_plan["zarr_config"] = {
                    "all_wells": all_wells,
                    "needs_initialization": True
                }
                logger.debug(f"Step '{step.name}' will use zarr backend for axis {context.axis_id}")
            else:
                step_plan["zarr_config"] = None

    @staticmethod
    def plan_materialization_flags_for_context(
        context: ProcessingContext,
        steps_definition: List[AbstractStep],
        orchestrator
    ) -> None:
        """
        Plans and injects materialization flags into context.step_plans
        by calling MaterializationFlagPlanner.
        """
        if context.is_frozen():
            raise AttributeError("Cannot plan materialization flags in a frozen ProcessingContext.")
        if not context.step_plans:
             logger.warning("step_plans is empty in context for materialization planning. This may be valid if pipeline is empty.")
             return

        # MaterializationFlagPlanner.prepare_pipeline_flags now takes context and pipeline_definition
        # and modifies context.step_plans in-place.
        MaterializationFlagPlanner.prepare_pipeline_flags(
            context,
            steps_definition,
            orchestrator.plate_path,
            orchestrator.pipeline_config
        )

        # Post-check (optional, but good for ensuring contracts are met by the planner)
        for step_index, step in enumerate(steps_definition):
            if step_index not in context.step_plans:
                 # This should not happen if prepare_pipeline_flags guarantees plans for all steps
                logger.error(f"Step {step.name} (index: {step_index}) missing from step_plans after materialization planning.")
                continue

            plan = context.step_plans[step_index]
            # Check for keys that FunctionStep actually uses during execution
            required_keys = [READ_BACKEND, WRITE_BACKEND]
            if not all(k in plan for k in required_keys):
                missing_keys = [k for k in required_keys if k not in plan]
                logger.error(
                    f"Materialization flag planning incomplete for step {step.name} (index: {step_index}). "
                    f"Missing required keys: {missing_keys} (Clause 273)."
                )


    @staticmethod
    def validate_memory_contracts_for_context(
        context: ProcessingContext,
        steps_definition: List[AbstractStep],
        orchestrator=None
    ) -> None:
        """
        Validates FunctionStep memory contracts, dict patterns, and adds memory type info to context.step_plans.

        Args:
            context: ProcessingContext to validate
            steps_definition: List of AbstractStep objects
            orchestrator: Optional orchestrator for dict pattern key validation
        """
        if context.is_frozen():
            raise AttributeError("Cannot validate memory contracts in a frozen ProcessingContext.")

        # FuncStepContractValidator might need access to input/output_memory_type_hint from plan
        step_memory_types = FuncStepContractValidator.validate_pipeline(
            steps=steps_definition,
            pipeline_context=context, # Pass context so validator can access step plans for memory type overrides
            orchestrator=orchestrator # Pass orchestrator for dict pattern key validation
        )

        for step_index, memory_types in step_memory_types.items():
            if "input_memory_type" not in memory_types or "output_memory_type" not in memory_types:
                step_name = context.step_plans[step_index]["step_name"]
                raise AssertionError(
                    f"Memory type validation must set input/output_memory_type for FunctionStep {step_name} (index: {step_index}) (Clause 101)."
                )
            if step_index in context.step_plans:
                context.step_plans[step_index].update(memory_types)
            else:
                logger.warning(f"Step index {step_index} found in memory_types but not in context.step_plans. Skipping.")

        # Apply memory type override: Any step with disk output must use numpy for disk writing
        for step_index, step in enumerate(steps_definition):
            if isinstance(step, FunctionStep):
                if step_index in context.step_plans:
                    step_plan = context.step_plans[step_index]
                    is_last_step = (step_index == len(steps_definition) - 1)
                    write_backend = step_plan['write_backend']

                    if write_backend == 'disk':
                        logger.debug(f"Step {step.name} has disk output, overriding output_memory_type to numpy")
                        step_plan['output_memory_type'] = 'numpy'



    @staticmethod
    def assign_gpu_resources_for_context(
        context: ProcessingContext
    ) -> None:
        """
        Validates GPU memory types from context.step_plans and assigns GPU device IDs.
        (Unchanged from previous version)
        """
        if context.is_frozen():
            raise AttributeError("Cannot assign GPU resources in a frozen ProcessingContext.")

        gpu_assignments = GPUMemoryTypeValidator.validate_step_plans(context.step_plans)

        for step_index, step_plan_val in context.step_plans.items(): # Renamed step_plan to step_plan_val to avoid conflict
            is_gpu_step = False
            input_type = step_plan_val["input_memory_type"]
            if input_type in VALID_GPU_MEMORY_TYPES:
                is_gpu_step = True

            output_type = step_plan_val["output_memory_type"]
            if output_type in VALID_GPU_MEMORY_TYPES:
                is_gpu_step = True

            if is_gpu_step:
                # Ensure gpu_assignments has an entry for this step_index if it's a GPU step
                # And that entry contains a 'gpu_id'
                step_gpu_assignment = gpu_assignments[step_index]
                if "gpu_id" not in step_gpu_assignment:
                    step_name = step_plan_val["step_name"]
                    raise AssertionError(
                        f"GPU validation must assign gpu_id for step {step_name} (index: {step_index}) "
                        f"with GPU memory types (Clause 295)."
                    )

        for step_index, gpu_assignment in gpu_assignments.items():
            if step_index in context.step_plans:
                context.step_plans[step_index].update(gpu_assignment)
            else:
                logger.warning(f"Step index {step_index} found in gpu_assignments but not in context.step_plans. Skipping.")

    @staticmethod
    def apply_global_visualizer_override_for_context(
        context: ProcessingContext,
        global_enable_visualizer: bool
    ) -> None:
        """
        Applies global visualizer override to all step_plans in the context.
        (Unchanged from previous version)
        """
        if context.is_frozen():
            raise AttributeError("Cannot apply visualizer override in a frozen ProcessingContext.")

        if global_enable_visualizer:
            if not context.step_plans: return # Guard against empty step_plans
            for step_index, plan in context.step_plans.items():
                plan["visualize"] = True
                logger.info(f"Global visualizer override: Step '{plan['step_name']}' marked for visualization.")

    @staticmethod
    def resolve_lazy_dataclasses_for_context(context: ProcessingContext, orchestrator) -> None:
        """
        Resolve all lazy dataclass instances in step plans to their base configurations.

        This method should be called after all compilation phases but before context
        freezing to ensure step plans are safe for pickling in multiprocessing contexts.

        NOTE: The caller MUST have already set up config_context(orchestrator.pipeline_config)
        before calling this method. We rely on that context for lazy resolution.

        Args:
            context: ProcessingContext to process
            orchestrator: PipelineOrchestrator (unused - kept for API compatibility)
        """
        from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization

        # Resolve the entire context recursively to catch all lazy dataclass instances
        # The caller has already set up config_context(), so lazy resolution happens automatically
        resolved_context_dict = resolve_lazy_configurations_for_serialization(vars(context))

        # Update context attributes with resolved values
        for attr_name, resolved_value in resolved_context_dict.items():
            if not attr_name.startswith('_'):  # Skip private attributes
                setattr(context, attr_name, resolved_value)

    @staticmethod
    def ensure_analysis_materialization(pipeline_definition: List[AbstractStep]) -> None:
        """
        Ensure intermediate steps with analysis outputs have step_materialization_config.

        Analysis results (special outputs) must be saved alongside the images they were
        created from to maintain metadata coherence. For intermediate steps (not final),
        this requires materializing the images so analysis has matching image metadata.

        Final steps don't need auto-creation because their images and analysis both
        go to main output directory (no metadata mismatch).

        Called once before per-well compilation loop.

        Args:
            pipeline_definition: List of pipeline steps to check
        """
        from openhcs.core.config import StepMaterializationConfig

        for step_index, step in enumerate(pipeline_definition):
            # Only process FunctionSteps
            if not isinstance(step, FunctionStep):
                continue

            # Check if step has special outputs (analysis results)
            has_special_outputs = hasattr(step.func, '__special_outputs__') and step.func.__special_outputs__

            # Only auto-create for intermediate steps (not final step)
            is_intermediate_step = step_index < len(pipeline_definition) - 1

            if has_special_outputs and not step.step_materialization_config and is_intermediate_step:
                # Auto-instantiate step materialization to preserve metadata coherence
                # Use LazyStepMaterializationConfig to enable proper inheritance from global config
                from openhcs.config_framework.lazy_factory import LazyStepMaterializationConfig
                step.step_materialization_config = LazyStepMaterializationConfig()

                logger.warning(
                    f"⚠️  Step '{step.name}' (index {step_index}) has analysis outputs but no "
                    f"step_materialization_config. Auto-creating with defaults to preserve "
                    f"metadata coherence (intermediate step analysis must be saved with matching images)."
                )
                logger.info(
                    f"    → Images and analysis will be saved to: "
                    f"{{plate_root}}/{step.step_materialization_config.sub_dir}/"
                )

    @staticmethod
    def compile_pipelines(
        orchestrator,
        pipeline_definition: List[AbstractStep],
        axis_filter: Optional[List[str]] = None,
        enable_visualizer_override: bool = False
    ) -> Dict[str, ProcessingContext]:
        """
        Compile-all phase: Prepares frozen ProcessingContexts for each axis value.

        This method iterates through the specified axis values, creates a ProcessingContext
        for each, and invokes the various phases of the PipelineCompiler to populate
        the context's step_plans. After all compilation phases for an axis value are complete,
        its context is frozen. Finally, attributes are stripped from the pipeline_definition,
        making the step objects stateless for the execution phase.

        Args:
            orchestrator: The PipelineOrchestrator instance to use for compilation
            pipeline_definition: The list of AbstractStep objects defining the pipeline.
            axis_filter: Optional list of axis values to process. If None, processes all found axis values.
            enable_visualizer_override: If True, all steps in all compiled contexts
                                        will have their 'visualize' flag set to True.

        Returns:
            A dictionary mapping axis values to their compiled and frozen ProcessingContexts.
            The input `pipeline_definition` list (of step objects) is modified in-place
            to become stateless.
        """
        from openhcs.constants.constants import OrchestratorState
        from openhcs.core.pipeline.step_attribute_stripper import StepAttributeStripper

        if not orchestrator.is_initialized():
            raise RuntimeError("PipelineOrchestrator must be explicitly initialized before calling compile_pipelines().")

        if not pipeline_definition:
            raise ValueError("A valid pipeline definition (List[AbstractStep]) must be provided.")

        try:
            compiled_contexts: Dict[str, ProcessingContext] = {}
            # Get multiprocessing axis values dynamically from configuration
            from openhcs.constants import MULTIPROCESSING_AXIS
            axis_values_to_process = orchestrator.get_component_keys(MULTIPROCESSING_AXIS, axis_filter)

            if not axis_values_to_process:
                logger.warning("No axis values found to process based on filter.")
                return {
                    'pipeline_definition': pipeline_definition,
                    'compiled_contexts': {}
                }

            logger.info(f"Starting compilation for axis values: {', '.join(axis_values_to_process)}")

            # === ANALYSIS MATERIALIZATION AUTO-INSTANTIATION ===
            # Ensure intermediate steps with analysis outputs have step_materialization_config
            # This preserves metadata coherence (ROIs must match image structure they were created from)
            PipelineCompiler.ensure_analysis_materialization(pipeline_definition)

            # === GLOBAL AXIS FILTER RESOLUTION ===
            # Resolve axis filters once for all axis values to ensure step-level inheritance works
            logger.debug("🔧 LAZY CONFIG RESOLUTION: Resolving lazy configs for axis filter resolution...")
            from openhcs.config_framework.lazy_factory import resolve_lazy_configurations_for_serialization
            from openhcs.config_framework.context_manager import config_context

            # Resolve each step with nested context (same as initialize_step_plans_for_context)
            # This ensures step-level configs inherit from pipeline-level configs
            resolved_steps_for_filters = []
            with config_context(orchestrator.pipeline_config):
                for step in pipeline_definition:
                    with config_context(step):  # Step-level context on top of pipeline context
                        resolved_step = resolve_lazy_configurations_for_serialization(step)
                        resolved_steps_for_filters.append(resolved_step)

            logger.debug("🎯 AXIS FILTER RESOLUTION: Resolving step axis filters...")
            # Create a temporary context to store the global axis filters
            temp_context = orchestrator.create_context("temp")

            # Use orchestrator context during axis filter resolution
            # This ensures that lazy config resolution uses the orchestrator context
            from openhcs.config_framework.context_manager import config_context
            with config_context(orchestrator.pipeline_config):
                _resolve_step_axis_filters(resolved_steps_for_filters, temp_context, orchestrator)
            global_step_axis_filters = getattr(temp_context, 'step_axis_filters', {})

            # Determine responsible axis value for metadata creation (lexicographically first)
            responsible_axis_value = sorted(axis_values_to_process)[0] if axis_values_to_process else None
            logger.debug(f"Designated responsible axis value for metadata creation: {responsible_axis_value}")

            for axis_id in axis_values_to_process:
                logger.debug(f"Compiling for axis value: {axis_id}")
                context = orchestrator.create_context(axis_id)

                # Copy global axis filters to this context
                context.step_axis_filters = global_step_axis_filters

                # Determine if this axis value is responsible for metadata creation
                is_responsible = (axis_id == responsible_axis_value)
                logger.debug(f"Axis {axis_id} metadata responsibility: {is_responsible}")

                # CRITICAL: Wrap all compilation steps in config_context() for lazy resolution
                from openhcs.config_framework.context_manager import config_context
                with config_context(orchestrator.pipeline_config):
                    PipelineCompiler.initialize_step_plans_for_context(context, pipeline_definition, orchestrator, metadata_writer=is_responsible, plate_path=orchestrator.plate_path)
                    PipelineCompiler.declare_zarr_stores_for_context(context, pipeline_definition, orchestrator)
                    PipelineCompiler.plan_materialization_flags_for_context(context, pipeline_definition, orchestrator)
                    PipelineCompiler.validate_memory_contracts_for_context(context, pipeline_definition, orchestrator)
                    PipelineCompiler.assign_gpu_resources_for_context(context)

                    if enable_visualizer_override:
                        PipelineCompiler.apply_global_visualizer_override_for_context(context, True)

                    # Resolve all lazy dataclasses before freezing to ensure multiprocessing compatibility
                    PipelineCompiler.resolve_lazy_dataclasses_for_context(context, orchestrator)





                context.freeze()
                compiled_contexts[axis_id] = context
                logger.debug(f"Compilation finished for axis value: {axis_id}")

            # Log path planning summary once per plate
            if compiled_contexts:
                first_context = next(iter(compiled_contexts.values()))
                logger.info("📁 PATH PLANNING SUMMARY:")
                logger.info(f"   Main pipeline output: {first_context.output_plate_root}")

                # Check for materialization steps in first context
                materialization_steps = []
                for step_id, plan in first_context.step_plans.items():
                    if 'materialized_output_dir' in plan:
                        step_name = plan.get('step_name', f'step_{step_id}')
                        mat_path = plan['materialized_output_dir']
                        materialization_steps.append((step_name, mat_path))

                for step_name, mat_path in materialization_steps:
                    logger.info(f"   Materialization {step_name}: {mat_path}")

            # After processing all wells, strip attributes and finalize
            logger.info("Stripping attributes from pipeline definition steps.")
            StepAttributeStripper.strip_step_attributes(pipeline_definition, {})

            orchestrator._state = OrchestratorState.COMPILED

            # Log worker configuration for execution planning
            effective_config = orchestrator.get_effective_config()
            logger.info(f"⚙️  EXECUTION CONFIG: {effective_config.num_workers} workers configured for pipeline execution")

            logger.info(f"🏁 COMPILATION COMPLETE: {len(compiled_contexts)} wells compiled successfully")

            # Return expected structure with both pipeline_definition and compiled_contexts
            return {
                'pipeline_definition': pipeline_definition,
                'compiled_contexts': compiled_contexts
            }
        except Exception as e:
            orchestrator._state = OrchestratorState.COMPILE_FAILED
            logger.error(f"Failed to compile pipelines: {e}")
            raise



# The monolithic compile() method is removed.
# Orchestrator will call the static methods above in sequence.
# _strip_step_attributes is also removed as StepAttributeStripper is called by Orchestrator.


def _resolve_step_axis_filters(resolved_steps: List[AbstractStep], context, orchestrator):
    """
    Resolve axis filters for steps with any WellFilterConfig instances.

    This function handles step-level axis filtering by resolving patterns like
    "row:A", ["A01", "B02"], or max counts against the available axis values for the plate.
    It processes ALL WellFilterConfig instances (materialization, streaming, etc.) uniformly.

    Args:
        resolved_steps: List of pipeline steps with lazy configs already resolved
        context: Processing context for the current axis value
        orchestrator: Orchestrator instance with access to available axis values
    """
    from openhcs.core.utils import WellFilterProcessor
    from openhcs.core.config import WellFilterConfig

    # Get available axis values from orchestrator using multiprocessing axis
    from openhcs.constants import MULTIPROCESSING_AXIS
    available_axis_values = orchestrator.get_component_keys(MULTIPROCESSING_AXIS)
    if not available_axis_values:
        logger.warning("No available axis values found for axis filter resolution")
        return

    # Initialize step_axis_filters in context if not present
    if not hasattr(context, 'step_axis_filters'):
        context.step_axis_filters = {}

    # Process each step for ALL WellFilterConfig instances using the already resolved steps
    for step_index, resolved_step in enumerate(resolved_steps):
        step_filters = {}

        # Check all attributes for WellFilterConfig instances on the RESOLVED step
        for attr_name in dir(resolved_step):
            if not attr_name.startswith('_'):
                config = getattr(resolved_step, attr_name, None)
                if config is not None and isinstance(config, WellFilterConfig) and config.well_filter is not None:
                    try:
                        # Resolve the axis filter pattern to concrete axis values
                        resolved_axis_values = WellFilterProcessor.resolve_compilation_filter(
                            config.well_filter,
                            available_axis_values
                        )

                        # Store resolved axis values for this config
                        step_filters[attr_name] = {
                            'resolved_axis_values': sorted(resolved_axis_values),
                            'filter_mode': config.well_filter_mode,
                            'original_filter': config.well_filter
                        }

                        logger.debug(f"Step '{resolved_step.name}' {attr_name} filter '{config.well_filter}' "
                                   f"resolved to {len(resolved_axis_values)} axis values: {sorted(resolved_axis_values)}")
                        logger.debug(f"Step '{resolved_step.name}' {attr_name} filter '{config.well_filter}' "
                                   f"resolved to {len(resolved_axis_values)} axis values: {sorted(resolved_axis_values)}")

                    except Exception as e:
                        logger.error(f"Failed to resolve axis filter for step '{resolved_step.name}' {attr_name}: {e}")
                        raise ValueError(f"Invalid axis filter '{config.well_filter}' "
                                       f"for step '{resolved_step.name}' {attr_name}: {e}")

        # Store step filters if any were found
        if step_filters:
            context.step_axis_filters[step_index] = step_filters

    total_filters = sum(len(filters) for filters in context.step_axis_filters.values())
    logger.debug(f"Axis filter resolution complete. {len(context.step_axis_filters)} steps have axis filters, {total_filters} total filters.")


def _should_process_for_well(axis_id, well_filter_config):
    """Unified well filtering logic for all WellFilterConfig systems."""
    if well_filter_config.well_filter is None:
        return True

    well_in_filter = axis_id in well_filter_config.well_filter
    return well_in_filter if well_filter_config.well_filter_mode == WellFilterMode.INCLUDE else not well_in_filter
