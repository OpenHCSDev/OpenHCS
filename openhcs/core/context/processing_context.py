"""
Processing Context for OpenHCS.

This module defines the ProcessingContext class, which maintains state during pipeline execution.
"""

from typing import Any, Dict, Optional

from openhcs.core.config import GlobalPipelineConfig, VFSConfig, PathPlanningConfig


class ProcessingContext:
    """
    Maintains state during pipeline execution.

    The ProcessingContext is the canonical owner of all state during pipeline execution.
    After compilation and freezing, it should be treated as immutable by processing steps.

    OWNERSHIP: This class may ONLY be instantiated by PipelineOrchestrator.
    All other components must receive a context instance, never create one.

    Attributes:
        step_plans: Dictionary mapping step IDs to execution plans.
        outputs: Dictionary for step outputs (usage may change with VFS-centric model).
        intermediates: Dictionary for intermediate results (usage may change).
        current_step: Current executing step ID (usage may change).
        axis_id: Identifier of the multiprocessing axis value being processed.
        filemanager: Instance of FileManager for VFS operations.
        global_config: GlobalPipelineConfig holding system-wide configurations.
        pipeline_sequential_mode: Flag indicating pipeline-wide vs step-wide sequential processing.
        pipeline_sequential_combinations: Pre-computed sequential combinations for pipeline-wide mode.
        current_sequential_combination: Active combination during pipeline-wide sequential execution.
        _is_frozen: Internal flag indicating if the context is immutable.
    """

    def __init__(
        self,
        global_config: GlobalPipelineConfig, # Made a required argument
        step_plans: Optional[Dict[str, Dict[str, Any]]] = None,
        axis_id: Optional[str] = None,
        **kwargs
    ):
        """
        Initialize the processing context.

        Args:
            global_config: The global pipeline configuration object.
            step_plans: Dictionary mapping step IDs to execution plans.
            axis_id: Identifier of the multiprocessing axis value being processed.
            **kwargs: Additional context attributes (e.g., filemanager, microscope_handler).
        """
        # Initialize _is_frozen first to allow other attributes to be set by __setattr__
        # This direct assignment bypasses the custom __setattr__ during initialization.
        object.__setattr__(self, '_is_frozen', False)

        self.step_plans = step_plans or {}
        self.outputs = {}  # Future use TBD, primary data flow via VFS
        self.intermediates = {} # Future use TBD, primary data flow via VFS
        self.current_step = None # Future use TBD
        self.axis_id = axis_id
        self.global_config = global_config # Store the global config
        self.filemanager = None # Expected to be set by Orchestrator via kwargs or direct assignment

        # Pipeline-wide sequential processing fields
        self.pipeline_sequential_mode = False
        self.pipeline_sequential_combinations = None  # Precomputed at compile time from metadata
        self.current_sequential_combination = None  # Set by compiler for each combination iteration

        # Add any additional attributes from kwargs
        # Note: 'filemanager' is often passed via kwargs by PipelineOrchestrator.create_context
        for key, value in kwargs.items():
            setattr(self, key, value) # This will now go through our __setattr__

    def __setattr__(self, name: str, value: Any) -> None:
        """
        Set an attribute, preventing modification if the context is frozen.

        All fields are immutable once frozen - no exceptions.
        """
        if getattr(self, '_is_frozen', False) and name != '_is_frozen':
            raise AttributeError(f"Cannot modify attribute '{name}' of a frozen ProcessingContext.")
        super().__setattr__(name, value)

    def inject_plan(self, step_id: str, plan: Dict[str, Any]) -> None:
        """
        Inject a step plan into the context.

        This method is the canonical way to add step plans to the context during compilation.
        All step configuration must be injected into the context using this method.

        Args:
            step_id: The unique identifier of the step
            plan: The step execution plan

        Raises:
            AttributeError: If the context is frozen.
        """
        if self._is_frozen:
            raise AttributeError("Cannot inject plan into a frozen ProcessingContext.")
        self.step_plans[step_id] = plan

    def freeze(self) -> None:
        """
        Freezes the context, making its attributes immutable.

        This should be called after all compilation and plan injection is complete.
        Essential attributes like step_plans, filemanager, and axis_id must be set.

        Raises:
            RuntimeError: If essential attributes are not set before freezing.
        """
        if not self.axis_id:
            raise RuntimeError("Cannot freeze ProcessingContext: 'axis_id' is not set.")
        if not hasattr(self, 'filemanager') or self.filemanager is None:
            raise RuntimeError("Cannot freeze ProcessingContext: 'filemanager' is not set.")
        # step_plans can be empty if the pipeline is empty, but it must exist.
        if not hasattr(self, 'step_plans'):
             raise RuntimeError("Cannot freeze ProcessingContext: 'step_plans' attribute does not exist.")

        self._is_frozen = True # This assignment is allowed by __setattr__

    def is_frozen(self) -> bool:
        """
        Check if the context is frozen.

        Returns:
            True if the context is frozen, False otherwise.
        """
        return self._is_frozen



    # update_from_step_result method is removed as per plan.

    # --- Config Getters ---
    # NOTE: These are only used outside compilation (e.g., in workers after context is frozen)
    # During compilation, code should access orchestrator.pipeline_config directly

    def get_vfs_config(self) -> VFSConfig:
        """Returns the VFSConfig part of the global configuration."""
        if not hasattr(self, 'global_config') or self.global_config is None:
            raise RuntimeError("GlobalPipelineConfig not set on ProcessingContext.")
        return self.global_config.vfs_config

    def get_path_planning_config(self) -> PathPlanningConfig:
        """Returns the PathPlanningConfig part of the global configuration."""
        if not hasattr(self, 'global_config') or self.global_config is None:
            raise RuntimeError("GlobalPipelineConfig not set on ProcessingContext.")
        return self.global_config.path_planning_config

    def get_num_workers(self) -> int:
        """Returns the number of workers from the global configuration."""
        if not hasattr(self, 'global_config') or self.global_config is None:
            raise RuntimeError("GlobalPipelineConfig not set on ProcessingContext.")
        return self.global_config.num_workers

    def __getstate__(self) -> Dict[str, Any]:
        """
        Prepare context for pickling (e.g., for multiprocessing).

        Excludes the filemanager from pickling to avoid copying the storage registry
        across process boundaries. The filemanager will be recreated in the worker
        process using the worker's local global registry.

        Preserves zarr_config and plate_path so backends can be recreated with the same
        settings in the worker process.

        Returns:
            Dictionary of state to pickle
        """
        state = self.__dict__.copy()

        # Preserve zarr config from global_config for filemanager recreation
        if hasattr(self, 'global_config') and self.global_config is not None:
            state['_zarr_config'] = self.global_config.zarr_config
        else:
            state['_zarr_config'] = None

        # Preserve plate_path for virtual_workspace backend recreation
        if hasattr(self, 'plate_path'):
            state['_plate_path'] = self.plate_path
        else:
            state['_plate_path'] = None

        # Check if virtual_workspace backend is registered in the filemanager
        if hasattr(self, 'filemanager') and self.filemanager is not None:
            from openhcs.constants.constants import Backend
            state['_has_virtual_workspace'] = Backend.VIRTUAL_WORKSPACE.value in self.filemanager.registry

            # Check if OMERO backend is registered and preserve its connection params
            state['_has_omero_backend'] = 'omero_local' in self.filemanager.registry
            if state['_has_omero_backend']:
                omero_backend = self.filemanager.registry.get('omero_local')
                # Preserve connection parameters for worker process reconnection
                if hasattr(omero_backend, '_conn_params') and omero_backend._conn_params:
                    state['_omero_conn_params'] = omero_backend._conn_params
                else:
                    state['_omero_conn_params'] = None
            else:
                state['_omero_conn_params'] = None
        else:
            state['_has_virtual_workspace'] = False
            state['_has_omero_backend'] = False
            state['_omero_conn_params'] = None

        # Remove filemanager - will be recreated in worker process
        state.pop('filemanager', None)

        return state

    def __setstate__(self, state: Dict[str, Any]) -> None:
        """
        Restore context after unpickling (e.g., in worker process).

        Recreates the filemanager using the worker's local global registry,
        ensuring that all processes share the same memory backend instance
        within their own process space.

        Also recreates the virtual_workspace and OMERO backends if they were
        registered in the main process.

        Args:
            state: Dictionary of state from __getstate__
        """
        # Extract preserved state
        zarr_config = state.pop('_zarr_config', None)
        plate_path = state.pop('_plate_path', None)
        has_virtual_workspace = state.pop('_has_virtual_workspace', False)
        has_omero_backend = state.pop('_has_omero_backend', False)
        omero_conn_params = state.pop('_omero_conn_params', None)

        # Restore all other attributes
        self.__dict__.update(state)

        # Recreate filemanager in worker process using worker's local global registry
        from openhcs.io.base import storage_registry as global_storage_registry, ensure_storage_registry
        from openhcs.io.filemanager import FileManager
        from openhcs.io.zarr import ZarrStorageBackend
        from openhcs.constants.constants import Backend

        # Ensure worker's registry is initialized
        ensure_storage_registry()

        # Override zarr backend with preserved config (same as orchestrator does)
        if zarr_config is not None:
            zarr_backend_with_config = ZarrStorageBackend(zarr_config)
            global_storage_registry[Backend.ZARR.value] = zarr_backend_with_config

        # Recreate virtual_workspace backend if it was registered in main process
        if has_virtual_workspace and plate_path is not None:
            from openhcs.io.virtual_workspace import VirtualWorkspaceBackend
            from pathlib import Path
            try:
                virtual_backend = VirtualWorkspaceBackend(plate_root=Path(plate_path))
                global_storage_registry[Backend.VIRTUAL_WORKSPACE.value] = virtual_backend
            except Exception as e:
                # Log but don't fail - the backend might not be needed in this worker
                import logging
                logger = logging.getLogger(__name__)
                logger.warning(f"Failed to recreate virtual_workspace backend in worker: {e}")

        # Recreate OMERO backend if it was registered in main process
        if has_omero_backend and omero_conn_params is not None:
            from openhcs.io.omero_local import OMEROLocalBackend
            import logging
            import os
            logger = logging.getLogger(__name__)
            try:
                # Create backend instance without connection
                omero_backend = OMEROLocalBackend()
                # Restore connection parameters
                omero_backend._conn_params = omero_conn_params

                # Try to establish connection using stored params
                # Password comes from environment variable or defaults to 'openhcs'
                password = os.getenv('OMERO_PASSWORD', 'openhcs')
                from omero.gateway import BlitzGateway
                conn = BlitzGateway(
                    omero_conn_params['username'],
                    password,
                    host=omero_conn_params['host'],
                    port=omero_conn_params['port']
                )
                if conn.connect():
                    omero_backend._initial_conn = conn
                    global_storage_registry['omero_local'] = omero_backend
                    logger.info(f"✓ Recreated OMERO backend in worker process (connected to {omero_conn_params['host']}:{omero_conn_params['port']})")
                else:
                    logger.warning(f"Failed to connect to OMERO in worker process - backend not registered")
            except Exception as e:
                # Log but don't fail - the backend might not be needed in this worker
                logger.warning(f"Failed to recreate OMERO backend in worker: {e}")

        # Create filemanager using worker's local global registry
        # This ensures the worker uses its own memory backend instance
        # Use __dict__ directly to bypass frozen check
        self.__dict__['filemanager'] = FileManager(global_storage_registry)
