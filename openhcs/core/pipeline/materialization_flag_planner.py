"""
Materialization flag planner for OpenHCS.

This module provides the MaterializationFlagPlanner class, which is responsible for
determining materialization flags and backend selection for each step in a pipeline.

Doctrinal Clauses:
- Clause 12 — Absolute Clean Execution
- Clause 17 — VFS Exclusivity (FileManager is the only component that uses VirtualPath)
- Clause 65 — No Fallback Logic
- Clause 66 — Immutability After Construction
- Clause 88 — No Inferred Capabilities
- Clause 245 — Path Declaration
- Clause 273 — Backend Authorization Doctrine
- Clause 276 — Positional Backend Enforcement
- Clause 504 — Pipeline Preparation Modifications
"""

import logging
from pathlib import Path
from typing import List

from openhcs.constants.constants import READ_BACKEND, WRITE_BACKEND, Backend
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.config import MaterializationBackend

logger = logging.getLogger(__name__)


class MaterializationFlagPlanner:
    """Sets read/write backends for pipeline steps."""

    @staticmethod
    def prepare_pipeline_flags(
        context: ProcessingContext,
        pipeline_definition: List[AbstractStep],
        plate_path: Path,
        pipeline_config
    ) -> None:
        """Set read/write backends for pipeline steps."""

        # === SETUP ===
        # Access config directly from pipeline_config (lazy resolution via config_context)
        vfs_config = pipeline_config.vfs_config
        step_plans = context.step_plans

        # === PROCESS EACH STEP ===
        for i, step in enumerate(pipeline_definition):
            step_plan = step_plans[i]  # Use step index instead of step_id

            # === READ BACKEND SELECTION ===
            if i == 0:  # First step - read from plate format
                read_backend = MaterializationFlagPlanner._get_first_step_read_backend(context, vfs_config)
                step_plan[READ_BACKEND] = read_backend

                # Zarr conversion flag is already set by path planner if needed
            else:  # Other steps - read from memory (unless already set by chainbreaker logic)
                if READ_BACKEND not in step_plan:
                    # Check if this step reads from PIPELINE_START (original input)
                    from openhcs.core.steps.abstract import InputSource
                    if step.input_source == InputSource.PIPELINE_START:
                        # Use the same backend as the first step
                        step_plan[READ_BACKEND] = step_plans[0][READ_BACKEND]
                    else:
                        step_plan[READ_BACKEND] = Backend.MEMORY.value

            # === WRITE BACKEND SELECTION ===
            # Check if this step will use zarr (has zarr_config set by compiler)
            will_use_zarr = step_plan.get("zarr_config") is not None

            if will_use_zarr:
                # Steps with zarr_config should write to materialization backend
                materialization_backend = MaterializationFlagPlanner._resolve_materialization_backend(context, vfs_config)
                step_plan[WRITE_BACKEND] = materialization_backend
            elif i == len(pipeline_definition) - 1:  # Last step without zarr - write to materialization backend
                materialization_backend = MaterializationFlagPlanner._resolve_materialization_backend(context, vfs_config)
                step_plan[WRITE_BACKEND] = materialization_backend
            else:  # Other steps - write to memory
                step_plan[WRITE_BACKEND] = Backend.MEMORY.value

            # === PER-STEP MATERIALIZATION BACKEND SELECTION ===
            if "materialized_output_dir" in step_plan:
                materialization_backend = MaterializationFlagPlanner._resolve_materialization_backend(context, vfs_config)
                step_plan["materialized_backend"] = materialization_backend

    @staticmethod
    def _get_first_step_read_backend(context: ProcessingContext, vfs_config) -> str:
        """Get read backend for first step based on VFS config and metadata-based auto-detection."""

        # Check if user explicitly configured a read backend
        if vfs_config.read_backend != Backend.AUTO:
            return vfs_config.read_backend.value

        # AUTO mode: Use unified backend detection
        return MaterializationFlagPlanner._detect_backend_for_context(context, fallback_backend=Backend.DISK.value)

    @staticmethod
    def _resolve_materialization_backend(context: ProcessingContext, vfs_config) -> str:
        """Resolve materialization backend, handling AUTO option."""
        # Check if user explicitly configured a materialization backend
        if vfs_config.materialization_backend != MaterializationBackend.AUTO:
            return vfs_config.materialization_backend.value

        # AUTO mode: Use unified backend detection
        return MaterializationFlagPlanner._detect_backend_for_context(context, fallback_backend=MaterializationBackend.DISK.value)

    @staticmethod
    def _detect_backend_for_context(context: ProcessingContext, fallback_backend: str) -> str:
        """Unified backend detection logic for both read and materialization backends."""
        # Use the microscope handler's get_primary_backend method
        # This handles both OpenHCS (metadata-based) and other microscopes (compatibility-based)
        return context.microscope_handler.get_primary_backend(context.input_dir, context.filemanager)






