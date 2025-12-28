"""
Collection containers for ObjectState hierarchy tracking.

These dataclasses define the minimal schema for tracking parent-child relationships
in the ObjectState hierarchy. They are pure data containers with no logic.

Why these exist:
- RootState: Tracks which plates (orchestrators) exist in the application
- Pipeline class already exists - no PipelineState needed
- No PlateState - orchestrator already has plate_path, everything else derives
"""
from dataclasses import dataclass, field
from typing import List


@dataclass
class RootState:
    """Root container tracking all plates in the application.

    ObjectState wraps this to make orchestrator_scope_ids a tracked parameter.
    No methods - pure data container.

    The orchestrator_scope_ids list contains plate_paths (strings).
    Each plate_path is both:
    - The unique identifier for the plate
    - The scope_id for the orchestrator's PipelineConfig ObjectState

    Everything else derives from these path strings:
    - Display name: Path(plate_path).name (or config.display_name if added later)
    - Pipeline scope: f"{plate_path}::pipeline"
    - Orchestrator: Created on Init Plate, ephemeral

    Why just strings, not wrapper objects:
    - PlateState would wrap a string with derived fields (unnecessary indirection)
    - Single source of truth: if custom names needed, add to PipelineConfig
    - Orchestrator already has plate_path - no duplication
    """
    orchestrator_scope_ids: List[str] = field(default_factory=list)
