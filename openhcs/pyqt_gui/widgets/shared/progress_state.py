"""Progress state management for ZMQ execution tracking.

Uses generic TaskProgress from zmqruntime.messages.
Application-specific data stored in the context field.
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any
from enum import Enum
from PyQt6.QtCore import Qt
from PyQt6.QtWidgets import QTreeWidgetItem

from zmqruntime.messages import TaskProgress, TaskPhase, TaskStatus


# Export for convenience
__all__ = ["ExecutionProgressTracker", "AxisProgress"]


# Application-specific phase/status extensions
class AxisPhase(Enum):
    """OpenHCS-specific axis phases - extends TaskPhase."""

    QUEUED = "queued"
    INIT = "init"
    COMPILE = "compile"
    AXIS_STARTED = "axis_started"
    STEP_STARTED = "step_started"
    PATTERN_GROUP = "pattern_group"
    STEP_COMPLETED = "step_completed"
    AXIS_COMPLETED = "axis_completed"
    AXIS_ERROR = "axis_error"


class AxisStatus(Enum):
    """OpenHCS-specific axis status - maps to TaskStatus from zmqruntime.

    NOTE: We use TaskStatus.SUCCESS (value="success") as the completion status.
    Do NOT use "completed" - that's an app-specific value that gets mapped to SUCCESS.
    """

    PENDING = "pending"  # Maps to TaskStatus.PENDING
    STARTED = "started"  # Maps to TaskStatus.STARTED
    RUNNING = "running"  # Maps to TaskStatus.RUNNING
    SUCCESS = "success"  # Maps to TaskStatus.SUCCESS (this is the completion status!)
    ERROR = "error"  # App-specific, stored in context
    QUEUED = "queued"  # App-specific, stored in context


def status_emoji(status: AxisStatus) -> str:
    """Get emoji for status display."""
    return {
        AxisStatus.QUEUED: "⏸️",
        AxisStatus.PENDING: "⏸️",
        AxisStatus.STARTED: "🚀",
        AxisStatus.RUNNING: "⚙️",
        AxisStatus.SUCCESS: "✅",
        AxisStatus.ERROR: "❌",
    }.get(status, "❓")


@dataclass(frozen=True)
class AxisProgress:
    """Progress tracking for a single axis within an execution.

    Wraps TaskProgress from zmqruntime with application-specific fields.
    """

    execution_id: str
    plate_id: str
    axis_id: str
    step_name: str
    phase: AxisPhase
    status: AxisStatus
    percent: float
    completed: int
    total: int
    pid: int | None = None  # Worker process ID (if applicable)

    @classmethod
    def from_task_progress(cls, progress: TaskProgress) -> "AxisProgress":
        """Create from TaskProgress - converts string phase/status to AxisPhase/AxisStatus enums."""
        import logging

        logger = logging.getLogger(__name__)

        # Get phase/status values - handle both string and Enum types
        from enum import Enum

        phase_value = (
            progress.phase.value if isinstance(progress.phase, Enum) else progress.phase
        )
        status_value = (
            progress.status.value
            if isinstance(progress.status, Enum)
            else progress.status
        )

        # Convert phase string to AxisPhase enum
        try:
            axis_phase = AxisPhase(phase_value)
        except ValueError:
            logger.error(
                f"Invalid phase value '{phase_value}' from TaskProgress. "
                f"Valid AxisPhase values: {[p.value for p in AxisPhase]}. "
                f"TaskProgress: phase={phase_value}, status={status_value}, "
                f"step={progress.context.get('step')}, axis={progress.axis_id}"
            )
            raise

        # Convert status string to AxisStatus enum
        # Map "completed" to SUCCESS (common case from orchestrator)
        if status_value == "completed":
            axis_status = AxisStatus.SUCCESS
        else:
            try:
                axis_status = AxisStatus(status_value)
            except ValueError:
                logger.error(
                    f"Invalid status value '{status_value}' from TaskProgress. "
                    f"Valid AxisStatus values: {[s.value for s in AxisStatus]}. "
                    f"TaskProgress: phase={phase_value}, status={status_value}, "
                    f"step={progress.context.get('step')}, axis={progress.axis_id}"
                )
                raise

        # Use 'step' field (single source of truth)
        step = progress.context["step"]

        # Extract worker PID if present
        pid = progress.context.get("pid")
        if pid is not None:
            pid = int(pid)

        return cls(
            execution_id=progress.task_id,
            plate_id=progress.plate_id,
            axis_id=progress.axis_id,
            step_name=step,  # Stores 'step' value
            phase=axis_phase,
            status=axis_status,
            percent=progress.percent,
            completed=progress.completed,
            total=progress.total,
            pid=pid,
        )

    def is_complete(self) -> bool:
        """Check if this axis is complete.

        An axis is only complete when the entire axis finishes, not individual steps.
        This ensures progress is included in averages until the axis truly completes.
        """
        import logging

        logger = logging.getLogger(__name__)

        # Special case: Compilation step
        # Compilation is NOT considered "complete" for cleanup purposes!
        # Compilation is just a preparation phase - the actual execution happens AFTER compilation.
        # If we mark compilation as complete, the execution gets deleted before workers start!
        if self.step_name == "compilation":
            logger.info(
                f"AxisProgress.is_complete() [COMPILATION]: axis={self.axis_id}, "
                f"percent={self.percent}, status={self.status.value}, "
                f"phase={self.phase.value}, result=False (compilation never complete)"
            )
            return False

        # For pipeline execution: Only AXIS_COMPLETED phase means the axis is truly done
        # STEP_COMPLETED just means one step finished, not the whole axis
        phase_complete = self.phase == AxisPhase.AXIS_COMPLETED
        status_complete = self.status == AxisStatus.SUCCESS

        # percent >= 100 is NOT sufficient - a step can be 100% while axis continues
        result = phase_complete or status_complete

        return result

    def display_text(self, plate_id: str) -> str:
        """Generate display text for tree widget."""
        return f"  {plate_id} [{self.axis_id}]"

    def status_text(self) -> str:
        """Generate status text with emoji."""
        return f"{status_emoji(self.status)} {self.step_name}"

    def info_text(self) -> str:
        """Generate info text with progress details."""
        return f"{self.percent:.0f}% ({self.completed}/{self.total} {self.phase.value})"

    def to_tree_item(self) -> QTreeWidgetItem:
        """Create a QTreeWidgetItem for display in the server tree."""
        progress_text = self.display_text(self.plate_id)
        progress_status = self.status_text()
        progress_info = self.info_text()

        item = QTreeWidgetItem([progress_text, progress_status, progress_info])
        item.setData(
            0,
            Qt.ItemDataRole.UserRole,
            {
                "type": "progress",
                "execution_id": self.execution_id,
                "plate_id": self.plate_id,
                "axis_id": self.axis_id,
            },
        )
        return item


@dataclass
class PlateProgress:
    """Progress tracking for a plate within an execution."""

    execution_id: str
    plate_id: str
    axes: Dict[str, AxisProgress] = field(default_factory=dict)

    def add_axis_progress(self, progress: AxisProgress) -> None:
        """Add or update axis progress."""
        self.axes[progress.axis_id] = progress

    def clear_axes(self) -> None:
        """Clear all axes for this plate.

        Use when switching from compilation to execution phase.
        """
        self.axes.clear()

    def get_sorted_axes(self, include_compilation: bool = False) -> List[AxisProgress]:
        """Get axes sorted by completion status.

        Args:
            include_compilation: If False, filters out compilation axes (compile, init, axis_started, step_started phases).
        """
        axes_to_sort = self.axes.values()

        # Filter out compilation axes if requested
        # Compilation phases include: compile, init, axis_started, step_started
        if not include_compilation:
            compilation_phase_values = {
                AxisPhase.COMPILE.value,
                AxisPhase.INIT.value,
                AxisPhase.AXIS_STARTED.value,
                AxisPhase.STEP_STARTED.value,
            }
            axes_to_sort = [
                ax for ax in axes_to_sort if ax.phase not in compilation_phase_values
            ]

        return sorted(axes_to_sort, key=lambda p: (p.is_complete(), p.axis_id))

    def clear_compilation_axes(self) -> None:
        """Clear all axes with compilation phase (compile, init).

        Call when transitioning from compilation to execution phase.
        """
        axes_to_remove = [
            axis_id
            for axis_id, axis in self.axes.items()
            if axis.phase in [AxisPhase.COMPILE, AxisPhase.INIT]
        ]

        for axis_id in axes_to_remove:
            del self.axes[axis_id]

        logger.debug(
            f"PlateProgress.clear_compilation_axes(): Cleared {len(axes_to_remove)} compilation axes, "
            f"remaining axes: {list(self.axes.keys())}"
        )

    def is_complete(self) -> bool:
        """Check if all axes in this plate are complete."""
        import logging

        logger = logging.getLogger(__name__)

        for axis in self.axes.values():
            if not axis.is_complete():
                logger.debug(
                    f"PlateProgress.is_complete(): plate={self.plate_id} not complete because "
                    f"axis={axis.axis_id}, step={axis.step_name}, percent={axis.percent}, "
                    f"phase={axis.phase.value}, status={axis.status.value} is not complete"
                )
                return False
        return True


@dataclass
class ExecutionProgress:
    """Progress tracking for an execution."""

    execution_id: str
    plates: Dict[str, PlateProgress] = field(default_factory=dict)
    completed_at: Optional[float] = None  # Timestamp when execution completed
    total_wells: List[str] = field(
        default_factory=list
    )  # All wells from compiled_contexts

    def set_total_wells(self, wells: List[str], plate_id: str) -> None:
        """Set total well list and initialize all wells as queued."""
        import logging

        logger = logging.getLogger(__name__)

        logger.info(
            f"TRACE: set_total_wells BEFORE: self.total_wells={self.total_wells}, id(self)={id(self)}"
        )
        self.total_wells = wells
        logger.info(
            f"TRACE: set_total_wells AFTER: self.total_wells={self.total_wells}, id(self)={id(self)}"
        )
        logger.info(
            f"Progress tracker: Execution {self.execution_id} set_total_wells: {wells}"
        )

        # Ensure plate exists
        if plate_id not in self.plates:
            self.plates[plate_id] = PlateProgress(
                execution_id=self.execution_id, plate_id=plate_id
            )

        # Initialize all wells as queued if they don't exist yet
        # Wells will be updated to running/completed as progress comes in
        for well_id in wells:
            if well_id not in self.plates[plate_id].axes:
                logger.debug(f"Initializing queued well: {well_id}")
                # Create a placeholder queued entry
                # Use a special AxisProgress to represent "queued" state
                from zmqruntime.messages import TaskProgress, TaskPhase, TaskStatus
                import time

                queued_progress = TaskProgress(
                    task_id=self.execution_id,
                    percent=0.0,
                    completed=0,
                    total=1,
                    phase=TaskPhase.QUEUED,
                    status=TaskStatus.PENDING,
                    plate_id=plate_id,
                    axis_id=well_id,
                    timestamp=time.time(),
                    context={
                        "step": "queued",
                        "app_phase": "queued",
                        "app_status": "queued",
                    },
                )
                self.plates[plate_id].add_axis_progress(
                    AxisProgress.from_task_progress(queued_progress)
                )

    def add_update(self, update: TaskProgress) -> None:
        """Add generic TaskProgress update."""
        import logging
        import time

        logger = logging.getLogger(__name__)

        # DEBUG: Log incoming update
        logger.debug(
            f"add_update: execution_id={update.task_id}, step={update.context.get('step')}, "
            f"context_keys={list(update.context.keys())}, total_wells in context={'total_wells' in update.context}"
        )

        # Handle total_wells from compilation messages
        total_wells = update.context.get("total_wells")
        if total_wells and isinstance(total_wells, list):
            logger.info(f"add_update: Found total_wells in context: {total_wells}")
            self.set_total_wells(total_wells, update.plate_id)
        else:
            logger.debug(
                f"add_update: No total_wells found (total_wells={total_wells})"
            )

        plate_id = update.plate_id
        if plate_id not in self.plates:
            self.plates[plate_id] = PlateProgress(
                execution_id=self.execution_id, plate_id=plate_id
            )

        self.plates[plate_id].add_axis_progress(AxisProgress.from_task_progress(update))

        # Mark completion timestamp
        if self.is_complete() and self.completed_at is None:
            self.completed_at = time.time()
            logger.info(
                f"Progress tracker: Execution {self.execution_id} marked complete at {self.completed_at}"
            )

    def is_complete(self) -> bool:
        """Check if entire execution is complete."""
        import logging

        logger = logging.getLogger(__name__)

        result = all(p.is_complete() for p in self.plates.values())
        logger.info(
            f"TRACE: ExecutionProgress.is_complete() for {self.execution_id}: result={result}, plates={len(self.plates)}, total_wells={self.total_wells}"
        )
        return result

    def should_cleanup(self, retention_seconds: float = 5.0) -> bool:
        """Check if this execution should be cleaned up (completed + retention period elapsed)."""
        import time

        if not self.is_complete():
            return False
        if self.completed_at is None:
            return False
        return (time.time() - self.completed_at) > retention_seconds

    def get_all_axes(self) -> List[AxisProgress]:
        """Get all axis progress across all plates."""
        all_axes = []
        for plate in self.plates.values():
            all_axes.extend(plate.get_sorted_axes())
        return all_axes


class ExecutionProgressTracker:
    """Tracker for all active executions.

    Singleton pattern ensures all UI components share the same progress data.
    """

    _instance: Optional["ExecutionProgressTracker"] = None
    _lock = None  # Will be initialized on first use

    def __new__(cls):
        """Singleton pattern - only one instance exists."""
        if cls._instance is None:
            import threading

            if cls._lock is None:
                cls._lock = threading.Lock()
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
                    cls._instance._initialized = False
        return cls._instance

    def __init__(self):
        """Initialize only once."""
        if hasattr(self, "_initialized") and self._initialized:
            return
        self.executions: Dict[str, ExecutionProgress] = {}
        self._initialized = True

    @classmethod
    def get_instance(cls) -> "ExecutionProgressTracker":
        """Get the singleton instance (explicit alternative to __new__)."""
        return cls()

    def add_message(self, message: dict) -> None:
        """Add progress message from ZMQ.

        Filters out pipeline-level progress (empty axis_id) at the source,
        except for compilation messages which contain total_wells list.
        """
        import logging

        logger = logging.getLogger(__name__)

        # Parse dict to generic TaskProgress at boundary
        progress = TaskProgress.from_dict(message)
        execution_id = progress.task_id

        # Filter out pipeline-level progress (empty axis_id) at SOURCE
        # These are not actual wells and shouldn't create AxisProgress objects
        # EXCEPTION: compilation messages may contain total_wells list
        axis_id = progress.axis_id
        step = progress.context["step"]
        total_wells = progress.context.get("total_wells")
        plate_id = progress.plate_id

        # Log what we received
        logger.info(
            f"Progress tracker: Received message for {execution_id} - "
            f"step={step}, axis={axis_id}, plate={plate_id}, "
            f"percent={progress.percent}, total_wells={total_wells}, "
            f"context_keys={list(progress.context.keys())}"
        )

        # Allow through if: has axis_id OR has total_wells info
        if not axis_id and not total_wells:
            logger.debug(
                f"Skipping pipeline-level progress for {execution_id}: step={step}"
            )
            return execution_id

        if execution_id not in self.executions:
            logger.info(f"Progress tracker: Creating new execution {execution_id}")
            self.executions[execution_id] = ExecutionProgress(execution_id=execution_id)

        if total_wells:
            logger.info(
                f"Progress tracker: Received total_wells for {execution_id}: {total_wells}"
            )

        logger.info(
            f"Progress tracker: Adding update for {execution_id} - "
            f"step={step}, axis={axis_id}, "
            f"plate={plate_id}, percent={progress.percent}, "
            f"total_wells={total_wells}"
        )
        self.executions[execution_id].add_update(progress)

        # Cleanup completed executions after 3 second delay
        if self.executions[execution_id].should_cleanup(retention_seconds=3.0):
            import time

            elapsed = (
                time.time() - self.executions[execution_id].completed_at
                if self.executions[execution_id].completed_at
                else 0
            )
            logger.info(
                f"Progress tracker: Execution {execution_id} cleanup check: is_complete={self.executions[execution_id].is_complete()}, completed_at={self.executions[execution_id].completed_at}, elapsed={elapsed:.1f}s"
            )
            logger.info(
                f"Progress tracker: Deleting execution {execution_id} after {elapsed:.1f}s"
            )
            del self.executions[execution_id]
        else:
            logger.info(
                f"Progress tracker: Execution {execution_id} has {len(self.executions[execution_id].plates)} plates, "
                f"{sum(len(p.axes) for p in self.executions[execution_id].plates.values())} axes"
            )

        return execution_id

    def cleanup_old_executions(self, retention_seconds: float = 5.0) -> None:
        """Remove executions that have been complete for longer than retention period."""
        import logging
        import time

        logger = logging.getLogger(__name__)

        logger.info(
            f"Progress tracker: cleanup_old_executions() called with retention_seconds={retention_seconds}, "
            f"checking {len(self.executions)} executions"
        )

        to_delete = []
        for exec_id, execution in self.executions.items():
            should_cleanup = execution.should_cleanup(retention_seconds)
            is_complete = execution.is_complete()
            completed_at = execution.completed_at

            logger.info(
                f"  Checking {exec_id[:8]}: is_complete={is_complete}, should_cleanup={should_cleanup}, "
                f"completed_at={completed_at}"
            )

            if completed_at:
                elapsed = time.time() - completed_at
                logger.info(
                    f"    Elapsed: {elapsed:.1f}s (retention: {retention_seconds}s)"
                )

            if should_cleanup:
                to_delete.append(exec_id)

        logger.info(f"  Found {len(to_delete)} executions to delete")

        for exec_id in to_delete:
            logger.info(f"Progress tracker: Cleaning up old execution {exec_id}")
            del self.executions[exec_id]

    def get_all_progress(self) -> List[AxisProgress]:
        """Get all active axis progress across all executions."""
        import logging

        logger = logging.getLogger(__name__)

        all_progress = []
        for execution in self.executions.values():
            all_progress.extend(execution.get_all_axes())

        logger.info(
            f"Progress tracker: get_all_progress() returning {len(all_progress)} axes "
            f"from {len(self.executions)} executions"
        )
        return all_progress

    def clear(self) -> None:
        """Clear all progress state."""
        self.executions.clear()
