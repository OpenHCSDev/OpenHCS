"""
Consolidated constants for OpenHCS.

This module defines all constants related to backends, defaults, I/O, memory, and pipeline.
These constants are governed by various doctrinal clauses.
"""

from enum import Enum
from typing import Any, Callable, Dict, List, Optional, Set, TypeVar

class VariableComponents(Enum):
    SITE = "site"
    CHANNEL = "channel"
    Z_INDEX = "z_index"
    WELL = "well"

class Microscope(Enum):
    AUTO = "auto"
    OPENHCS = "openhcs"  # Added for the OpenHCS pre-processed format
    IMAGEXPRESS = "ImageXpress"
    OPERAPHENIX = "OperaPhenix"

class GroupBy(Enum):
    """
    Enum wrapper around VariableComponents for grouping operations.

    This eliminates the need for separate enum definitions and conversion logic
    while maintaining type safety, backward compatibility, and proper enum detection.
    """

    # Use VariableComponents as enum values for direct wrapping
    CHANNEL = VariableComponents.CHANNEL
    SITE = VariableComponents.SITE
    WELL = VariableComponents.WELL
    Z_INDEX = VariableComponents.Z_INDEX
    NONE = None  # Special case for "no grouping"

    @property
    def component(self) -> Optional[VariableComponents]:
        """Get the wrapped VariableComponents enum."""
        return self.value

    @classmethod
    def from_string(cls, component_type: str) -> Optional['GroupBy']:
        """
        Create GroupBy enum from string value.

        Provides a clean, unified lookup mechanism that encapsulates the conversion logic
        within the enum class itself, eliminating the need for manual iteration and
        nested conditionals in calling code.

        Args:
            component_type: String value to convert (e.g., "channel", "site", "well")

        Returns:
            Matching GroupBy enum member, or None if no match found

        Examples:
            >>> GroupBy.from_string("channel")
            <GroupBy.CHANNEL: VariableComponents.CHANNEL>
            >>> GroupBy.from_string("invalid")
            None
        """
        if not component_type:
            return cls.NONE

        for group_by in cls:
            if group_by.value is not None and group_by.value.value == component_type:
                return group_by

        return None

    def __eq__(self, other):
        """Support equality with both GroupBy and VariableComponents."""
        if isinstance(other, GroupBy):
            return self.value == other.value
        elif isinstance(other, VariableComponents):
            return self.value == other
        return False

    def __hash__(self):
        """
        Delegate hashing to the wrapped VariableComponents enum.

        This ensures GroupBy enum members are hashable and can be used as dictionary keys.
        For GroupBy.NONE (value=None), we use a consistent hash value.

        Hash consistency:
        - GroupBy.CHANNEL and VariableComponents.CHANNEL have the same hash
        - GroupBy.NONE has a unique, consistent hash value
        """
        if self.value is None:
            # Use a consistent hash for GroupBy.NONE
            return hash("GroupBy.NONE")
        else:
            # Delegate to the wrapped VariableComponents enum's hash
            return hash(self.value)

    def __str__(self):
        """String representation for debugging."""
        return f"GroupBy.{self.name}"

    def __repr__(self):
        """Detailed representation for debugging."""
        return f"GroupBy.{self.name}"

class OrchestratorState(Enum):
    """Simple orchestrator state tracking - no complex state machine."""
    CREATED = "created"         # Object exists, not initialized
    READY = "ready"             # Initialized, ready for compilation
    COMPILED = "compiled"       # Compilation complete, ready for execution
    EXECUTING = "executing"     # Execution in progress
    COMPLETED = "completed"     # Execution completed successfully
    INIT_FAILED = "init_failed"       # Initialization failed
    COMPILE_FAILED = "compile_failed" # Compilation failed (implies initialized)
    EXEC_FAILED = "exec_failed"       # Execution failed (implies compiled)

# I/O-related constants
DEFAULT_IMAGE_EXTENSION = ".tif"
DEFAULT_IMAGE_EXTENSIONS: Set[str] = {".tif", ".tiff", ".TIF", ".TIFF"}
DEFAULT_SITE_PADDING = 3
DEFAULT_RECURSIVE_PATTERN_SEARCH = False
DEFAULT_VARIABLE_COMPONENTS: List[VariableComponents] = [VariableComponents.SITE]
DEFAULT_GROUP_BY: GroupBy = GroupBy.CHANNEL
DEFAULT_MICROSCOPE: Microscope = Microscope.AUTO

# Generic component configuration system
# This provides the new configurable component system while maintaining backward compatibility
# Using lazy initialization to avoid circular imports
OPENHCS_CONFIG = None

def get_openhcs_config():
    """Get the OpenHCS configuration, initializing it if needed."""
    global OPENHCS_CONFIG
    if OPENHCS_CONFIG is None:
        try:
            from openhcs.core.components.framework import ComponentConfigurationFactory
            OPENHCS_CONFIG = ComponentConfigurationFactory.create_openhcs_default_configuration()
        except ImportError:
            # Fallback for cases where the new system isn't available yet
            OPENHCS_CONFIG = None
        except Exception:
            # Fallback for any other errors (like circular imports)
            OPENHCS_CONFIG = None
    return OPENHCS_CONFIG

# Don't initialize on module load to avoid circular imports
# OPENHCS_CONFIG will be None until get_openhcs_config() is called



# Backend-related constants
class Backend(Enum):
    DISK = "disk"
    MEMORY = "memory"
    ZARR = "zarr"

class FileFormat(Enum):
    TIFF = list(DEFAULT_IMAGE_EXTENSIONS)
    NUMPY = [".npy"]
    TORCH = [".pt", ".torch", ".pth"]
    JAX = [".jax"]
    CUPY = [".cupy",".craw"]
    TENSORFLOW = [".tf"]
    TEXT = [".txt",".csv",".json",".py",".md"]

DEFAULT_BACKEND = Backend.MEMORY
REQUIRES_DISK_READ = "requires_disk_read"
REQUIRES_DISK_WRITE = "requires_disk_write"
FORCE_DISK_WRITE = "force_disk_write"
READ_BACKEND = "read_backend"
WRITE_BACKEND = "write_backend"

# Default values
DEFAULT_TILE_OVERLAP = 10.0
DEFAULT_MAX_SHIFT = 50
DEFAULT_MARGIN_RATIO = 0.1
DEFAULT_PIXEL_SIZE = 1.0
DEFAULT_ASSEMBLER_LOG_LEVEL = "INFO"
DEFAULT_INTERPOLATION_MODE = "nearest"
DEFAULT_INTERPOLATION_ORDER = 1
DEFAULT_CPU_THREAD_COUNT = 4
DEFAULT_PATCH_SIZE = 128
DEFAULT_SEARCH_RADIUS = 20
# Consolidated definition for CPU thread count


# Memory-related constants
T = TypeVar('T')
ConversionFunc = Callable[[Any], Any]

class MemoryType(Enum):
    NUMPY = "numpy"
    CUPY = "cupy"
    TORCH = "torch"
    TENSORFLOW = "tensorflow"
    JAX = "jax"
    PYCLESPERANTO = "pyclesperanto"

CPU_MEMORY_TYPES: Set[MemoryType] = {MemoryType.NUMPY}
GPU_MEMORY_TYPES: Set[MemoryType] = {
    MemoryType.CUPY,
    MemoryType.TORCH,
    MemoryType.TENSORFLOW,
    MemoryType.JAX,
    MemoryType.PYCLESPERANTO
}
SUPPORTED_MEMORY_TYPES: Set[MemoryType] = CPU_MEMORY_TYPES | GPU_MEMORY_TYPES

VALID_MEMORY_TYPES = {mt.value for mt in MemoryType}
VALID_GPU_MEMORY_TYPES = {mt.value for mt in GPU_MEMORY_TYPES}

# Memory type constants for direct access
MEMORY_TYPE_NUMPY = MemoryType.NUMPY.value
MEMORY_TYPE_CUPY = MemoryType.CUPY.value
MEMORY_TYPE_TORCH = MemoryType.TORCH.value
MEMORY_TYPE_TENSORFLOW = MemoryType.TENSORFLOW.value
MEMORY_TYPE_JAX = MemoryType.JAX.value
MEMORY_TYPE_PYCLESPERANTO = MemoryType.PYCLESPERANTO.value

DEFAULT_NUM_WORKERS = 1
# Consolidated definition for number of workers
DEFAULT_OUT_DIR_SUFFIX = "_out"
DEFAULT_POSITIONS_DIR_SUFFIX = "_positions"
DEFAULT_STITCHED_DIR_SUFFIX = "_stitched"
DEFAULT_WORKSPACE_DIR_SUFFIX = "_workspace"