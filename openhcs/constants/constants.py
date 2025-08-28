"""
Consolidated constants for OpenHCS.

This module defines all constants related to backends, defaults, I/O, memory, and pipeline.
These constants are governed by various doctrinal clauses.
"""

from enum import Enum
from typing import Any, Callable, Dict, List, Optional, Set, Type, TypeVar


class Microscope(Enum):
    AUTO = "auto"
    OPENHCS = "openhcs"  # Added for the OpenHCS pre-processed format
    IMAGEXPRESS = "ImageXpress"
    OPERAPHENIX = "OperaPhenix"


# Direct filtered enum definitions using ComponentConfiguration
def get_openhcs_config():
    """Get the OpenHCS configuration, initializing it if needed."""
    from openhcs.core.components.framework import ComponentConfigurationFactory
    return ComponentConfigurationFactory.create_openhcs_default_configuration()


def _create_filtered_variable_components():
    """Create VariableComponents enum with multiprocessing axis filtered out."""
    config = get_openhcs_config()
    remaining = config.get_remaining_components()

    # Create enum dict
    enum_dict = {}
    for comp in remaining:
        enum_dict[comp.name] = comp.value

    # Create the enum class
    FilteredVariableComponents = Enum('FilteredVariableComponents', enum_dict)

    return FilteredVariableComponents


def _create_filtered_group_by():
    """Create GroupBy enum with multiprocessing axis filtered out."""
    config = get_openhcs_config()
    remaining = config.get_remaining_components()

    # Create enum dict with VariableComponents as values
    enum_dict = {}
    for comp in remaining:
        enum_dict[comp.name] = comp
    enum_dict['NONE'] = None

    # Create the base enum class
    FilteredGroupBy = Enum('FilteredGroupBy', enum_dict)

    # Add the special methods to the enum class
    def component(self) -> Optional:
        """Get the wrapped VariableComponents enum."""
        return self.value

    def __eq__(self, other):
        """Support equality with both GroupBy and VariableComponents."""
        if isinstance(other, FilteredGroupBy):
            return self.value == other.value
        elif hasattr(other, 'value'):  # VariableComponents or similar enum
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

    # Add methods to the enum class
    FilteredGroupBy.component = property(component)
    FilteredGroupBy.__eq__ = __eq__
    FilteredGroupBy.__hash__ = __hash__
    FilteredGroupBy.__str__ = __str__
    FilteredGroupBy.__repr__ = __repr__

    return FilteredGroupBy


# Initialize the filtered enums directly
# This works because we've resolved the circular import by moving get_openhcs_config here
try:
    VariableComponents = _create_filtered_variable_components()
    GroupBy = _create_filtered_group_by()
except Exception:
    # If initialization fails during import, create fallback enums
    class VariableComponents(Enum):
        SITE = "site"
        CHANNEL = "channel"
        Z_INDEX = "z_index"

    class GroupBy(Enum):
        SITE = VariableComponents.SITE
        CHANNEL = VariableComponents.CHANNEL
        Z_INDEX = VariableComponents.Z_INDEX
        NONE = None





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
# Lazy defaults using ComponentConfiguration
_default_variable_components = None
_default_group_by = None


def get_default_variable_components():
    global _default_variable_components
    if _default_variable_components is None:
        config = get_openhcs_config()
        _default_variable_components = [getattr(VariableComponents, comp.name) for comp in config.default_variable]
    return _default_variable_components


def get_default_group_by():
    global _default_group_by
    if _default_group_by is None:
        config = get_openhcs_config()
        _default_group_by = getattr(GroupBy, config.default_group_by.name) if config.default_group_by else None
    return _default_group_by


# Note: DEFAULT_VARIABLE_COMPONENTS and DEFAULT_GROUP_BY are now functions
# to avoid circular imports. Use get_default_variable_components() and get_default_group_by()
DEFAULT_MICROSCOPE: Microscope = Microscope.AUTO





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