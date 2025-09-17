"""
Consolidated constants for OpenHCS.

This module defines all constants related to backends, defaults, I/O, memory, and pipeline.
These constants are governed by various doctrinal clauses.
"""

from enum import Enum
from functools import lru_cache
from typing import Any, Callable, Dict, List, Optional, Set, Type, TypeVar


class Microscope(Enum):
    AUTO = "auto"
    OPENHCS = "openhcs"  # Added for the OpenHCS pre-processed format
    IMAGEXPRESS = "ImageXpress"
    OPERAPHENIX = "OperaPhenix"


def get_openhcs_config():
    """Get the OpenHCS configuration, initializing it if needed."""
    from openhcs.core.components.framework import ComponentConfigurationFactory
    return ComponentConfigurationFactory.create_openhcs_default_configuration()


# Simple lazy initialization - just defer the config call
@lru_cache(maxsize=1)
def _create_enums():
    """Create enums when first needed."""
    config = get_openhcs_config()
    remaining = config.get_remaining_components()

    # AllComponents: ALL possible dimensions (including multiprocessing axis)
    all_components = Enum('AllComponents', {c.name: c.value for c in config.all_components})

    # VariableComponents: Components available for variable selection (excludes multiprocessing axis)
    vc = Enum('VariableComponents', {c.name: c.value for c in remaining})

    # GroupBy: Same as VariableComponents + NONE option (they're the same concept)
    gb_dict = {c.name: c.value for c in remaining}
    gb_dict['NONE'] = None
    GroupBy = Enum('GroupBy', gb_dict)

    # Add original interface methods
    GroupBy.component = property(lambda self: self.value)
    GroupBy.__eq__ = lambda self, other: self.value == getattr(other, 'value', other)
    GroupBy.__hash__ = lambda self: hash("GroupBy.NONE") if self.value is None else hash(self.value)
    GroupBy.__str__ = lambda self: f"GroupBy.{self.name}"
    GroupBy.__repr__ = lambda self: f"GroupBy.{self.name}"

    return all_components, vc, GroupBy


def __getattr__(name):
    """Lazy enum creation."""
    if name in ('AllComponents', 'VariableComponents', 'GroupBy'):
        all_components, vc, gb = _create_enums()
        globals()['AllComponents'] = all_components
        globals()['VariableComponents'] = vc
        globals()['GroupBy'] = gb
        return globals()[name]
    raise AttributeError(f"module '{__name__}' has no attribute '{name}'")





#Documentation URL
DOCUMENTATION_URL = "https://openhcs.readthedocs.io/en/latest/"


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
# Lazy default resolution using lru_cache
@lru_cache(maxsize=1)
def get_default_variable_components():
    """Get default variable components from ComponentConfiguration."""
    _, vc, _ = _create_enums()  # Get the enum directly
    return [getattr(vc, c.name) for c in get_openhcs_config().default_variable]


@lru_cache(maxsize=1)
def get_default_group_by():
    """Get default group_by from ComponentConfiguration."""
    _, _, gb = _create_enums()  # Get the enum directly
    config = get_openhcs_config()
    return getattr(gb, config.default_group_by.name) if config.default_group_by else None

@lru_cache(maxsize=1)
def get_multiprocessing_axis():
    """Get multiprocessing axis from ComponentConfiguration."""
    config = get_openhcs_config()
    return config.multiprocessing_axis

DEFAULT_MICROSCOPE: Microscope = Microscope.AUTO





# Backend-related constants
class Backend(Enum):
    AUTO = "auto"
    DISK = "disk"
    MEMORY = "memory"
    ZARR = "zarr"
    NAPARI_STREAM = "napari_stream"
    FIJI_STREAM = "fiji_stream"

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

# Napari streaming constants
DEFAULT_NAPARI_STREAM_PORT = 5555


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