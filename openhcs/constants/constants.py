"""
Consolidated constants for OpenHCS.

This module defines all constants related to backends, defaults, I/O, memory, and pipeline.
These constants are governed by various doctrinal clauses.
"""

from enum import Enum
from functools import lru_cache
from typing import Any, Callable, Set, TypeVar


class Microscope(Enum):
    AUTO = "auto"
    OPENHCS = "openhcs"  # Added for the OpenHCS pre-processed format
    IMAGEXPRESS = "ImageXpress"
    OPERAPHENIX = "OperaPhenix"
    OMERO = "omero"  # Added for OMERO virtual filesystem backend


class VirtualComponents(Enum):
    """Components that don't come from filename parsing but from execution/location context."""
    STEP_NAME = "step_name"
    STEP_INDEX = "step_index"
    SOURCE = "source"  # Parent directory/plate name


def get_openhcs_config():
    """Get the OpenHCS configuration, initializing it if needed."""
    from openhcs.components.framework import ComponentConfigurationFactory
    return ComponentConfigurationFactory.create_openhcs_default_configuration()


# Simple lazy initialization - just defer the config call
@lru_cache(maxsize=1)
def _create_enums():
    """Create enums when first needed.

    CRITICAL: This function must create enums with proper __module__ and __qualname__
    attributes so they can be pickled correctly in multiprocessing contexts.
    The enums are stored in module globals() to ensure identity consistency.
    """
    import logging
    import os
    import traceback
    logger = logging.getLogger(__name__)
    logger.info(f"🔧 _create_enums() CALLED in process {os.getpid()}")
    logger.info(f"🔧 _create_enums() cache_info: {_create_enums.cache_info()}")
    logger.info(f"🔧 _create_enums() STACK TRACE:\n{''.join(traceback.format_stack())}")

    config = get_openhcs_config()
    remaining = config.get_remaining_components()

    # AllComponents: ALL possible dimensions (including multiprocessing axis)
    all_components = Enum('AllComponents', {c.name: c.value for c in config.all_components})
    all_components.__module__ = __name__
    all_components.__qualname__ = 'AllComponents'

    # VariableComponents: Components available for variable selection (excludes multiprocessing axis)
    vc = Enum('VariableComponents', {c.name: c.value for c in remaining})
    vc.__module__ = __name__
    vc.__qualname__ = 'VariableComponents'

    # GroupBy: Same as VariableComponents + NONE option (they're the same concept)
    gb_dict = {c.name: c.value for c in remaining}
    gb_dict['NONE'] = None
    GroupBy = Enum('GroupBy', gb_dict)
    GroupBy.__module__ = __name__
    GroupBy.__qualname__ = 'GroupBy'

    # Add original interface methods
    GroupBy.component = property(lambda self: self.value)
    GroupBy.__eq__ = lambda self, other: self.value == getattr(other, 'value', other)
    GroupBy.__hash__ = lambda self: hash("GroupBy.NONE") if self.value is None else hash(self.value)
    GroupBy.__str__ = lambda self: f"GroupBy.{self.name}"
    GroupBy.__repr__ = lambda self: f"GroupBy.{self.name}"

    logger.info(f"🔧 _create_enums() RETURNING in process {os.getpid()}: "
               f"AllComponents={id(all_components)}, VariableComponents={id(vc)}, GroupBy={id(GroupBy)}")
    logger.info(f"🔧 _create_enums() cache_info after return: {_create_enums.cache_info()}")
    return all_components, vc, GroupBy


@lru_cache(maxsize=1)
def _create_streaming_components():
    """Create StreamingComponents enum combining AllComponents + VirtualComponents.

    This enum includes both filename components (from parser) and virtual components
    (from execution/location context) for streaming visualization.
    """
    import logging
    import os
    logger = logging.getLogger(__name__)
    logger.info(f"🔧 _create_streaming_components() CALLED in process {os.getpid()}")

    # Import AllComponents (triggers lazy creation if needed)
    from openhcs.constants import AllComponents

    # Combine all component types
    components_dict = {c.name: c.value for c in AllComponents}
    components_dict.update({c.name: c.value for c in VirtualComponents})

    streaming_components = Enum('StreamingComponents', components_dict)
    streaming_components.__module__ = __name__
    streaming_components.__qualname__ = 'StreamingComponents'

    logger.info(f"🔧 _create_streaming_components() RETURNING: StreamingComponents={id(streaming_components)}")
    return streaming_components


def __getattr__(name):
    """Lazy enum creation with identity guarantee.

    CRITICAL: Ensures enums are created exactly once per process and stored in globals()
    so that pickle identity checks pass in multiprocessing contexts.
    """
    if name in ('AllComponents', 'VariableComponents', 'GroupBy'):
        # Check if already created (handles race conditions)
        if name in globals():
            return globals()[name]

        # Create all enums at once and store in globals
        import logging
        import os
        logger = logging.getLogger(__name__)
        logger.info(f"🔧 ENUM CREATION: Creating {name} in process {os.getpid()}")

        all_components, vc, gb = _create_enums()
        globals()['AllComponents'] = all_components
        globals()['VariableComponents'] = vc
        globals()['GroupBy'] = gb

        logger.info(f"🔧 ENUM CREATION: Created enums in process {os.getpid()}: "
                   f"AllComponents={id(all_components)}, VariableComponents={id(vc)}, GroupBy={id(gb)}")
        logger.info(f"🔧 ENUM CREATION: VariableComponents.__module__={vc.__module__}, __qualname__={vc.__qualname__}")

        return globals()[name]

    if name == 'StreamingComponents':
        # Check if already created
        if name in globals():
            return globals()[name]

        import logging
        import os
        logger = logging.getLogger(__name__)
        logger.info(f"🔧 ENUM CREATION: Creating StreamingComponents in process {os.getpid()}")

        streaming_components = _create_streaming_components()
        globals()['StreamingComponents'] = streaming_components

        logger.info(f"🔧 ENUM CREATION: Created StreamingComponents in process {os.getpid()}: "
                   f"StreamingComponents={id(streaming_components)}")

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
    OMERO_LOCAL = "omero_local"
    VIRTUAL_WORKSPACE = "virtual_workspace"

class FileFormat(Enum):
    TIFF = list(DEFAULT_IMAGE_EXTENSIONS)
    NUMPY = [".npy"]
    TORCH = [".pt", ".torch", ".pth"]
    JAX = [".jax"]
    CUPY = [".cupy",".craw"]
    TENSORFLOW = [".tf"]
    JSON = [".json"]
    CSV = [".csv"]
    TEXT = [".txt", ".py", ".md"]
    ROI = [".roi.zip"]

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

# Streaming viewer constants
DEFAULT_NAPARI_STREAM_PORT = 5555
DEFAULT_FIJI_STREAM_PORT = 5565  # Non-overlapping with Napari (5555-5564)


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
