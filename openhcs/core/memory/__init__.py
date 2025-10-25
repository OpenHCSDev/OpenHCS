"""Memory module for OpenHCS."""

from openhcs.constants.constants import MemoryType
from .decorators import cupy, jax, memory_types, numpy, tensorflow, torch
from .converters import convert_memory, detect_memory_type

# Define memory type constants
MEMORY_TYPE_NUMPY = MemoryType.NUMPY.value
MEMORY_TYPE_CUPY = MemoryType.CUPY.value
MEMORY_TYPE_TORCH = MemoryType.TORCH.value
MEMORY_TYPE_TENSORFLOW = MemoryType.TENSORFLOW.value
MEMORY_TYPE_JAX = MemoryType.JAX.value
MEMORY_TYPE_PYCLESPERANTO = MemoryType.PYCLESPERANTO.value

__all__ = [
    'convert_memory',
    'detect_memory_type',
    'MEMORY_TYPE_NUMPY',
    'MEMORY_TYPE_CUPY',
    'MEMORY_TYPE_TORCH',
    'MEMORY_TYPE_TENSORFLOW',
    'MEMORY_TYPE_JAX',
    'MEMORY_TYPE_PYCLESPERANTO',
    'memory_types',
    'numpy',
    'cupy',
    'torch',
    'tensorflow',
    'jax',
]
