"""Memory conversion public API for OpenHCS."""

from typing import Any
import numpy as np
from openhcs.constants.constants import MemoryType


def convert_memory(data: Any, source_type: str, target_type: str, gpu_id: int) -> Any:
    """
    Convert data between memory types.

    Args:
        data: The data to convert
        source_type: The source memory type (e.g., "numpy", "torch")
        target_type: The target memory type (e.g., "cupy", "jax")
        gpu_id: The target GPU device ID

    Returns:
        The converted data in the target memory type

    Raises:
        ValueError: If source_type or target_type is invalid
        MemoryConversionError: If conversion fails
    """
    source_enum = MemoryType(source_type)
    return getattr(source_enum, f"to_{target_type}")(data, gpu_id)


def detect_memory_type(data: Any) -> str:
    """
    Detect the memory type of data.

    Args:
        data: The data to detect

    Returns:
        The detected memory type string (e.g., "numpy", "torch")

    Raises:
        ValueError: If memory type cannot be detected
    """
    # NumPy
    if isinstance(data, np.ndarray):
        return MemoryType.NUMPY.value

    # CuPy
    if type(data).__module__.startswith('cupy'):
        return MemoryType.CUPY.value

    # PyTorch
    if type(data).__module__.startswith('torch'):
        return MemoryType.TORCH.value

    # TensorFlow
    if 'tensorflow' in type(data).__module__:
        return MemoryType.TENSORFLOW.value

    # JAX
    if type(data).__module__.startswith('jax'):
        return MemoryType.JAX.value

    # pyclesperanto
    if 'pyclesperanto' in type(data).__module__:
        return MemoryType.PYCLESPERANTO.value

    raise ValueError(f"Unknown memory type for {type(data)}")
