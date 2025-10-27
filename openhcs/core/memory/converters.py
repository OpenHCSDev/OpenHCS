"""Memory conversion public API for OpenHCS."""

from typing import Any
import numpy as np
from openhcs.constants.constants import MemoryType
from openhcs.core.memory.conversion_helpers import _CONVERTERS
from openhcs.core.memory.framework_config import _FRAMEWORK_CONFIG


def convert_memory(data: Any, source_type: str, target_type: str, gpu_id: int) -> Any:
    """
    Convert data between memory types using the unified converter infrastructure.

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
    converter = _CONVERTERS[source_enum]
    method = getattr(converter, f"to_{target_type}")
    return method(data, gpu_id)


def detect_memory_type(data: Any) -> str:
    """
    Detect the memory type of data using framework config.

    Args:
        data: The data to detect

    Returns:
        The detected memory type string (e.g., "numpy", "torch")

    Raises:
        ValueError: If memory type cannot be detected
    """
    # NumPy special case (most common, check first)
    if isinstance(data, np.ndarray):
        return MemoryType.NUMPY.value

    # Check all frameworks using their module names from config
    module_name = type(data).__module__

    for mem_type, config in _FRAMEWORK_CONFIG.items():
        import_name = config['import_name']
        # Check if module name starts with or contains the import name
        if module_name.startswith(import_name) or import_name in module_name:
            return mem_type.value

    raise ValueError(f"Unknown memory type for {type(data)} (module: {module_name})")
