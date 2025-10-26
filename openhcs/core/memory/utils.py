"""
Memory conversion utility functions for OpenHCS.

This module provides utility functions for memory conversion operations,
supporting Clause 251 (Declarative Memory Conversion Interface) and
Clause 65 (Fail Loudly).
"""

import importlib
import logging
from typing import Any, Optional

from openhcs.constants.constants import MemoryType

from .exceptions import MemoryConversionError
from .framework_config import _FRAMEWORK_CONFIG

logger = logging.getLogger(__name__)


def _ensure_module(module_name: str) -> Any:
    """
    Ensure a module is imported and meets version requirements.

    Args:
        module_name: The name of the module to import

    Returns:
        The imported module

    Raises:
        ImportError: If the module cannot be imported or does not meet version requirements
        RuntimeError: If the module has known issues with specific versions
    """
    try:
        module = importlib.import_module(module_name)

        # Check TensorFlow version for DLPack compatibility
        if module_name == "tensorflow":
            import pkg_resources
            tf_version = pkg_resources.parse_version(module.__version__)
            min_version = pkg_resources.parse_version("2.12.0")

            if tf_version < min_version:
                raise RuntimeError(
                    f"TensorFlow version {module.__version__} is not supported for DLPack operations. "
                    f"Version 2.12.0 or higher is required for stable DLPack support. "
                    f"Clause 88 (No Inferred Capabilities) violation: Cannot infer DLPack capability."
                )

        return module
    except ImportError:
        raise ImportError(f"Module {module_name} is required for this operation but is not installed")


def _supports_cuda_array_interface(obj: Any) -> bool:
    """
    Check if an object supports the CUDA Array Interface.

    Args:
        obj: The object to check

    Returns:
        True if the object supports the CUDA Array Interface, False otherwise
    """
    return hasattr(obj, "__cuda_array_interface__")


def _supports_dlpack(obj: Any) -> bool:
    """
    Check if an object supports DLPack.

    Args:
        obj: The object to check

    Returns:
        True if the object supports DLPack, False otherwise

    Note:
        For TensorFlow tensors, this function enforces Clause 88 (No Inferred Capabilities)
        by explicitly checking:
        1. TensorFlow version must be 2.12+ for stable DLPack support
        2. Tensor must be on GPU (CPU tensors might succeed even without proper DLPack support)
        3. tf.experimental.dlpack module must exist
    """
    # Check for PyTorch, CuPy, or JAX DLPack support
    # PyTorch: __dlpack__ method, CuPy: toDlpack method, JAX: __dlpack__ method
    if hasattr(obj, "toDlpack") or hasattr(obj, "to_dlpack") or hasattr(obj, "__dlpack__"):
        # Special handling for TensorFlow to enforce Clause 88
        if 'tensorflow' in str(type(obj)):
            try:
                import tensorflow as tf

                # Check TensorFlow version - DLPack is only stable in TF 2.12+
                tf_version = tf.__version__
                major, minor = map(int, tf_version.split('.')[:2])

                if major < 2 or (major == 2 and minor < 12):
                    # Explicitly fail for TF < 2.12 to prevent silent fallbacks
                    raise RuntimeError(
                        f"TensorFlow version {tf_version} does not support stable DLPack operations. "
                        f"Version 2.12.0 or higher is required. "
                        f"Clause 88 violation: Cannot infer DLPack capability."
                    )

                # Check if tensor is on GPU - CPU tensors might succeed even without proper DLPack support
                device_str = obj.device.lower()
                if "gpu" not in device_str:
                    # Explicitly fail for CPU tensors to prevent deceptive behavior
                    raise RuntimeError(
                        "TensorFlow tensor on CPU cannot use DLPack operations reliably. "
                        "Only GPU tensors are supported for DLPack operations. "
                        "Clause 88 violation: Cannot infer GPU capability."
                    )

                # Check if experimental.dlpack module exists
                if not hasattr(tf.experimental, "dlpack"):
                    raise RuntimeError(
                        "TensorFlow installation missing experimental.dlpack module. "
                        "Clause 88 violation: Cannot infer DLPack capability."
                    )

                return True
            except (ImportError, AttributeError) as e:
                # Re-raise with more specific error message
                raise RuntimeError(
                    f"TensorFlow DLPack support check failed: {str(e)}. "
                    f"Clause 88 violation: Cannot infer DLPack capability."
                ) from e

        # For non-TensorFlow types, return True if they have DLPack methods
        return True

    return False


# NOTE: Device operations now defined in framework_config.py
# This eliminates the scattered _DEVICE_OPS dict


def _get_device_id(data: Any, memory_type: str) -> Optional[int]:
    """
    Get the GPU device ID from a data object using framework config.

    Args:
        data: The data object
        memory_type: The memory type

    Returns:
        The GPU device ID or None if not applicable

    Raises:
        MemoryConversionError: If the device ID cannot be determined for a GPU memory type
    """
    # Convert string to enum
    mem_type = MemoryType(memory_type)
    config = _FRAMEWORK_CONFIG[mem_type]
    get_id_handler = config['get_device_id']

    # Check if it's a callable handler (pyclesperanto)
    if callable(get_id_handler):
        mod = _ensure_module(mem_type.value)
        return get_id_handler(data, mod)

    # Check if it's None (CPU)
    if get_id_handler is None:
        return None

    # It's an eval expression
    try:
        mod = _ensure_module(mem_type.value)  # noqa: F841 (used in eval)
        return eval(get_id_handler)
    except (AttributeError, Exception) as e:
        logger.warning(f"Failed to get device ID for {mem_type.value} array: {e}")
        # Try fallback if available
        if 'get_device_id_fallback' in config:
            return eval(config['get_device_id_fallback'])


def _set_device(memory_type: str, device_id: int) -> None:
    """
    Set the current device for a specific memory type using framework config.

    Args:
        memory_type: The memory type
        device_id: The GPU device ID

    Raises:
        MemoryConversionError: If the device cannot be set
    """
    # Convert string to enum
    mem_type = MemoryType(memory_type)
    config = _FRAMEWORK_CONFIG[mem_type]
    set_device_handler = config['set_device']

    # Check if it's a callable handler (pyclesperanto)
    if callable(set_device_handler):
        try:
            mod = _ensure_module(mem_type.value)
            set_device_handler(device_id, mod)
        except Exception as e:
            raise MemoryConversionError(
                source_type=memory_type,
                target_type=memory_type,
                method="device_selection",
                reason=f"Failed to set {mem_type.value} device to {device_id}: {e}"
            ) from e
        return

    # Check if it's None (frameworks that don't need global device setting)
    if set_device_handler is None:
        return

    # It's an eval expression
    try:
        mod = _ensure_module(mem_type.value)  # noqa: F841 (used in eval)
        eval(set_device_handler.format(mod='mod'))
    except Exception as e:
        raise MemoryConversionError(
            source_type=memory_type,
            target_type=memory_type,
            method="device_selection",
            reason=f"Failed to set {mem_type.value} device to {device_id}: {e}"
        ) from e


def _move_to_device(data: Any, memory_type: str, device_id: int) -> Any:
    """
    Move data to a specific GPU device using framework config.

    Args:
        data: The data to move
        memory_type: The memory type
        device_id: The target GPU device ID

    Returns:
        The data on the target device

    Raises:
        MemoryConversionError: If the data cannot be moved to the specified device
    """
    # Convert string to enum
    mem_type = MemoryType(memory_type)
    config = _FRAMEWORK_CONFIG[mem_type]
    move_handler = config['move_to_device']

    # Check if it's a callable handler (pyclesperanto)
    if callable(move_handler):
        try:
            mod = _ensure_module(mem_type.value)
            return move_handler(data, device_id, mod, memory_type)
        except Exception as e:
            raise MemoryConversionError(
                source_type=memory_type,
                target_type=memory_type,
                method="device_movement",
                reason=f"Failed to move {mem_type.value} array to device {device_id}: {e}"
            ) from e

    # Check if it's None (CPU memory types)
    if move_handler is None:
        return data

    # It's an eval expression
    try:
        mod = _ensure_module(mem_type.value)  # noqa: F841 (used in eval)

        # Handle context managers (CuPy, TensorFlow)
        if 'move_context' in config and config['move_context']:
            context_expr = config['move_context'].format(mod='mod')
            context = eval(context_expr)
            with context:
                return eval(move_handler.format(mod='mod'))
        else:
            return eval(move_handler.format(mod='mod'))
    except Exception as e:
        raise MemoryConversionError(
            source_type=memory_type,
            target_type=memory_type,
            method="device_movement",
            reason=f"Failed to move {mem_type.value} array to device {device_id}: {e}"
        ) from e
