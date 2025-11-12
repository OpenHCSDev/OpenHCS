"""
Dtype scaling and conversion functions for different memory types.

This module provides framework-specific scaling functions that handle conversion
between floating point and integer dtypes with proper range scaling.

Uses enum-driven metaprogramming to eliminate 276 lines of duplication (82% reduction).
Pattern follows PR #38: pure data → eval() → single generic function.
"""

import numpy as np
from openhcs.constants.constants import MemoryType
from openhcs.core.memory.framework_config import _FRAMEWORK_CONFIG
from openhcs.core.utils import optional_import


# Scaling ranges for integer dtypes (shared across all memory types)
_DTYPE_MAX_VALUES = {
    'uint8': 255.0,
    'uint16': 65535.0,
    'uint32': 4294967295.0,
    'int8': 127.0,
    'int16': 32767.0,
    'int32': 2147483647.0,
    'float16': 1.0,
    'float32': 1.0,
    'float64': 1.0,
}

_DTYPE_MIN_VALUES = {
    'uint8': 0.0,
    'uint16': 0.0,
    'uint32': 0.0,
    'int8': -128.0,
    'int16': -32768.0,
    'int32': -2147483648.0,
    'float16': 0.0,
    'float32': 0.0,
    'float64': 0.0,
}


# NOTE: Framework-specific scaling operations now defined in framework_config.py
# This eliminates the scattered _FRAMEWORK_OPS dict


def _scale_generic(result, target_dtype, mem_type: MemoryType):
    """
    Generic scaling function that works for all memory types using framework config.

    This single function replaces 6 nearly-identical scaling functions.
    """
    # Special case: pyclesperanto
    if mem_type == MemoryType.PYCLESPERANTO:
        return _scale_pyclesperanto(result, target_dtype)

    config = _FRAMEWORK_CONFIG[mem_type]
    ops = config['scaling_ops']
    mod = optional_import(mem_type.value)  # noqa: F841 (used in eval)
    if mod is None:
        return result

    if not hasattr(result, 'dtype'):
        return result

    # Handle dtype mapping for frameworks that need it
    target_dtype_mapped = target_dtype  # noqa: F841 (used in eval)
    if ops.get('needs_dtype_map'):
        dtype_map = {
            np.uint8: mod.uint8, np.int8: mod.int8, np.int16: mod.int16,
            np.int32: mod.int32, np.int64: mod.int64, np.float16: mod.float16,
            np.float32: mod.float32, np.float64: mod.float64,
        }
        target_dtype_mapped = dtype_map.get(target_dtype, mod.float32)  # noqa: F841

    # Extra imports (e.g., jax.numpy)
    if 'extra_import' in ops:
        jnp = optional_import(ops['extra_import'])  # noqa: F841 (used in eval)

    # Get dtype names
    result_dtype_name = result.dtype.name if hasattr(result.dtype, 'name') else str(result.dtype).split('.')[-1]
    target_dtype_name = target_dtype.__name__ if hasattr(target_dtype, '__name__') else str(target_dtype).split('.')[-1]

    # Check if we need dtype-to-dtype scaling
    # Only scale when converting between different numeric ranges
    if result_dtype_name == target_dtype_name:
        return result

    # Get dtype ranges
    input_min = _DTYPE_MIN_VALUES.get(result_dtype_name)
    input_max = _DTYPE_MAX_VALUES.get(result_dtype_name)
    target_min = _DTYPE_MIN_VALUES.get(target_dtype_name)
    target_max = _DTYPE_MAX_VALUES.get(target_dtype_name)

    # If we don't have range info for either dtype, just do direct conversion
    if input_max is None or target_max is None:
        return eval(ops['astype'])

    # Dtype-to-dtype scaling: scale based on dtype ranges, not data ranges
    # Formula: output = (input - input_min) * (target_max - target_min) / (input_max - input_min) + target_min
    # This preserves the relative position in the dtype range

    input_range = input_max - input_min
    target_range = target_max - target_min
    scale_factor = target_range / input_range

    # Scale from input dtype range to target dtype range
    scaled = (result - input_min) * scale_factor + target_min  # noqa: F841 (used in eval)

    # Convert dtype
    result = scaled  # noqa: F841 (used in eval)
    converted = eval(ops['astype'])
    return converted


def _scale_pyclesperanto(result, target_dtype):
    """Scale pyclesperanto results (GPU operations require special handling)."""
    cle = optional_import("pyclesperanto")
    if cle is None or not hasattr(result, 'dtype'):
        return result

    # Get dtype names
    result_dtype_name = result.dtype.name if hasattr(result.dtype, 'name') else str(result.dtype).split('.')[-1]
    target_dtype_name = target_dtype.__name__ if hasattr(target_dtype, '__name__') else str(target_dtype).split('.')[-1]

    # Check if we need dtype-to-dtype scaling
    if result_dtype_name == target_dtype_name:
        # Same dtype, no conversion needed
        return result

    # Get dtype ranges
    input_min = _DTYPE_MIN_VALUES.get(result_dtype_name)
    input_max = _DTYPE_MAX_VALUES.get(result_dtype_name)
    target_min = _DTYPE_MIN_VALUES.get(target_dtype_name)
    target_max = _DTYPE_MAX_VALUES.get(target_dtype_name)

    # If we don't have range info for either dtype, just do direct conversion
    if input_max is None or target_max is None:
        return cle.push(cle.pull(result).astype(target_dtype))

    # Dtype-to-dtype scaling using GPU operations
    # Formula: output = (input - input_min) * (target_max - target_min) / (input_max - input_min) + target_min

    input_range = input_max - input_min
    target_range = target_max - target_min
    scale_factor = target_range / input_range

    # Scale from input dtype range to target dtype range using GPU ops
    scaled = cle.subtract_image_from_scalar(result, scalar=input_min)
    scaled = cle.multiply_image_and_scalar(scaled, scalar=scale_factor)
    scaled = cle.add_image_and_scalar(scaled, scalar=target_min)

    # Convert dtype
    return cle.push(cle.pull(scaled).astype(target_dtype))


# Auto-generate all scaling functions using partial application
from functools import partial

_SCALING_FUNCTIONS_GENERATED = {
    mem_type.value: partial(_scale_generic, mem_type=mem_type)
    for mem_type in MemoryType
}

# Registry mapping memory type names to scaling functions (backward compatibility)
SCALING_FUNCTIONS = _SCALING_FUNCTIONS_GENERATED
