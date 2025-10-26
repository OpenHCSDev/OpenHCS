"""
Dtype scaling and conversion functions for different memory types.

This module provides framework-specific scaling functions that handle conversion
between floating point and integer dtypes with proper range scaling.

Uses enum-driven metaprogramming to eliminate 276 lines of duplication (82% reduction).
Pattern follows PR #38: pure data → eval() → single generic function.
"""

import numpy as np
from openhcs.constants.constants import MemoryType
from openhcs.core.utils import optional_import


# Scaling ranges for integer dtypes (shared across all memory types)
_SCALING_RANGES = {
    'uint8': 255.0,
    'uint16': 65535.0,
    'uint32': 4294967295.0,
    'int16': (65535.0, 32768.0),  # (scale, offset)
    'int32': (4294967295.0, 2147483648.0),
}


# Pure data - framework-specific operations as strings
_FRAMEWORK_OPS = {
    MemoryType.NUMPY: {
        'min': 'result.min()',
        'max': 'result.max()',
        'astype': 'result.astype(target_dtype)',
        'check_float': 'np.issubdtype(result.dtype, np.floating)',
        'check_int': 'target_dtype in [np.uint8, np.uint16, np.uint32, np.int8, np.int16, np.int32]',
    },
    MemoryType.CUPY: {
        'min': 'mod.min(result)',
        'max': 'mod.max(result)',
        'astype': 'result.astype(target_dtype)',
        'check_float': 'mod.issubdtype(result.dtype, mod.floating)',
        'check_int': 'not mod.issubdtype(target_dtype, mod.floating)',
    },
    MemoryType.TORCH: {
        'min': 'result.min()',
        'max': 'result.max()',
        'astype': 'result.to(target_dtype_mapped)',
        'check_float': 'result.dtype in [mod.float16, mod.float32, mod.float64]',
        'check_int': 'target_dtype_mapped in [mod.uint8, mod.int8, mod.int16, mod.int32, mod.int64]',
        'needs_dtype_map': True,
    },
    MemoryType.TENSORFLOW: {
        'min': 'mod.reduce_min(result)',
        'max': 'mod.reduce_max(result)',
        'astype': 'mod.cast(result, target_dtype_mapped)',
        'check_float': 'result.dtype in [mod.float16, mod.float32, mod.float64]',
        'check_int': 'target_dtype_mapped in [mod.uint8, mod.int8, mod.int16, mod.int32, mod.int64]',
        'needs_dtype_map': True,
    },
    MemoryType.JAX: {
        'min': 'jnp.min(result)',
        'max': 'jnp.max(result)',
        'astype': 'result.astype(target_dtype_mapped)',
        'check_float': 'result.dtype in [jnp.float16, jnp.float32, jnp.float64]',
        'check_int': 'target_dtype_mapped in [jnp.uint8, jnp.int8, jnp.int16, jnp.int32, jnp.int64]',
        'needs_dtype_map': True,
        'extra_import': 'jax.numpy',
    },
    MemoryType.PYCLESPERANTO: None,  # Custom implementation
}


def _scale_generic(result, target_dtype, mem_type: MemoryType):
    """
    Generic scaling function that works for all memory types using eval().

    This single function replaces 6 nearly-identical scaling functions.
    """
    # Special case: pyclesperanto
    if mem_type == MemoryType.PYCLESPERANTO:
        return _scale_pyclesperanto(result, target_dtype)

    ops = _FRAMEWORK_OPS[mem_type]
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

    # Check if conversion needed (float → int)
    result_is_float = eval(ops['check_float'])
    target_is_int = eval(ops['check_int'])

    if not (result_is_float and target_is_int):
        # Direct conversion
        return eval(ops['astype'])

    # Get min/max
    result_min = eval(ops['min'])  # noqa: F841 (used in eval)
    result_max = eval(ops['max'])  # noqa: F841 (used in eval)

    if result_max <= result_min:
        # Constant image
        return eval(ops['astype'])

    # Normalize to [0, 1]
    normalized = (result - result_min) / (result_max - result_min)  # noqa: F841 (used in eval)

    # Scale to target range
    dtype_name = target_dtype.__name__ if hasattr(target_dtype, '__name__') else str(target_dtype).split('.')[-1]

    if dtype_name in _SCALING_RANGES:
        range_info = _SCALING_RANGES[dtype_name]
        if isinstance(range_info, tuple):
            scale_val, offset_val = range_info
            result = normalized * scale_val - offset_val  # noqa: F841 (used in eval)
        else:
            result = normalized * range_info  # noqa: F841 (used in eval)
    else:
        result = normalized  # noqa: F841 (used in eval)

    # Convert dtype
    return eval(ops['astype'])


def _scale_pyclesperanto(result, target_dtype):
    """Scale pyclesperanto results (GPU operations require special handling)."""
    cle = optional_import("pyclesperanto")
    if cle is None or not hasattr(result, 'dtype'):
        return result

    # Check if result is floating point and target is integer
    result_is_float = np.issubdtype(result.dtype, np.floating)
    target_is_int = target_dtype in [np.uint8, np.uint16, np.uint32, np.int8, np.int16, np.int32]

    if not (result_is_float and target_is_int):
        # Direct conversion
        return cle.push(cle.pull(result).astype(target_dtype))

    # Get min/max
    result_min = float(cle.minimum_of_all_pixels(result))
    result_max = float(cle.maximum_of_all_pixels(result))

    if result_max <= result_min:
        # Constant image
        return cle.push(cle.pull(result).astype(target_dtype))

    # Normalize to [0, 1] using GPU operations
    normalized = cle.subtract_image_from_scalar(result, scalar=result_min)
    range_val = result_max - result_min
    normalized = cle.multiply_image_and_scalar(normalized, scalar=1.0/range_val)

    # Scale to target range
    dtype_name = target_dtype.__name__
    if dtype_name in _SCALING_RANGES:
        range_info = _SCALING_RANGES[dtype_name]
        if isinstance(range_info, tuple):
            scale_val, offset_val = range_info
            scaled = cle.multiply_image_and_scalar(normalized, scalar=scale_val)
            scaled = cle.subtract_image_from_scalar(scaled, scalar=offset_val)
        else:
            scaled = cle.multiply_image_and_scalar(normalized, scalar=range_info)
    else:
        scaled = normalized

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

