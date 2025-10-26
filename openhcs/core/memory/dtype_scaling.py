"""
Dtype scaling and conversion functions for different memory types.

This module provides framework-specific scaling functions that handle conversion
between floating point and integer dtypes with proper range scaling.
"""

import numpy as np
from openhcs.core.utils import optional_import


def _scale_numpy(result, target_dtype):
    """Scale numpy results to target integer range and convert dtype."""
    if not hasattr(result, 'dtype'):
        return result

    # Check if result is floating point and target is integer
    result_is_float = np.issubdtype(result.dtype, np.floating)
    target_is_int = target_dtype in [np.uint8, np.uint16, np.uint32, np.int8, np.int16, np.int32]

    if result_is_float and target_is_int:
        # Scale floating point results to integer range
        result_min = result.min()
        result_max = result.max()

        if result_max > result_min:  # Avoid division by zero
            # Normalize to [0, 1] range
            normalized = (result - result_min) / (result_max - result_min)

            # Scale to target dtype range
            if target_dtype == np.uint8:
                scaled = normalized * 255.0
            elif target_dtype == np.uint16:
                scaled = normalized * 65535.0
            elif target_dtype == np.uint32:
                scaled = normalized * 4294967295.0
            elif target_dtype == np.int16:
                scaled = normalized * 65535.0 - 32768.0
            elif target_dtype == np.int32:
                scaled = normalized * 4294967295.0 - 2147483648.0
            else:
                scaled = normalized

            return scaled.astype(target_dtype)
        else:
            # Constant image, just convert dtype
            return result.astype(target_dtype)
    else:
        # Direct conversion for compatible types
        return result.astype(target_dtype)


def _scale_cupy(result, target_dtype):
    """Scale CuPy results to target integer range and convert dtype."""
    cp = optional_import("cupy")
    if cp is None:
        return result

    if not hasattr(result, 'dtype'):
        return result

    # If result is floating point and target is integer, scale appropriately
    if cp.issubdtype(result.dtype, cp.floating) and not cp.issubdtype(target_dtype, cp.floating):
        # Clip to [0, 1] range and scale to integer range
        clipped = cp.clip(result, 0, 1)
        if target_dtype == cp.uint8:
            return (clipped * 255).astype(target_dtype)
        elif target_dtype == cp.uint16:
            return (clipped * 65535).astype(target_dtype)
        elif target_dtype == cp.uint32:
            return (clipped * 4294967295).astype(target_dtype)
        else:
            # For other integer types, just convert without scaling
            return result.astype(target_dtype)

    # Direct conversion for same numeric type families
    return result.astype(target_dtype)


def _scale_torch(result, target_dtype):
    """Scale PyTorch results to target integer range and convert dtype."""
    torch = optional_import("torch")
    if torch is None:
        return result

    if not hasattr(result, 'dtype'):
        return result

    # Map numpy dtype to torch dtype
    dtype_map = {
        np.uint8: torch.uint8,
        np.int8: torch.int8,
        np.int16: torch.int16,
        np.int32: torch.int32,
        np.int64: torch.int64,
        np.float16: torch.float16,
        np.float32: torch.float32,
        np.float64: torch.float64,
    }
    
    torch_target_dtype = dtype_map.get(target_dtype, torch.float32)

    # Check if result is floating point and target is integer
    result_is_float = result.dtype in [torch.float16, torch.float32, torch.float64]
    target_is_int = torch_target_dtype in [torch.uint8, torch.int8, torch.int16, torch.int32, torch.int64]

    if result_is_float and target_is_int:
        # Scale floating point results to integer range
        result_min = result.min()
        result_max = result.max()

        if result_max > result_min:  # Avoid division by zero
            # Normalize to [0, 1] range
            normalized = (result - result_min) / (result_max - result_min)

            # Scale to target dtype range
            if torch_target_dtype == torch.uint8:
                scaled = normalized * 255.0
            elif torch_target_dtype == torch.int16:
                scaled = normalized * 65535.0 - 32768.0
            elif torch_target_dtype == torch.int32:
                scaled = normalized * 4294967295.0 - 2147483648.0
            else:
                scaled = normalized

            return scaled.to(torch_target_dtype)
        else:
            # Constant image, just convert dtype
            return result.to(torch_target_dtype)
    else:
        # Direct conversion for compatible types
        return result.to(torch_target_dtype)


def _scale_tensorflow(result, target_dtype):
    """Scale TensorFlow results to target integer range and convert dtype."""
    tf = optional_import("tensorflow")
    if tf is None:
        return result

    if not hasattr(result, 'dtype'):
        return result

    # Map numpy dtype to tensorflow dtype
    dtype_map = {
        np.uint8: tf.uint8,
        np.int8: tf.int8,
        np.int16: tf.int16,
        np.int32: tf.int32,
        np.int64: tf.int64,
        np.float16: tf.float16,
        np.float32: tf.float32,
        np.float64: tf.float64,
    }
    
    tf_target_dtype = dtype_map.get(target_dtype, tf.float32)

    # Check if result is floating point and target is integer
    result_is_float = result.dtype in [tf.float16, tf.float32, tf.float64]
    target_is_int = tf_target_dtype in [tf.uint8, tf.int8, tf.int16, tf.int32, tf.int64]

    if result_is_float and target_is_int:
        # Scale floating point results to integer range
        result_min = tf.reduce_min(result)
        result_max = tf.reduce_max(result)

        if result_max > result_min:  # Avoid division by zero
            # Normalize to [0, 1] range
            normalized = (result - result_min) / (result_max - result_min)

            # Scale to target dtype range
            if tf_target_dtype == tf.uint8:
                scaled = normalized * 255.0
            elif tf_target_dtype == tf.int16:
                scaled = normalized * 65535.0 - 32768.0
            elif tf_target_dtype == tf.int32:
                scaled = normalized * 4294967295.0 - 2147483648.0
            else:
                scaled = normalized

            return tf.cast(scaled, tf_target_dtype)
        else:
            # Constant image, just convert dtype
            return tf.cast(result, tf_target_dtype)
    else:
        # Direct conversion for compatible types
        return tf.cast(result, tf_target_dtype)


def _scale_jax(result, target_dtype):
    """Scale JAX results to target integer range and convert dtype."""
    jax = optional_import("jax")
    if jax is None:
        return result

    import jax.numpy as jnp

    if not hasattr(result, 'dtype'):
        return result

    # Map numpy dtype to jax dtype
    dtype_map = {
        np.uint8: jnp.uint8,
        np.int8: jnp.int8,
        np.int16: jnp.int16,
        np.int32: jnp.int32,
        np.int64: jnp.int64,
        np.float16: jnp.float16,
        np.float32: jnp.float32,
        np.float64: jnp.float64,
    }
    
    jax_target_dtype = dtype_map.get(target_dtype, jnp.float32)

    # Check if result is floating point and target is integer
    result_is_float = result.dtype in [jnp.float16, jnp.float32, jnp.float64]
    target_is_int = jax_target_dtype in [jnp.uint8, jnp.int8, jnp.int16, jnp.int32, jnp.int64]

    if result_is_float and target_is_int:
        # Scale floating point results to integer range
        result_min = jnp.min(result)
        result_max = jnp.max(result)

        if result_max > result_min:  # Avoid division by zero
            # Normalize to [0, 1] range
            normalized = (result - result_min) / (result_max - result_min)

            # Scale to target dtype range
            if jax_target_dtype == jnp.uint8:
                scaled = normalized * 255.0
            elif jax_target_dtype == jnp.int16:
                scaled = normalized * 65535.0 - 32768.0
            elif jax_target_dtype == jnp.int32:
                scaled = normalized * 4294967295.0 - 2147483648.0
            else:
                scaled = normalized

            return scaled.astype(jax_target_dtype)
        else:
            # Constant image, just convert dtype
            return result.astype(jax_target_dtype)
    else:
        # Direct conversion for compatible types
        return result.astype(jax_target_dtype)


def _scale_pyclesperanto(result, target_dtype):
    """Scale pyclesperanto results to target integer range and convert dtype."""
    cle = optional_import("pyclesperanto")
    if cle is None:
        return result

    if not hasattr(result, 'dtype'):
        return result

    # Check if result is floating point and target is integer
    result_is_float = np.issubdtype(result.dtype, np.floating)
    target_is_int = target_dtype in [np.uint8, np.uint16, np.uint32, np.int8, np.int16, np.int32]

    if result_is_float and target_is_int:
        # Get min/max of result for proper scaling
        result_min = float(cle.minimum_of_all_pixels(result))
        result_max = float(cle.maximum_of_all_pixels(result))

        if result_max > result_min:  # Avoid division by zero
            # Normalize to [0, 1] range
            normalized = cle.subtract_image_from_scalar(result, scalar=result_min)
            range_val = result_max - result_min
            normalized = cle.multiply_image_and_scalar(normalized, scalar=1.0/range_val)

            # Scale to target dtype range
            if target_dtype == np.uint8:
                scaled = cle.multiply_image_and_scalar(normalized, scalar=255.0)
            elif target_dtype == np.uint16:
                scaled = cle.multiply_image_and_scalar(normalized, scalar=65535.0)
            elif target_dtype == np.uint32:
                scaled = cle.multiply_image_and_scalar(normalized, scalar=4294967295.0)
            elif target_dtype == np.int16:
                scaled = cle.multiply_image_and_scalar(normalized, scalar=65535.0)
                scaled = cle.subtract_image_from_scalar(scaled, scalar=32768.0)
            elif target_dtype == np.int32:
                scaled = cle.multiply_image_and_scalar(normalized, scalar=4294967295.0)
                scaled = cle.subtract_image_from_scalar(scaled, scalar=2147483648.0)
            else:
                scaled = normalized

            # Convert to target dtype using push/pull method
            scaled_cpu = cle.pull(scaled).astype(target_dtype)
            return cle.push(scaled_cpu)
        else:
            # Constant image, just convert dtype
            result_cpu = cle.pull(result).astype(target_dtype)
            return cle.push(result_cpu)
    else:
        # Direct conversion for compatible types
        result_cpu = cle.pull(result).astype(target_dtype)
        return cle.push(result_cpu)


# Registry mapping memory type names to scaling functions
SCALING_FUNCTIONS = {
    'numpy': _scale_numpy,
    'cupy': _scale_cupy,
    'torch': _scale_torch,
    'tensorflow': _scale_tensorflow,
    'jax': _scale_jax,
    'pyclesperanto': _scale_pyclesperanto,
}

