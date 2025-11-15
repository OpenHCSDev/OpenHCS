"""
Single source of truth for ALL framework-specific behavior.

This module consolidates all framework-specific logic that was previously
scattered across utils.py, stack_utils.py, gpu_cleanup.py, dtype_scaling.py,
and framework_ops.py.

Architecture:
- Framework handlers: Custom logic for special cases (pyclesperanto, JAX, TensorFlow)
- Unified config: Single _FRAMEWORK_CONFIG dict with all framework metadata
- Polymorphic dispatch: Handlers can be callables or eval expressions
"""

import gc
import logging
from typing import Any, Optional, Callable
from openhcs.constants.constants import MemoryType

logger = logging.getLogger(__name__)


# ============================================================================
# FRAMEWORK HANDLERS - All special-case logic lives here
# ============================================================================

def _pyclesperanto_get_device_id(data: Any, mod: Any) -> int:
    """Get device ID for pyclesperanto array."""
    try:
        current_device = mod.get_device()
        if hasattr(current_device, 'id'):
            return current_device.id
        devices = mod.list_available_devices()
        for i, device in enumerate(devices):
            if str(device) == str(current_device):
                return i
        return 0
    except Exception as e:
        logger.warning(f"Failed to get device ID for pyclesperanto: {e}")
        return 0


def _pyclesperanto_set_device(device_id: int, mod: Any) -> None:
    """Set device for pyclesperanto."""
    devices = mod.list_available_devices()
    if device_id >= len(devices):
        raise ValueError(f"Device {device_id} not available. Available: {len(devices)}")
    mod.select_device(device_id)


def _pyclesperanto_move_to_device(data: Any, device_id: int, mod: Any, memory_type: str) -> Any:
    """Move pyclesperanto array to device."""
    # Import here to avoid circular dependency
    from openhcs.core.memory.utils import _get_device_id
    
    current_device_id = _get_device_id(data, memory_type)
    
    if current_device_id != device_id:
        mod.select_device(device_id)
        result = mod.create_like(data)
        mod.copy(data, result)
        return result
    return data


def _pyclesperanto_stack_slices(slices: list, memory_type: str, gpu_id: int, mod: Any) -> Any:
    """Stack slices using pyclesperanto's concatenate_along_z (pairwise concatenation)."""
    from openhcs.core.memory.converters import convert_memory, detect_memory_type

    converted_slices = []
    conversion_count = 0

    for slice_data in slices:
        source_type = detect_memory_type(slice_data)

        if source_type != memory_type:
            conversion_count += 1

        if source_type == memory_type:
            converted_slices.append(slice_data)
        else:
            converted = convert_memory(slice_data, source_type, memory_type, gpu_id)
            converted_slices.append(converted)

    # Log batch conversion
    if conversion_count > 0:
        logger.debug(
            f"🔄 MEMORY CONVERSION: Converted {conversion_count}/{len(slices)} slices "
            f"to {memory_type} for pyclesperanto stacking"
        )

    # Handle single slice case - must return 3D array with shape (1, Y, X)
    if len(converted_slices) == 1:
        slice_2d = converted_slices[0]
        # Reshape 2D slice to 3D with shape (1, Y, X)
        result = mod.create((1, slice_2d.shape[0], slice_2d.shape[1]), dtype=slice_2d.dtype)
        result[0] = slice_2d
        return result

    # Pyclesperanto's concatenate_along_z takes two arguments (pairwise concatenation)
    # Start with first slice and concatenate remaining slices one by one
    result = converted_slices[0]
    for i in range(1, len(converted_slices)):
        result = mod.concatenate_along_z(result, converted_slices[i])

    return result


def _jax_assign_slice(result: Any, index: int, slice_data: Any) -> Any:
    """Assign slice to JAX array (immutable)."""
    return result.at[index].set(slice_data)


def _tensorflow_validate_dlpack(obj: Any, mod: Any) -> bool:
    """Validate TensorFlow DLPack support."""
    # Check version
    major, minor = map(int, mod.__version__.split('.')[:2])
    if major < 2 or (major == 2 and minor < 12):
        raise RuntimeError(
            f"TensorFlow {mod.__version__} does not support stable DLPack. "
            f"Version 2.12.0+ required. "
            f"Clause 88 violation: Cannot infer DLPack capability."
        )
    
    # Check GPU
    device_str = obj.device.lower()
    if "gpu" not in device_str:
        raise RuntimeError(
            "TensorFlow tensor on CPU cannot use DLPack operations reliably. "
            "Only GPU tensors are supported for DLPack operations. "
            "Clause 88 violation: Cannot infer GPU capability."
        )
    
    # Check module
    if not hasattr(mod.experimental, "dlpack"):
        raise RuntimeError(
            "TensorFlow installation missing experimental.dlpack module. "
            "Clause 88 violation: Cannot infer DLPack capability."
        )
    
    return True


def _numpy_dtype_conversion_needed(first_slice: Any, detect_memory_type_func: Callable) -> bool:
    """Check if NumPy needs dtype conversion (only for torch sources)."""
    source_type = detect_memory_type_func(first_slice)
    return source_type == MemoryType.TORCH.value


def _torch_dtype_conversion_needed(first_slice: Any, detect_memory_type_func: Callable) -> bool:
    """Torch always needs dtype conversion to get correct torch dtype."""
    return True


# ============================================================================
# UNIFIED FRAMEWORK CONFIGURATION
# ============================================================================

_FRAMEWORK_CONFIG = {
    MemoryType.NUMPY: {
        # Metadata
        'import_name': 'numpy',
        'display_name': 'NumPy',
        'is_gpu': False,
        
        # Device operations
        'get_device_id': None,  # CPU
        'set_device': None,  # CPU
        'move_to_device': None,  # CPU
        
        # Stack operations
        'allocate_stack': 'np.empty(stack_shape, dtype=dtype)',
        'allocate_context': None,
        'needs_dtype_conversion': _numpy_dtype_conversion_needed,  # Callable
        'assign_slice': None,  # Standard: result[i] = slice
        'stack_handler': None,  # Standard stacking
        
        # Dtype scaling
        'scaling_ops': {
            'min': 'result.min()',
            'max': 'result.max()',
            'astype': 'result.astype(target_dtype)',
            'check_float': 'np.issubdtype(result.dtype, np.floating)',
            'check_int': 'target_dtype in [np.uint8, np.uint16, np.uint32, np.int8, np.int16, np.int32]',
        },
        
        # Conversion operations
        'conversion_ops': {
            'to_numpy': 'data',
            'from_numpy': 'data',
            'from_dlpack': None,
            'move_to_device': 'data',
        },

        # DLPack
        'supports_dlpack': False,
        'validate_dlpack': None,

        # GPU/Cleanup
        'lazy_getter': None,
        'gpu_check': None,
        'stream_context': None,
        'device_context': None,
        'cleanup_ops': None,
        'has_oom_recovery': False,
        'oom_exception_types': [],
        'oom_string_patterns': ['cannot allocate memory', 'memory exhausted'],
        'oom_clear_cache': 'import gc; gc.collect()',
    },
    
    MemoryType.CUPY: {
        # Metadata
        'import_name': 'cupy',
        'display_name': 'CuPy',
        'is_gpu': True,
        
        # Device operations (eval expressions)
        'get_device_id': 'data.device.id',
        'get_device_id_fallback': '0',
        'set_device': '{mod}.cuda.Device(device_id).use()',
        'move_to_device': 'data.copy() if data.device.id != device_id else data',
        'move_context': '{mod}.cuda.Device(device_id)',
        
        # Stack operations
        'allocate_stack': 'cupy.empty(stack_shape, dtype=first_slice.dtype)',
        'allocate_context': 'cupy.cuda.Device(gpu_id)',
        'needs_dtype_conversion': False,
        'assign_slice': None,  # Standard
        'stack_handler': None,  # Standard
        
        # Dtype scaling
        'scaling_ops': {
            'min': 'mod.min(result)',
            'max': 'mod.max(result)',
            'astype': 'result.astype(target_dtype)',
            'check_float': 'mod.issubdtype(result.dtype, mod.floating)',
            'check_int': 'not mod.issubdtype(target_dtype, mod.floating)',
        },
        
        # Conversion operations
        'conversion_ops': {
            'to_numpy': 'data.get()',
            'from_numpy': '({mod}.cuda.Device(gpu_id), {mod}.array(data))[1]',
            'from_dlpack': '{mod}.from_dlpack(data)',
            'move_to_device': 'data if data.device.id == gpu_id else ({mod}.cuda.Device(gpu_id), {mod}.array(data))[1]',
        },

        # DLPack
        'supports_dlpack': True,
        'validate_dlpack': None,

        # GPU/Cleanup
        'lazy_getter': '_get_cupy',
        'gpu_check': '{mod} is not None and hasattr({mod}, "cuda")',
        'stream_context': '{mod}.cuda.Stream()',
        'device_context': '{mod}.cuda.Device({device_id})',
        'cleanup_ops': '{mod}.get_default_memory_pool().free_all_blocks(); {mod}.get_default_pinned_memory_pool().free_all_blocks(); {mod}.cuda.runtime.deviceSynchronize()',
        'has_oom_recovery': True,
        'oom_exception_types': ['{mod}.cuda.memory.OutOfMemoryError', '{mod}.cuda.runtime.CUDARuntimeError'],
        'oom_string_patterns': ['out of memory', 'cuda_error_out_of_memory'],
        'oom_clear_cache': '{mod}.get_default_memory_pool().free_all_blocks(); {mod}.get_default_pinned_memory_pool().free_all_blocks(); {mod}.cuda.runtime.deviceSynchronize()',
    },
    
    MemoryType.TORCH: {
        # Metadata
        'import_name': 'torch',
        'display_name': 'PyTorch',
        'is_gpu': True,
        
        # Device operations
        'get_device_id': 'data.device.index if data.is_cuda else None',
        'get_device_id_fallback': 'None',
        'set_device': None,  # PyTorch handles device at tensor creation
        'move_to_device': 'data.to(f"cuda:{device_id}") if (not data.is_cuda or data.device.index != device_id) else data',
        
        # Stack operations
        'allocate_stack': 'torch.empty(stack_shape, dtype=sample_converted.dtype, device=sample_converted.device)',
        'allocate_context': None,
        'needs_dtype_conversion': _torch_dtype_conversion_needed,  # Callable
        'assign_slice': None,  # Standard
        'stack_handler': None,  # Standard
        
        # Dtype scaling
        'scaling_ops': {
            'min': 'result.min()',
            'max': 'result.max()',
            'astype': 'result.to(target_dtype_mapped)',
            'check_float': 'result.dtype in [mod.float16, mod.float32, mod.float64]',
            'check_int': 'target_dtype_mapped in [mod.uint8, mod.int8, mod.int16, mod.int32, mod.int64]',
            'needs_dtype_map': True,
        },
        
        # Conversion operations
        'conversion_ops': {
            'to_numpy': 'data.cpu().numpy()',
            'from_numpy': '{mod}.from_numpy(data).cuda(gpu_id)',
            'from_dlpack': '{mod}.from_dlpack(data)',
            'move_to_device': 'data if data.device.index == gpu_id else data.cuda(gpu_id)',
        },

        # DLPack
        'supports_dlpack': True,
        'validate_dlpack': None,

        # GPU/Cleanup
        'lazy_getter': '_get_torch',
        'gpu_check': '{mod} is not None and hasattr({mod}, "cuda") and {mod}.cuda.is_available()',
        'stream_context': '{mod}.cuda.Stream()',
        'device_context': '{mod}.cuda.device({device_id})',
        'cleanup_ops': '{mod}.cuda.empty_cache(); {mod}.cuda.synchronize()',
        'has_oom_recovery': True,
        'oom_exception_types': ['{mod}.cuda.OutOfMemoryError'],
        'oom_string_patterns': ['out of memory', 'cuda_error_out_of_memory'],
        'oom_clear_cache': '{mod}.cuda.empty_cache(); {mod}.cuda.synchronize()',
    },

    MemoryType.TENSORFLOW: {
        # Metadata
        'import_name': 'tensorflow',
        'display_name': 'TensorFlow',
        'is_gpu': True,

        # Device operations
        'get_device_id': 'int(data.device.lower().split(":")[-1]) if "gpu" in data.device.lower() else None',
        'get_device_id_fallback': 'None',
        'set_device': None,  # TensorFlow handles device at tensor creation
        'move_to_device': '{mod}.identity(data)',
        'move_context': '{mod}.device(f"/device:GPU:{device_id}")',

        # Stack operations
        'allocate_stack': 'tf.zeros(stack_shape, dtype=first_slice.dtype)',  # TF doesn't have empty()
        'allocate_context': 'tf.device(f"/device:GPU:{gpu_id}")',
        'needs_dtype_conversion': False,
        'assign_slice': None,  # Standard
        'stack_handler': None,  # Standard

        # Dtype scaling
        'scaling_ops': {
            'min': 'mod.reduce_min(result)',
            'max': 'mod.reduce_max(result)',
            'astype': 'mod.cast(result, target_dtype_mapped)',
            'check_float': 'result.dtype in [mod.float16, mod.float32, mod.float64]',
            'check_int': 'target_dtype_mapped in [mod.uint8, mod.int8, mod.int16, mod.int32, mod.int64]',
            'needs_dtype_map': True,
        },

        # Conversion operations
        'conversion_ops': {
            'to_numpy': 'data.numpy()',
            'from_numpy': '{mod}.convert_to_tensor(data)',
            'from_dlpack': '{mod}.experimental.dlpack.from_dlpack(data)',
            'move_to_device': 'data',
        },

        # DLPack
        'supports_dlpack': True,
        'validate_dlpack': _tensorflow_validate_dlpack,  # Custom validation

        # GPU/Cleanup
        'lazy_getter': '_get_tensorflow',
        'gpu_check': '{mod} is not None and {mod}.config.list_physical_devices("GPU")',
        'stream_context': None,  # TensorFlow manages streams internally
        'device_context': '{mod}.device("/GPU:0")',
        'cleanup_ops': None,  # TensorFlow has no explicit cache clearing API
        'has_oom_recovery': True,
        'oom_exception_types': ['{mod}.errors.ResourceExhaustedError', '{mod}.errors.InvalidArgumentError'],
        'oom_string_patterns': ['out of memory', 'resource_exhausted'],
        'oom_clear_cache': None,  # TensorFlow has no explicit cache clearing API
    },

    MemoryType.JAX: {
        # Metadata
        'import_name': 'jax',
        'display_name': 'JAX',
        'is_gpu': True,

        # Device operations
        'get_device_id': 'int(str(data.device).lower().split(":")[-1]) if "gpu" in str(data.device).lower() else None',
        'get_device_id_fallback': 'None',
        'set_device': None,  # JAX handles device at array creation
        'move_to_device': '{mod}.device_put(data, {mod}.devices("gpu")[device_id])',

        # Stack operations
        'allocate_stack': 'jnp.empty(stack_shape, dtype=first_slice.dtype)',
        'allocate_context': None,
        'needs_dtype_conversion': False,
        'assign_slice': _jax_assign_slice,  # Custom handler for immutability
        'stack_handler': None,  # Standard

        # Dtype scaling
        'scaling_ops': {
            'min': 'jnp.min(result)',
            'max': 'jnp.max(result)',
            'astype': 'result.astype(target_dtype_mapped)',
            'check_float': 'result.dtype in [jnp.float16, jnp.float32, jnp.float64]',
            'check_int': 'target_dtype_mapped in [jnp.uint8, jnp.int8, jnp.int16, jnp.int32, jnp.int64]',
            'needs_dtype_map': True,
            'extra_import': 'jax.numpy',
        },

        # Conversion operations
        'conversion_ops': {
            'to_numpy': 'np.asarray(data)',
            'from_numpy': '{mod}.device_put(data, {mod}.devices()[gpu_id])',
            'from_dlpack': '{mod}.dlpack.from_dlpack(data)',
            'move_to_device': 'data',
        },

        # DLPack
        'supports_dlpack': True,
        'validate_dlpack': None,

        # GPU/Cleanup
        'lazy_getter': '_get_jax',
        'gpu_check': '{mod} is not None and any(d.platform == "gpu" for d in {mod}.devices())',
        'stream_context': None,  # JAX/XLA manages streams internally
        'device_context': '{mod}.default_device([d for d in {mod}.devices() if d.platform == "gpu"][0])',
        'cleanup_ops': '{mod}.clear_caches()',
        'has_oom_recovery': True,
        'oom_exception_types': [],
        'oom_string_patterns': ['out of memory', 'oom when allocating', 'allocation failure'],
        'oom_clear_cache': '{mod}.clear_caches()',
    },

    MemoryType.PYCLESPERANTO: {
        # Metadata
        'import_name': 'pyclesperanto',
        'display_name': 'pyclesperanto',
        'is_gpu': True,

        # Device operations (custom handlers)
        'get_device_id': _pyclesperanto_get_device_id,  # Callable
        'get_device_id_fallback': '0',
        'set_device': _pyclesperanto_set_device,  # Callable
        'move_to_device': _pyclesperanto_move_to_device,  # Callable

        # Stack operations (custom handler)
        'allocate_stack': None,  # Uses concatenate_along_z
        'allocate_context': None,
        'needs_dtype_conversion': False,
        'assign_slice': None,  # Not used (custom stacking)
        'stack_handler': _pyclesperanto_stack_slices,  # Custom stacking

        # Conversion operations
        'conversion_ops': {
            'to_numpy': '{mod}.pull(data)',
            'from_numpy': '{mod}.push(data)',
            'from_dlpack': None,
            'move_to_device': 'data',
        },

        # Dtype scaling (custom implementation in dtype_scaling.py)
        'scaling_ops': None,  # Custom _scale_pyclesperanto function

        # DLPack
        'supports_dlpack': False,
        'validate_dlpack': None,

        # GPU/Cleanup
        'lazy_getter': None,
        'gpu_check': None,  # pyclesperanto always uses GPU if available
        'stream_context': None,  # OpenCL manages streams internally
        'device_context': None,  # OpenCL device selection is global
        'cleanup_ops': None,  # pyclesperanto/OpenCL has no explicit cache clearing API
        'has_oom_recovery': True,
        'oom_exception_types': [],
        'oom_string_patterns': ['cl_mem_object_allocation_failure', 'cl_out_of_resources', 'out of memory'],
        'oom_clear_cache': None,  # pyclesperanto/OpenCL has no explicit cache clearing API
    },
}

