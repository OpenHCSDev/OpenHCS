"""
Framework operations data for memory type system.

This module contains pure data definitions describing framework-specific operations
for each memory type. These definitions are used by metaprogramming to auto-generate
decorators, cleanup functions, and other framework-specific code.
"""

from openhcs.constants.constants import MemoryType

# Pure data - framework-specific operations as strings
# These will be used with eval() and format() to generate actual code
_FRAMEWORK_OPS = {
    MemoryType.NUMPY: {
        'import_name': 'numpy',
        'display_name': 'NumPy',
        'lazy_getter': None,  # CPU, no lazy import needed
        'gpu_check': None,  # CPU, no GPU check
        'stream_context': None,  # CPU, no stream context
        'device_context': None,  # CPU, no device context
        'cleanup_ops': None,  # CPU, no cleanup needed
        'has_oom_recovery': False,
        'get_device_id': None,  # CPU, no device ID
        # OOM detection (CPU doesn't have GPU OOM, but can have MemoryError)
        'oom_exception_types': [],
        'oom_string_patterns': ['cannot allocate memory', 'memory exhausted'],
        'oom_clear_cache': 'import gc; gc.collect()',
    },
    MemoryType.CUPY: {
        'import_name': 'cupy',
        'display_name': 'CuPy',
        'lazy_getter': '_get_cupy',
        'gpu_check': '{mod} is not None and hasattr({mod}, "cuda")',
        'stream_context': '{mod}.cuda.Stream()',
        'device_context': '{mod}.cuda.Device({device_id})',
        'cleanup_ops': '{mod}.get_default_memory_pool().free_all_blocks(); {mod}.get_default_pinned_memory_pool().free_all_blocks(); {mod}.cuda.runtime.deviceSynchronize()',
        'has_oom_recovery': True,
        'get_device_id': 'image.device.id if hasattr(image, "device") else 0',
        # OOM detection
        'oom_exception_types': ['{mod}.cuda.memory.OutOfMemoryError', '{mod}.cuda.runtime.CUDARuntimeError'],
        'oom_string_patterns': ['out of memory', 'cuda_error_out_of_memory'],
        # OOM cache clearing (with device context)
        'oom_clear_cache': '{mod}.get_default_memory_pool().free_all_blocks(); {mod}.get_default_pinned_memory_pool().free_all_blocks(); {mod}.cuda.runtime.deviceSynchronize()',
    },
    MemoryType.TORCH: {
        'import_name': 'torch',
        'display_name': 'PyTorch',
        'lazy_getter': '_get_torch',
        'gpu_check': '{mod} is not None and hasattr({mod}, "cuda") and {mod}.cuda.is_available()',
        'stream_context': '{mod}.cuda.Stream()',
        'device_context': '{mod}.cuda.device({device_id})',
        'cleanup_ops': '{mod}.cuda.empty_cache(); {mod}.cuda.synchronize()',
        'has_oom_recovery': True,
        'get_device_id': 'image.device.index if hasattr(image, "device") and hasattr(image.device, "index") else 0',
        # OOM detection
        'oom_exception_types': ['{mod}.cuda.OutOfMemoryError'],
        'oom_string_patterns': ['out of memory', 'cuda_error_out_of_memory'],
        # OOM cache clearing (with device context)
        'oom_clear_cache': '{mod}.cuda.empty_cache(); {mod}.cuda.synchronize()',
    },
    MemoryType.TENSORFLOW: {
        'import_name': 'tensorflow',
        'display_name': 'TensorFlow',
        'lazy_getter': '_get_tensorflow',
        'gpu_check': '{mod} is not None and {mod}.config.list_physical_devices("GPU")',
        'stream_context': None,  # TensorFlow manages streams internally
        'device_context': '{mod}.device("/GPU:0")',
        'cleanup_ops': 'import gc; gc.collect()',  # TensorFlow doesn't have explicit cleanup
        'has_oom_recovery': True,
        'get_device_id': '0',  # TensorFlow uses device strings, default to GPU:0
        # OOM detection
        'oom_exception_types': ['{mod}.errors.ResourceExhaustedError', '{mod}.errors.InvalidArgumentError'],
        'oom_string_patterns': ['out of memory', 'resource_exhausted'],
        # OOM cache clearing
        'oom_clear_cache': 'import gc; gc.collect()',
    },
    MemoryType.JAX: {
        'import_name': 'jax',
        'display_name': 'JAX',
        'lazy_getter': '_get_jax',
        'gpu_check': '{mod} is not None and any(d.platform == "gpu" for d in {mod}.devices())',
        'stream_context': None,  # JAX/XLA manages streams internally
        'device_context': '{mod}.default_device([d for d in {mod}.devices() if d.platform == "gpu"][0])',
        'cleanup_ops': 'import gc; gc.collect(); {mod}.clear_caches()',
        'has_oom_recovery': True,
        'get_device_id': '0',  # JAX uses device objects, default to first GPU
        # OOM detection
        'oom_exception_types': [],  # JAX doesn't have specific OOM exception types
        'oom_string_patterns': ['out of memory', 'oom when allocating', 'allocation failure'],
        # OOM cache clearing
        'oom_clear_cache': 'import gc; gc.collect(); {mod}.clear_caches()',
    },
    MemoryType.PYCLESPERANTO: {
        'import_name': 'pyclesperanto',
        'display_name': 'pyclesperanto',
        'lazy_getter': None,  # pyclesperanto imported differently
        'gpu_check': None,  # pyclesperanto always uses GPU if available
        'stream_context': None,  # OpenCL manages streams internally
        'device_context': None,  # OpenCL device selection is global
        'cleanup_ops': 'import gc; gc.collect()',  # OpenCL manages memory automatically
        'has_oom_recovery': True,
        'get_device_id': '0',  # pyclesperanto uses global device selection
        # OOM detection
        'oom_exception_types': [],  # OpenCL doesn't expose specific exception types
        'oom_string_patterns': ['cl_mem_object_allocation_failure', 'cl_out_of_resources', 'out of memory'],
        # OOM cache clearing
        'oom_clear_cache': 'import gc; gc.collect()',
    },
}

