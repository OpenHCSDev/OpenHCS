"""
GPU memory cleanup utilities for different frameworks.

This module provides unified GPU memory cleanup functions for PyTorch, CuPy,
TensorFlow, JAX, and pyclesperanto. The cleanup functions are designed to be called
after processing steps to free up GPU memory that's no longer needed.

REFACTORED: Uses enum-driven metaprogramming to eliminate 67% of code duplication.
"""

import gc
import logging
import os
from typing import Optional
from openhcs.core.utils import optional_import
from openhcs.constants.constants import VALID_GPU_MEMORY_TYPES, MemoryType
from openhcs.core.memory.framework_ops import _FRAMEWORK_OPS, get_all_gpu_memory_types

logger = logging.getLogger(__name__)

# Check if we're in subprocess runner mode and should skip GPU imports
if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
    # Subprocess runner mode - skip GPU imports
    torch = None
    cupy = None
    tensorflow = None
    jax = None
    pyclesperanto = None
    logger.info("Subprocess runner mode - skipping GPU library imports in gpu_cleanup")
else:
    # Normal mode - import GPU frameworks as lazy dependencies
    from openhcs.core.lazy_gpu_imports import torch, cupy, tensorflow, jax, pyclesperanto


def is_gpu_memory_type(memory_type: str) -> bool:
    """
    Check if a memory type is a GPU memory type.

    Args:
        memory_type: Memory type string

    Returns:
        True if it's a GPU memory type, False otherwise
    """
    return memory_type in VALID_GPU_MEMORY_TYPES


def _create_cleanup_function(mem_type: MemoryType):
    """
    Factory function that creates a cleanup function for a specific memory type.
    
    This single factory replaces 6 nearly-identical cleanup functions.
    """
    ops = _FRAMEWORK_OPS[mem_type]
    framework_name = ops['import_name']
    display_name = ops['display_name']
    
    # CPU memory type - no cleanup needed
    if ops['cleanup_ops'] is None:
        def cleanup(device_id: Optional[int] = None) -> None:
            """No-op cleanup for CPU memory type."""
            logger.debug(f"🔥 GPU CLEANUP: No-op for {display_name} (CPU memory type)")
        
        cleanup.__name__ = f"cleanup_{framework_name}_gpu"
        cleanup.__doc__ = f"No-op cleanup for {display_name} (CPU memory type)."
        return cleanup
    
    # GPU memory type - generate cleanup function
    def cleanup(device_id: Optional[int] = None) -> None:
        """
        Clean up {display_name} GPU memory.
        
        Args:
            device_id: Optional GPU device ID. If None, cleans all devices.
        """
        framework = globals().get(framework_name)
        
        if framework is None:
            logger.debug(f"{display_name} not available, skipping cleanup")
            return
        
        try:
            # Check GPU availability
            gpu_check_expr = ops['gpu_check'].format(mod=framework_name)
            try:
                gpu_available = eval(gpu_check_expr, {framework_name: framework})
            except:
                gpu_available = False
            
            if not gpu_available:
                return
            
            # Execute cleanup operations
            if device_id is not None and ops['device_context'] is not None:
                # Clean specific device with context
                device_ctx_expr = ops['device_context'].format(device_id=device_id, mod=framework_name)
                device_ctx = eval(device_ctx_expr, {framework_name: framework})
                
                with device_ctx:
                    # Execute cleanup operations
                    cleanup_expr = ops['cleanup_ops'].format(mod=framework_name)
                    exec(cleanup_expr, {framework_name: framework, 'gc': gc})
                
                logger.debug(f"🔥 GPU CLEANUP: Cleared {display_name} for device {device_id}")
            else:
                # Clean all devices (no device context)
                cleanup_expr = ops['cleanup_ops'].format(mod=framework_name)
                exec(cleanup_expr, {framework_name: framework, 'gc': gc})
                logger.debug(f"🔥 GPU CLEANUP: Cleared {display_name} for all devices")
        
        except Exception as e:
            logger.warning(f"Failed to cleanup {display_name} GPU memory: {e}")
    
    # Set proper function name and docstring
    cleanup.__name__ = f"cleanup_{framework_name}_gpu"
    cleanup.__doc__ = cleanup.__doc__.format(display_name=display_name)
    
    return cleanup


# Auto-generate all cleanup functions
for mem_type in MemoryType:
    cleanup_func = _create_cleanup_function(mem_type)
    globals()[cleanup_func.__name__] = cleanup_func


# Auto-generate cleanup registry
MEMORY_TYPE_CLEANUP_REGISTRY = {
    mem_type.value: globals()[f"cleanup_{_FRAMEWORK_OPS[mem_type]['import_name']}_gpu"]
    for mem_type in MemoryType
}


def cleanup_all_gpu_frameworks(device_id: Optional[int] = None) -> None:
    """
    Clean up GPU memory for all available frameworks.
    
    This function calls cleanup for all GPU frameworks that are currently loaded.
    It's safe to call even if some frameworks aren't available.
    
    Args:
        device_id: Optional GPU device ID. If None, cleans all devices.
    """
    logger.debug(f"🔥 GPU CLEANUP: Starting cleanup for all GPU frameworks (device_id={device_id})")
    
    # Only cleanup GPU memory types
    for mem_type in get_all_gpu_memory_types():
        cleanup_func = MEMORY_TYPE_CLEANUP_REGISTRY[mem_type.value]
        cleanup_func(device_id)
    
    logger.debug("🔥 GPU CLEANUP: Completed cleanup for all GPU frameworks")


def log_gpu_memory_usage(context: str = "") -> None:
    """
    Log GPU memory usage with a specific context for tracking.

    Args:
        context: Description of when/where this memory check is happening
    """
    context_str = f" ({context})" if context else ""

    if torch is not None:
        try:  # Keep try-except for runtime CUDA availability check
            if torch.cuda.is_available():
                for i in range(torch.cuda.device_count()):
                    allocated = torch.cuda.memory_allocated(i) / 1024**3
                    reserved = torch.cuda.memory_reserved(i) / 1024**3
                    free_memory = torch.cuda.get_device_properties(i).total_memory / 1024**3 - reserved
                    logger.debug(f"🔍 VRAM{context_str} GPU {i}: {allocated:.2f}GB alloc, {reserved:.2f}GB reserved, {free_memory:.2f}GB free")
            else:
                logger.debug(f"🔍 VRAM{context_str}: No CUDA available")
        except Exception as e:
            logger.warning(f"🔍 VRAM{context_str}: Error checking PyTorch memory - {e}")


def check_gpu_memory_usage() -> dict:
    """
    Check GPU memory usage for all available frameworks.
    
    Returns:
        Dictionary mapping framework names to memory usage info
    """
    memory_info = {}
    
    # PyTorch
    if torch is not None and hasattr(torch, 'cuda') and torch.cuda.is_available():
        try:
            device_count = torch.cuda.device_count()
            memory_info['torch'] = {
                'device_count': device_count,
                'devices': []
            }
            for i in range(device_count):
                allocated = torch.cuda.memory_allocated(i) / 1024**3  # GB
                reserved = torch.cuda.memory_reserved(i) / 1024**3  # GB
                memory_info['torch']['devices'].append({
                    'device_id': i,
                    'allocated_gb': allocated,
                    'reserved_gb': reserved
                })
        except Exception as e:
            logger.warning(f"Failed to get PyTorch memory info: {e}")
    
    # CuPy
    if cupy is not None and hasattr(cupy, 'cuda'):
        try:
            device_count = cupy.cuda.runtime.getDeviceCount()
            memory_info['cupy'] = {
                'device_count': device_count,
                'devices': []
            }
            for i in range(device_count):
                with cupy.cuda.Device(i):
                    pool = cupy.get_default_memory_pool()
                    used = pool.used_bytes() / 1024**3  # GB
                    total = pool.total_bytes() / 1024**3  # GB
                    memory_info['cupy']['devices'].append({
                        'device_id': i,
                        'used_gb': used,
                        'total_gb': total
                    })
        except Exception as e:
            logger.warning(f"Failed to get CuPy memory info: {e}")
    
    # TensorFlow
    if tensorflow is not None:
        try:
            gpus = tensorflow.config.list_physical_devices('GPU')
            memory_info['tensorflow'] = {
                'device_count': len(gpus),
                'devices': [{'device_id': i, 'name': gpu.name} for i, gpu in enumerate(gpus)]
            }
        except Exception as e:
            logger.warning(f"Failed to get TensorFlow memory info: {e}")
    
    # JAX
    if jax is not None:
        try:
            devices = [d for d in jax.devices() if d.platform == 'gpu']
            memory_info['jax'] = {
                'device_count': len(devices),
                'devices': [{'device_id': i, 'platform': d.platform} for i, d in enumerate(devices)]
            }
        except Exception as e:
            logger.warning(f"Failed to get JAX memory info: {e}")
    
    return memory_info


# Export all cleanup functions and utilities
__all__ = [
    'is_gpu_memory_type',
    'cleanup_all_gpu_frameworks',
    'check_gpu_memory_usage',
    'log_gpu_memory_usage',
    'MEMORY_TYPE_CLEANUP_REGISTRY',
    'cleanup_numpy_gpu',
    'cleanup_cupy_gpu',
    'cleanup_torch_gpu',
    'cleanup_tensorflow_gpu',
    'cleanup_jax_gpu',
    'cleanup_pyclesperanto_gpu',
]

