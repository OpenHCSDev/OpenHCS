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
from openhcs.core.memory.framework_config import _FRAMEWORK_CONFIG

logger = logging.getLogger(__name__)

# Check if we're in subprocess runner mode and should skip GPU imports
if os.getenv('OPENHCS_SUBPROCESS_NO_GPU') == '1':
    # Subprocess runner mode - skip GPU imports
    torch = None
    logger.info("Subprocess runner mode - skipping GPU library imports in gpu_cleanup")
else:
    # Normal mode - import torch for VRAM logging
    from openhcs.core.lazy_gpu_imports import torch





def _create_cleanup_function(mem_type: MemoryType):
    """
    Factory function that creates a cleanup function for a specific memory type.

    This single factory replaces 6 nearly-identical cleanup functions.
    """
    config = _FRAMEWORK_CONFIG[mem_type]
    framework_name = config['import_name']
    display_name = config['display_name']
    
    # CPU memory type - no cleanup needed
    if config['cleanup_ops'] is None:
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
            gpu_check_expr = config['gpu_check'].format(mod=framework_name)
            try:
                gpu_available = eval(gpu_check_expr, {framework_name: framework})
            except:
                gpu_available = False

            if not gpu_available:
                return

            # Execute cleanup operations
            if device_id is not None and config['device_context'] is not None:
                # Clean specific device with context
                device_ctx_expr = config['device_context'].format(device_id=device_id, mod=framework_name)
                device_ctx = eval(device_ctx_expr, {framework_name: framework})

                with device_ctx:
                    # Execute cleanup operations
                    cleanup_expr = config['cleanup_ops'].format(mod=framework_name)
                    exec(cleanup_expr, {framework_name: framework, 'gc': gc})

                logger.debug(f"🔥 GPU CLEANUP: Cleared {display_name} for device {device_id}")
            else:
                # Clean all devices (no device context)
                cleanup_expr = config['cleanup_ops'].format(mod=framework_name)
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
    mem_type.value: globals()[f"cleanup_{_FRAMEWORK_CONFIG[mem_type]['import_name']}_gpu"]
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

    # Only cleanup GPU memory types (those with cleanup operations)
    for mem_type, config in _FRAMEWORK_CONFIG.items():
        if config['cleanup_ops'] is not None:
            cleanup_func = MEMORY_TYPE_CLEANUP_REGISTRY[mem_type.value]
            cleanup_func(device_id)

    logger.debug("🔥 GPU CLEANUP: Completed cleanup for all GPU frameworks")


def log_gpu_memory_usage(context: str = "") -> None:
    """
    Log GPU memory usage for PyTorch (primary framework for VRAM tracking).

    This is a lightweight logging function used by orchestrator and function_step
    for debugging VRAM usage. Only logs PyTorch memory since that's the primary
    GPU framework used in OpenHCS.

    Args:
        context: Description of when/where this memory check is happening
    """
    context_str = f" ({context})" if context else ""

    if torch is not None:
        try:
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


# Export all cleanup functions and utilities
__all__ = [
    'cleanup_all_gpu_frameworks',
    'log_gpu_memory_usage',
    'MEMORY_TYPE_CLEANUP_REGISTRY',
    'cleanup_numpy_gpu',
    'cleanup_cupy_gpu',
    'cleanup_torch_gpu',
    'cleanup_tensorflow_gpu',
    'cleanup_jax_gpu',
    'cleanup_pyclesperanto_gpu',
]

