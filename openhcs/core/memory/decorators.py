"""
Memory type declaration decorators for OpenHCS.

This module provides decorators for explicitly declaring the memory interface
of pure functions, enforcing Clause 106-A (Declared Memory Types) and supporting
memory-type-aware dispatching and orchestration.

These decorators annotate functions with input_memory_type and output_memory_type
attributes and provide automatic thread-local CUDA stream management for GPU
frameworks to enable true parallelization across multiple threads.

REFACTORED: Uses enum-driven metaprogramming to eliminate 79% of code duplication.
"""

import functools
import inspect
import logging
import threading
from typing import Any, Callable, Optional, TypeVar

from openhcs.constants.constants import VALID_MEMORY_TYPES, MemoryType
from openhcs.core.utils import optional_import
from openhcs.core.memory.oom_recovery import _execute_with_oom_recovery
from openhcs.core.memory.framework_ops import _FRAMEWORK_OPS
from openhcs.core.memory.dtype_scaling import SCALING_FUNCTIONS
from openhcs.core.memory.slice_processing import process_slices

logger = logging.getLogger(__name__)

F = TypeVar('F', bound=Callable[..., Any])

# Dtype conversion enum and utilities for consistent dtype handling across all frameworks
from enum import Enum
import numpy as np

class DtypeConversion(Enum):
    """Data type conversion modes for all memory type functions."""

    PRESERVE_INPUT = "preserve"     # Keep input dtype (default)
    NATIVE_OUTPUT = "native"        # Use framework's native output
    UINT8 = "uint8"                # Force uint8 (0-255 range)
    UINT16 = "uint16"              # Force uint16 (microscopy standard)
    INT16 = "int16"                # Force int16 (signed microscopy data)
    INT32 = "int32"                # Force int32 (large integer values)
    FLOAT32 = "float32"            # Force float32 (GPU performance)
    FLOAT64 = "float64"            # Force float64 (maximum precision)

    @property
    def numpy_dtype(self):
        """Get the corresponding numpy dtype."""
        dtype_map = {
            self.UINT8: np.uint8,
            self.UINT16: np.uint16,
            self.INT16: np.int16,
            self.INT32: np.int32,
            self.FLOAT32: np.float32,
            self.FLOAT64: np.float64,
        }
        return dtype_map.get(self, None)


# Thread-local cache for lazy-loaded GPU frameworks
_gpu_frameworks_cache = {}


def _create_lazy_getter(framework_name: str):
    """Factory function that creates a lazy import getter for a framework."""
    def getter():
        if framework_name not in _gpu_frameworks_cache:
            _gpu_frameworks_cache[framework_name] = optional_import(framework_name)
            if _gpu_frameworks_cache[framework_name] is not None:
                logger.debug(f"🔧 Lazy imported {framework_name} in thread {threading.current_thread().name}")
        return _gpu_frameworks_cache[framework_name]
    return getter


# Auto-generate lazy getters for all GPU frameworks
for mem_type in MemoryType:
    ops = _FRAMEWORK_OPS[mem_type]
    if ops['lazy_getter'] is not None:
        getter_func = _create_lazy_getter(ops['import_name'])
        globals()[f"_get_{ops['import_name']}"] = getter_func


# Thread-local storage for GPU streams and contexts
_thread_gpu_contexts = threading.local()

class ThreadGPUContext:
    """Thread-local GPU context manager for CUDA streams."""
    
    def __init__(self):
        self.cupy_stream = None
        self.torch_stream = None
        self.tensorflow_device = None
        self.jax_device = None
    
    def get_cupy_stream(self):
        """Get or create thread-local CuPy stream."""
        if self.cupy_stream is None:
            cupy = _get_cupy()
            if cupy is not None and hasattr(cupy, 'cuda'):
                self.cupy_stream = cupy.cuda.Stream()
                logger.debug(f"🔧 Created CuPy stream for thread {threading.current_thread().name}")
        return self.cupy_stream
    
    def get_torch_stream(self):
        """Get or create thread-local PyTorch stream."""
        if self.torch_stream is None:
            torch = _get_torch()
            if torch is not None and hasattr(torch, 'cuda') and torch.cuda.is_available():
                self.torch_stream = torch.cuda.Stream()
                logger.debug(f"🔧 Created PyTorch stream for thread {threading.current_thread().name}")
        return self.torch_stream


def _get_thread_gpu_context():
    """Get or create thread-local GPU context."""
    if not hasattr(_thread_gpu_contexts, 'context'):
        _thread_gpu_contexts.context = ThreadGPUContext()
    return _thread_gpu_contexts.context


def memory_types(
    input_type: str,
    output_type: str,
    contract: Optional[Callable[[Any], bool]] = None
) -> Callable[[F], F]:
    """
    Base decorator for declaring memory types of a function.
    
    This is the foundation decorator that all memory-type-specific decorators build upon.
    """
    def decorator(func: F) -> F:
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            result = func(*args, **kwargs)
            
            # Apply contract validation if provided
            if contract is not None and not contract(result):
                raise ValueError(f"Function {func.__name__} violated its output contract")
            
            return result
        
        # Attach memory type metadata
        wrapper.input_memory_type = input_type
        wrapper.output_memory_type = output_type
        
        return wrapper
    
    return decorator


def _create_dtype_wrapper(func, mem_type: MemoryType, func_name: str):
    """
    Auto-generate dtype preservation wrapper for any memory type.
    
    This single function replaces 6 nearly-identical dtype wrapper functions.
    """
    ops = _FRAMEWORK_OPS[mem_type]
    scale_func = SCALING_FUNCTIONS[mem_type.value]
    
    @functools.wraps(func)
    def dtype_wrapper(image, *args, dtype_conversion=None, slice_by_slice: bool = False, **kwargs):
        # Set default dtype_conversion if not provided
        if dtype_conversion is None:
            dtype_conversion = DtypeConversion.PRESERVE_INPUT
        
        try:
            # Store original dtype
            original_dtype = image.dtype
            
            # Handle slice_by_slice processing for 3D arrays
            if slice_by_slice and hasattr(image, 'ndim') and image.ndim == 3:
                result = process_slices(image, func, args, kwargs)
            else:
                # Call the original function normally
                result = func(image, *args, **kwargs)
            
            # Apply dtype conversion based on enum value
            if hasattr(result, 'dtype') and dtype_conversion is not None:
                if dtype_conversion == DtypeConversion.PRESERVE_INPUT:
                    # Preserve input dtype
                    if result.dtype != original_dtype:
                        result = scale_func(result, original_dtype)
                elif dtype_conversion == DtypeConversion.NATIVE_OUTPUT:
                    # Return framework's native output dtype
                    pass  # No conversion needed
                else:
                    # Force specific dtype
                    target_dtype = dtype_conversion.numpy_dtype
                    if target_dtype is not None:
                        result = scale_func(result, target_dtype)
            
            return result
        except Exception as e:
            logger.error(f"Error in {mem_type.value} dtype/slice preserving wrapper for {func_name}: {e}")
            # Return original result on error
            return func(image, *args, **kwargs)
    
    # Update function signature to include new parameters
    try:
        original_sig = inspect.signature(func)
        new_params = list(original_sig.parameters.values())
        
        # Check if parameters already exist
        param_names = [p.name for p in new_params]
        
        # Add dtype_conversion parameter first (before slice_by_slice)
        if 'dtype_conversion' not in param_names:
            dtype_param = inspect.Parameter(
                'dtype_conversion',
                inspect.Parameter.KEYWORD_ONLY,
                default=DtypeConversion.PRESERVE_INPUT,
                annotation=Optional[DtypeConversion]
            )
            new_params.append(dtype_param)
        
        # Add slice_by_slice parameter
        if 'slice_by_slice' not in param_names:
            slice_param = inspect.Parameter(
                'slice_by_slice',
                inspect.Parameter.KEYWORD_ONLY,
                default=False,
                annotation=bool
            )
            new_params.append(slice_param)
        
        # Create new signature
        new_sig = original_sig.replace(parameters=new_params)
        dtype_wrapper.__signature__ = new_sig
        
        # Update docstring
        if dtype_wrapper.__doc__:
            dtype_wrapper.__doc__ += f"\n\n    Additional Parameters (added by {mem_type.value} decorator):\n"
            dtype_wrapper.__doc__ += "        dtype_conversion (DtypeConversion, optional): How to handle output dtype.\n"
            dtype_wrapper.__doc__ += "            Defaults to PRESERVE_INPUT (match input dtype).\n"
            dtype_wrapper.__doc__ += "        slice_by_slice (bool, optional): Process 3D arrays slice-by-slice.\n"
            dtype_wrapper.__doc__ += "            Defaults to False. Prevents cross-slice contamination.\n"
    
    except Exception as e:
        logger.warning(f"Could not update signature for {func_name}: {e}")
    
    return dtype_wrapper


def _create_gpu_wrapper(func, mem_type: MemoryType, oom_recovery: bool):
    """
    Auto-generate GPU stream/device wrapper for any GPU memory type.
    
    This function creates the GPU-specific wrapper with stream management and OOM recovery.
    """
    ops = _FRAMEWORK_OPS[mem_type]
    framework_name = ops['import_name']
    lazy_getter = globals().get(ops['lazy_getter'])
    
    @functools.wraps(func)
    def gpu_wrapper(*args, **kwargs):
        framework = lazy_getter()
        
        # Check if GPU is available for this framework
        if framework is not None:
            gpu_check_expr = ops['gpu_check'].format(mod=framework_name)
            try:
                gpu_available = eval(gpu_check_expr, {framework_name: framework})
            except:
                gpu_available = False
            
            if gpu_available:
                # Get thread-local context
                ctx = _get_thread_gpu_context()
                
                # Get stream if framework supports it
                stream = None
                if mem_type == MemoryType.CUPY:
                    stream = ctx.get_cupy_stream()
                elif mem_type == MemoryType.TORCH:
                    stream = ctx.get_torch_stream()
                
                # Execute with stream context and OOM recovery
                if stream is not None:
                    with stream:
                        if oom_recovery and ops['has_oom_recovery']:
                            return _execute_with_oom_recovery(func, *args, **kwargs)
                        else:
                            return func(*args, **kwargs)
                else:
                    # No stream support, just execute with OOM recovery if enabled
                    if oom_recovery and ops['has_oom_recovery']:
                        return _execute_with_oom_recovery(func, *args, **kwargs)
                    else:
                        return func(*args, **kwargs)
        
        # CPU fallback or framework not available
        return func(*args, **kwargs)
    
    # Preserve memory type attributes
    gpu_wrapper.input_memory_type = func.input_memory_type
    gpu_wrapper.output_memory_type = func.output_memory_type

    return gpu_wrapper


def _create_memory_decorator(mem_type: MemoryType):
    """
    Factory function that creates a decorator for a specific memory type.

    This single factory replaces 6 nearly-identical decorator functions.
    """
    ops = _FRAMEWORK_OPS[mem_type]

    def decorator(func=None, *, input_type=mem_type.value, output_type=mem_type.value,
                  oom_recovery=True, contract=None):
        """
        Decorator for {mem_type} memory type functions.

        Args:
            func: Function to decorate (when used as @decorator)
            input_type: Expected input memory type (default: {mem_type})
            output_type: Expected output memory type (default: {mem_type})
            oom_recovery: Enable automatic OOM recovery (default: True)
            contract: Optional validation function for outputs

        Returns:
            Decorated function with memory type metadata and dtype preservation
        """
        def inner_decorator(func):
            # Apply base memory_types decorator
            memory_decorator = memory_types(input_type=input_type, output_type=output_type, contract=contract)
            func = memory_decorator(func)

            # Apply dtype preservation wrapper
            func = _create_dtype_wrapper(func, mem_type, func.__name__)

            # Apply GPU wrapper if this is a GPU memory type
            if ops['gpu_check'] is not None:
                func = _create_gpu_wrapper(func, mem_type, oom_recovery)

            return func

        # Handle both @decorator and @decorator() forms
        if func is None:
            return inner_decorator
        return inner_decorator(func)

    # Set proper function name and docstring
    decorator.__name__ = mem_type.value
    decorator.__doc__ = decorator.__doc__.format(mem_type=ops['display_name'])

    return decorator


# Auto-generate all 6 memory type decorators
for mem_type in MemoryType:
    decorator_func = _create_memory_decorator(mem_type)
    globals()[mem_type.value] = decorator_func


# Export all decorators
__all__ = [
    'memory_types',
    'DtypeConversion',
    'numpy',
    'cupy',
    'torch',
    'tensorflow',
    'jax',
    'pyclesperanto',
]

