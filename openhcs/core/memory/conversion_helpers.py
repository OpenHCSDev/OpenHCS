"""
Memory conversion helpers for OpenHCS.

This module provides the ABC and metaprogramming infrastructure for memory type conversions.
Uses enum-driven polymorphism to eliminate 1,567 lines of duplication.
"""

from abc import ABC, abstractmethod
from openhcs.constants.constants import MemoryType
from openhcs.core.memory.utils import _ensure_module, _supports_dlpack
import logging
import numpy as np

logger = logging.getLogger(__name__)


class MemoryTypeConverter(ABC):
    """Abstract base class for memory type converters.
    
    Each memory type (numpy, cupy, torch, etc.) has a concrete converter
    that implements these four core operations. All to_X() methods are
    auto-generated using polymorphism.
    """
    
    @abstractmethod
    def to_numpy(self, data, gpu_id):
        """Extract to NumPy (type-specific implementation)."""
        pass

    @abstractmethod
    def from_numpy(self, data, gpu_id):
        """Create from NumPy (type-specific implementation)."""
        pass

    @abstractmethod
    def from_dlpack(self, data, gpu_id):
        """Create from DLPack capsule (type-specific implementation)."""
        pass

    @abstractmethod
    def move_to_device(self, data, gpu_id):
        """Move data to specified GPU device if needed (type-specific implementation)."""
        pass


def _add_converter_methods():
    """Add to_X() methods to MemoryTypeConverter ABC.
    
    NOTE: This must be called AFTER _CONVERTERS is defined (see below).
    
    For each target memory type, generates a method like to_cupy(), to_torch(), etc.
    that tries GPU-to-GPU conversion via DLPack first, then falls back to CPU roundtrip.
    """
    for target_type in MemoryType:
        method_name = f"to_{target_type.value}"
        
        def make_method(tgt):
            def method(self, data, gpu_id):
                # Try GPU-to-GPU first (DLPack)
                if _supports_dlpack(data):
                    try:
                        target_converter = _CONVERTERS[tgt]
                        result = target_converter.from_dlpack(data, gpu_id)
                        return target_converter.move_to_device(result, gpu_id)
                    except Exception as e:
                        logger.warning(f"DLPack conversion failed: {e}. Using CPU roundtrip.")
                
                # CPU roundtrip using polymorphism
                numpy_data = self.to_numpy(data, gpu_id)
                target_converter = _CONVERTERS[tgt]
                return target_converter.from_numpy(numpy_data, gpu_id)
            return method
        
        setattr(MemoryTypeConverter, method_name, make_method(target_type))


# Pure data - just the operations (module name from enum)
# Using dicts instead of tuples eliminates fragile zip() with magic string lists
_OPS = {
    MemoryType.NUMPY: {
        'to_numpy': 'data',
        'from_numpy': 'data',
        'from_dlpack': None,
        'move_to_device': 'data',
    },
    MemoryType.CUPY: {
        'to_numpy': 'data.get()',
        'from_numpy': '({mod}.cuda.Device(gpu_id), {mod}.array(data))[1]',
        'from_dlpack': '{mod}.from_dlpack(data)',
        'move_to_device': 'data if data.device.id == gpu_id else ({mod}.cuda.Device(gpu_id), {mod}.array(data))[1]',
    },
    MemoryType.TORCH: {
        'to_numpy': 'data.cpu().numpy()',
        'from_numpy': '{mod}.from_numpy(data).cuda(gpu_id)',
        'from_dlpack': '{mod}.from_dlpack(data)',
        'move_to_device': 'data if data.device.index == gpu_id else data.cuda(gpu_id)',
    },
    MemoryType.TENSORFLOW: {
        'to_numpy': 'data.numpy()',
        'from_numpy': '{mod}.convert_to_tensor(data)',
        'from_dlpack': '{mod}.experimental.dlpack.from_dlpack(data)',
        'move_to_device': 'data',
    },
    MemoryType.JAX: {
        'to_numpy': 'np.asarray(data)',
        'from_numpy': '{mod}.device_put(data, {mod}.devices()[gpu_id])',
        'from_dlpack': '{mod}.dlpack.from_dlpack(data)',
        'move_to_device': 'data',
    },
    MemoryType.PYCLESPERANTO: {
        'to_numpy': '{mod}.pull(data)',
        'from_numpy': '{mod}.push(data)',
        'from_dlpack': None,
        'move_to_device': 'data',
    },
}

# Auto-generate lambdas from strings
def _make_not_implemented(mem_type_value, method_name):
    """Create a lambda that raises NotImplementedError with the correct signature."""
    def not_impl(self, data, gpu_id):
        raise NotImplementedError(f"DLPack not supported for {mem_type_value}")
    # Add proper names for better debugging
    not_impl.__name__ = method_name
    not_impl.__qualname__ = f'{mem_type_value.capitalize()}Converter.{method_name}'
    return not_impl

def _make_lambda_with_name(expr_str, mem_type, method_name):
    """Create a lambda from expression string and add proper __name__ for debugging."""
    lambda_func = eval(f'lambda self, data, gpu_id: {expr_str.format(mod=f"_ensure_module(\"{mem_type.value}\")")}')
    lambda_func.__name__ = method_name
    lambda_func.__qualname__ = f'{mem_type.value.capitalize()}Converter.{method_name}'
    return lambda_func

_TYPE_OPERATIONS = {
    mem_type: {
        method_name: (
            _make_lambda_with_name(expr, mem_type, method_name)
            if expr is not None
            else _make_not_implemented(mem_type.value, method_name)
        )
        for method_name, expr in ops.items()  # Iterate over dict items - self-documenting!
    }
    for mem_type, ops in _OPS.items()
}

# Auto-generate all 6 converter classes
_CONVERTERS = {
    mem_type: type(
        f"{mem_type.value.capitalize()}Converter",
        (MemoryTypeConverter,),
        _TYPE_OPERATIONS[mem_type]
    )()
    for mem_type in MemoryType
}

# NOW call _add_converter_methods() after _CONVERTERS exists
_add_converter_methods()


# Runtime validation: ensure all converters have required methods
def _validate_converters():
    """Validate that all generated converters have the required methods."""
    required_methods = ['to_numpy', 'from_numpy', 'from_dlpack', 'move_to_device']

    for mem_type, converter in _CONVERTERS.items():
        # Check ABC methods
        for method in required_methods:
            if not hasattr(converter, method):
                raise RuntimeError(f"{mem_type.value} converter missing method: {method}")

        # Check to_X() methods for all memory types
        for target_type in MemoryType:
            method_name = f'to_{target_type.value}'
            if not hasattr(converter, method_name):
                raise RuntimeError(f"{mem_type.value} converter missing method: {method_name}")

    logger.debug(f"✅ Validated {len(_CONVERTERS)} memory type converters")

# Run validation at module load time
_validate_converters()

