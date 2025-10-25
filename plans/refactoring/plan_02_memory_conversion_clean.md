# plan_02_memory_conversion_clean.md
## Component: Memory Conversion System

### Objective

Eliminate 1,567 lines of duplication using enum-driven metaprogramming. Remove unused `allow_cpu_roundtrip` flag. **Completely eliminate MemoryWrapper** - it's unnecessary overhead that's already being bypassed.

**Target**: 2,144 lines → ~150 lines (93% reduction)
- Delete `conversion_functions.py` (1,567 lines)
- Delete `wrapper.py` (402 lines)
- Simplify `converters.py` (175 lines → ~50 lines)

---

### Plan

#### 1. Create ABC with Polymorphic Conversion

**File**: `openhcs/core/memory/conversion_helpers.py`

```python
from abc import ABC, abstractmethod
from openhcs.constants.constants import MemoryType
from openhcs.core.memory.utils import _ensure_module, _supports_dlpack
import logging
import numpy as np

logger = logging.getLogger(__name__)

class MemoryTypeConverter(ABC):
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

# Auto-generate all to_X() methods using polymorphism
def _add_converter_methods():
    """Add to_X() methods to MemoryTypeConverter ABC.

    NOTE: This must be called AFTER _CONVERTERS is defined (see Step 2).
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

# NOTE: _add_converter_methods() is called at the END of this file, after _CONVERTERS is defined
```

---

#### 2. Define Type-Specific Operations

**File**: `openhcs/core/memory/conversion_helpers.py`

Pure data as strings, then metaprogram everything.

```python
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
_TYPE_OPERATIONS = {
    mem_type: {
        method_name: (
            eval(f'lambda data, gpu_id: {expr.format(mod=f"_ensure_module(\"{mem_type.value}\")")}')
            if expr is not None
            else lambda data, gpu_id: (_ for _ in ()).throw(NotImplementedError(f"DLPack not supported for {mem_type.value}"))
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
```

---

#### 3. Extend MemoryType Enum

**File**: `openhcs/constants/constants.py`

```python
class MemoryType(Enum):
    NUMPY = "numpy"
    CUPY = "cupy"
    TORCH = "torch"
    TENSORFLOW = "tensorflow"
    JAX = "jax"
    PYCLESPERANTO = "pyclesperanto"
    
    @property
    def converter(self):
        from openhcs.core.memory.conversion_helpers import _CONVERTERS
        return _CONVERTERS[self]

# Auto-generate to_X() methods on enum
def _add_conversion_methods():
    for target_type in MemoryType:
        method_name = f"to_{target_type.value}"
        def make_method(target):
            def method(self, data, gpu_id):
                return getattr(self.converter, f"to_{target.value}")(data, gpu_id)
            return method
        setattr(MemoryType, method_name, make_method(target_type))

_add_conversion_methods()
```

---

#### 4. Update Public API and Add Memory Type Detection

**File**: `openhcs/core/memory/converters.py`

Replace entire file with simplified version:
```python
"""Memory conversion public API for OpenHCS."""

from typing import Any
import numpy as np
from openhcs.constants.constants import MemoryType

def convert_memory(data: Any, source_type: str, target_type: str, gpu_id: int) -> Any:
    """
    Convert data between memory types.

    Args:
        data: The data to convert
        source_type: The source memory type (e.g., "numpy", "torch")
        target_type: The target memory type (e.g., "cupy", "jax")
        gpu_id: The target GPU device ID

    Returns:
        The converted data in the target memory type

    Raises:
        ValueError: If source_type or target_type is invalid
        MemoryConversionError: If conversion fails
    """
    source_enum = MemoryType(source_type)
    return getattr(source_enum, f"to_{target_type}")(data, gpu_id)


def detect_memory_type(data: Any) -> str:
    """
    Detect the memory type of data.

    Args:
        data: The data to detect

    Returns:
        The detected memory type string (e.g., "numpy", "torch")

    Raises:
        ValueError: If memory type cannot be detected
    """
    # NumPy
    if isinstance(data, np.ndarray):
        return MemoryType.NUMPY.value

    # CuPy
    if type(data).__module__.startswith('cupy'):
        return MemoryType.CUPY.value

    # PyTorch
    if type(data).__module__.startswith('torch'):
        return MemoryType.TORCH.value

    # TensorFlow
    if 'tensorflow' in type(data).__module__:
        return MemoryType.TENSORFLOW.value

    # JAX
    if type(data).__module__.startswith('jax'):
        return MemoryType.JAX.value

    # pyclesperanto
    if 'pyclesperanto' in type(data).__module__:
        return MemoryType.PYCLESPERANTO.value

    raise ValueError(f"Unknown memory type for {type(data)}")


def validate_memory_type(memory_type: str) -> None:
    """
    Validate that a memory type string is supported.

    Args:
        memory_type: The memory type to validate

    Raises:
        ValueError: If memory type is not supported
    """
    try:
        MemoryType(memory_type)
    except ValueError:
        valid_types = [t.value for t in MemoryType]
        raise ValueError(f"Invalid memory type '{memory_type}'. Valid types: {valid_types}")


def validate_data_compatibility(data: Any, memory_type: str) -> None:
    """
    Validate that data matches the declared memory type.

    Args:
        data: The data to validate
        memory_type: The declared memory type

    Raises:
        ValueError: If data doesn't match the declared type
    """
    detected = detect_memory_type(data)
    if detected != memory_type:
        raise ValueError(f"Data type mismatch: declared '{memory_type}' but detected '{detected}'")
```

---

#### 5. Cleanup Old Implementation

**Delete entire files**:
- `openhcs/core/memory/conversion_functions.py` (1,567 lines)
- `openhcs/core/memory/wrapper.py` (402 lines)

**Update `openhcs/core/memory/__init__.py`**:
```python
"""Memory module for OpenHCS."""

from openhcs.constants.constants import MemoryType
from .decorators import cupy, jax, memory_types, numpy, tensorflow, torch
from .converters import convert_memory, detect_memory_type

# Define memory type constants
MEMORY_TYPE_NUMPY = MemoryType.NUMPY.value
MEMORY_TYPE_CUPY = MemoryType.CUPY.value
MEMORY_TYPE_TORCH = MemoryType.TORCH.value
MEMORY_TYPE_TENSORFLOW = MemoryType.TENSORFLOW.value
MEMORY_TYPE_JAX = MemoryType.JAX.value
MEMORY_TYPE_PYCLESPERANTO = MemoryType.PYCLESPERANTO.value

__all__ = [
    'convert_memory',
    'detect_memory_type',
    'MEMORY_TYPE_NUMPY',
    'MEMORY_TYPE_CUPY',
    'MEMORY_TYPE_TORCH',
    'MEMORY_TYPE_TENSORFLOW',
    'MEMORY_TYPE_JAX',
    'MEMORY_TYPE_PYCLESPERANTO',
    'memory_types',
    'numpy',
    'cupy',
    'torch',
    'tensorflow',
    'jax',
]
```

**Update `openhcs/core/memory/stack_utils.py`**:
- Remove `from openhcs.core.memory import MemoryWrapper`
- Remove `if isinstance(data, MemoryWrapper):` check in `_detect_memory_type()`
- Use `from openhcs.core.memory.converters import detect_memory_type` instead
- Already using direct `convert_memory()` calls (no changes needed there)

**Update all code using MemoryWrapper**:
Replace pattern:
```python
# Old
wrapped = MemoryWrapper(data, source_type, gpu_id)
converted = wrapped.to_torch()
```

With:
```python
# New
converted = convert_memory(data, source_type, "torch", gpu_id)
```

**Update documentation**:
- Remove all MemoryWrapper references from docs
- Update examples to use `convert_memory()` directly
- Update `docs/architecture/memory-type-system.md`

---

### Findings

**Files affected**:
- `openhcs/core/memory/conversion_functions.py` (1,567 lines) - **DELETE**
- `openhcs/core/memory/wrapper.py` (402 lines) - **DELETE**
- `openhcs/core/memory/converters.py` (175 lines → ~100 lines) - Complete rewrite
- `openhcs/core/memory/conversion_helpers.py` - **NEW** (~150 lines)
- `openhcs/core/memory/__init__.py` - Remove MemoryWrapper export
- `openhcs/core/memory/stack_utils.py` - Remove MemoryWrapper usage
- `openhcs/constants/constants.py` (292 lines) - Extend enum

**Key insights**:
1. **MemoryWrapper is unnecessary overhead**:
   - Only 38 references in entire codebase
   - Already being bypassed for performance ("Direct conversion without MemoryWrapper overhead")
   - Direct `convert_memory()` is simpler: 1 line vs 2 lines
   - Eliminates object creation overhead

2. Every conversion is either:
   - Identity (same type)
   - GPU-to-GPU via DLPack (try first, log warning if fails)
   - CPU roundtrip via NumPy (always works)

3. All 30 conversions follow identical pattern - only 4 operations differ per type:
   - `to_numpy()` - extract to CPU
   - `from_numpy()` - create from CPU
   - `from_dlpack()` - create from DLPack capsule
   - `move_to_device()` - move to specific GPU

4. Memory type detection is just isinstance checks - move to converters.py

---

### Implementation Draft

(Code will be written here after smell loop approval)

---

### Validation

**API changes**:
- Removed `allow_cpu_roundtrip` parameter from all functions
- Signature: `convert_memory(data, source_type, target_type, gpu_id)`
- Always falls back to CPU roundtrip with warning
- **Completely removed MemoryWrapper class**
- New public API: `convert_memory()`, `detect_memory_type()`, `validate_memory_type()`, `validate_data_compatibility()`

**Breaking changes**:
- All code using `MemoryWrapper` must be updated:
  ```python
  # Old
  wrapped = MemoryWrapper(data, "torch", gpu_id)
  converted = wrapped.to_cupy()

  # New
  converted = convert_memory(data, "torch", "cupy", gpu_id)
  ```
- Code accessing `wrapper.data` or `wrapper.memory_type` must be refactored
- Code using `MemoryWrapper.detect_memory_type()` should use `detect_memory_type()` from converters

**Tests**:
- Update tests to remove `allow_cpu_roundtrip` calls
- Update all tests using MemoryWrapper to use convert_memory() directly
- Update tests that import MemoryWrapper
- All conversions must still work
- Verify warnings logged when DLPack fails

**Metrics**:
- **2,144 lines → ~150 lines (93% reduction)**
- Deleted files: conversion_functions.py (1,567 lines) + wrapper.py (402 lines)
- 30 conversion functions → 24 methods (6 types × 4 methods)
- 36-branch dispatch → 1-line polymorphic call
- 2 helper functions with if/elif chains → eliminated via polymorphism
- 1 unnecessary abstraction layer (MemoryWrapper) → eliminated

