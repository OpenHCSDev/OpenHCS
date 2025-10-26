# plan_03_memory_decorators_cleanup.md
## Component: Memory Type Decorators and GPU Cleanup

### Objective
Eliminate 70%+ of code duplication in `decorators.py` (1,940 lines) and `gpu_cleanup.py` (454 lines) using enum-driven metaprogramming, following the same architectural principles that achieved 93% reduction in the conversion system.

**Target**: 2,393 lines → ~700 lines (71% reduction)

---

## Current State Analysis

### File: `openhcs/core/memory/decorators.py` (1,940 lines)

#### Identified Duplication Patterns

**1. Memory Type Decorators (6 nearly-identical functions: 540 lines)**
- `numpy()` (lines 504-543): 39 lines
- `cupy()` (lines 545-612): 67 lines  
- `torch()` (lines 614-688): 74 lines
- `tensorflow()` (lines 690-757): 67 lines
- `jax()` (lines 759-833): 74 lines
- `pyclesperanto()` (lines 835-895): 60 lines

**Pattern**: Each decorator follows identical structure:
```python
def <memory_type>(func=None, *, input_type="<type>", output_type="<type>", 
                  oom_recovery=True, contract=None):
    def decorator(func):
        # 1. Apply memory_types() decorator
        memory_decorator = memory_types(input_type=input_type, output_type=output_type, contract=contract)
        func = memory_decorator(func)
        
        # 2. Apply dtype preservation wrapper
        func = _create_<type>_dtype_preserving_wrapper(func, func.__name__)
        
        # 3. Add GPU stream/device wrapper (GPU types only)
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            <framework> = _get_<framework>()
            if <framework> is not None and <gpu_check>:
                # Get stream/device context
                # Execute with OOM recovery if enabled
            else:
                return func(*args, **kwargs)
        
        # 4. Preserve memory type attributes
        wrapper.input_memory_type = func.input_memory_type
        wrapper.output_memory_type = func.output_memory_type
        return wrapper
    
    # Handle both @decorator and @decorator() forms
    if func is None:
        return decorator
    return decorator(func)
```

**Duplication**: 90% of code is identical structure, only differs in:
- Memory type name string
- Framework getter function name
- GPU availability check expression
- Stream/device context manager type

**2. Dtype Preservation Wrappers (6 nearly-identical functions: 900 lines)**
- `_create_numpy_dtype_preserving_wrapper()` (lines 901-1054): 153 lines
- `_create_cupy_dtype_preserving_wrapper()` (lines 1056-1209): 153 lines
- `_create_torch_dtype_preserving_wrapper()` (lines 1211-1364): 153 lines
- `_create_tensorflow_dtype_preserving_wrapper()` (lines 1366-1519): 153 lines
- `_create_jax_dtype_preserving_wrapper()` (lines 1521-1674): 153 lines
- `_create_pyclesperanto_dtype_preserving_wrapper()` (lines 1676-1829): 153 lines

**Pattern**: Each wrapper follows identical structure:
```python
def _create_<type>_dtype_preserving_wrapper(original_func, func_name):
    @wraps(original_func)
    def <type>_dtype_and_slice_preserving_wrapper(image, *args, dtype_conversion=None, slice_by_slice=False, **kwargs):
        # Set default dtype_conversion
        if dtype_conversion is None:
            dtype_conversion = DtypeConversion.PRESERVE_INPUT
        
        try:
            # Import framework (optional)
            <framework> = optional_import("<framework>")
            if <framework> is None:
                return original_func(image, *args, **kwargs)
            
            # Store original dtype
            original_dtype = image.dtype
            
            # Handle slice_by_slice processing (IDENTICAL across all 6)
            if slice_by_slice and hasattr(image, 'ndim') and image.ndim == 3:
                # ... 40 lines of identical slice processing logic
            else:
                result = original_func(image, *args, **kwargs)
            
            # Apply dtype conversion (framework-specific scaling)
            if hasattr(result, 'dtype') and dtype_conversion is not None:
                if dtype_conversion == DtypeConversion.PRESERVE_INPUT:
                    if result.dtype != original_dtype:
                        result = _scale_and_convert_<type>(result, original_dtype)
                # ... identical enum handling
            
            return result
        except Exception as e:
            logger.error(f"Error in {<type>} dtype/slice preserving wrapper for {func_name}: {e}")
            return original_func(image, *args, **kwargs)
    
    # Update function signature (IDENTICAL 40 lines)
    # Update docstring (IDENTICAL 60 lines)
    return <type>_dtype_and_slice_preserving_wrapper
```

**Duplication**: 85% of code is identical, only differs in:
- Framework import name
- Scaling function name (`_scale_and_convert_<type>`)
- GPU device ID extraction (cupy only)

**3. Framework Lazy Import Functions (5 identical functions: 50 lines)**
- `_get_cupy()` (lines 185-192): 7 lines
- `_get_torch()` (lines 194-200): 7 lines
- `_get_tensorflow()` (lines 202-208): 7 lines
- `_get_jax()` (lines 210-216): 7 lines

**Pattern**: 100% identical except framework name
```python
def _get_<framework>():
    """Lazy import <Framework> only when needed."""
    if '<framework>' not in _gpu_frameworks_cache:
        _gpu_frameworks_cache['<framework>'] = optional_import("<framework>")
        if _gpu_frameworks_cache['<framework>'] is not None:
            logger.debug(f"🔧 Lazy imported <Framework> in thread {threading.current_thread().name}")
    return _gpu_frameworks_cache['<framework>']
```

**4. Scaling Functions (3 similar functions: 150 lines)**
- `_scale_and_convert_numpy()` (lines 58-97): 39 lines
- `_scale_and_convert_pyclesperanto()` (lines 99-151): 52 lines
- `_scale_and_convert_cupy()` (lines 153-179): 26 lines

**Pattern**: Similar logic with framework-specific operations

---

### File: `openhcs/core/memory/gpu_cleanup.py` (454 lines)

#### Identified Duplication Patterns

**1. Cleanup Functions (6 nearly-identical functions: 250 lines)**
- `cleanup_pytorch_gpu()` (lines 49-78): 29 lines
- `cleanup_cupy_gpu()` (lines 80-129): 49 lines
- `cleanup_tensorflow_gpu()` (lines 131-162): 31 lines
- `cleanup_jax_gpu()` (lines 164-191): 27 lines
- `cleanup_pyclesperanto_gpu()` (lines 193-231): 38 lines
- `cleanup_numpy_noop()` (lines 272-280): 8 lines

**Pattern**: Each cleanup function follows identical structure:
```python
def cleanup_<framework>_gpu(device_id: Optional[int] = None) -> None:
    """Clean up <Framework> GPU memory."""
    if <framework> is None:
        logger.debug("<Framework> not available, skipping cleanup")
        return
    
    try:
        # Framework-specific availability check
        if not <gpu_available_check>:
            return
        
        if device_id is not None:
            # Clean specific device
            with <device_context>(device_id):
                <cleanup_operations>
            logger.debug(f"🔥 GPU CLEANUP: Cleared <Framework> for device {device_id}")
        else:
            # Clean all devices
            <cleanup_operations>
            logger.debug("🔥 GPU CLEANUP: Cleared <Framework> for all devices")
    
    except Exception as e:
        logger.warning(f"Failed to cleanup <Framework> GPU memory: {e}")
```

**Duplication**: 80% of code is identical structure, only differs in:
- Framework variable name
- GPU availability check
- Device context manager
- Cleanup operation calls

**2. Registry Pattern (already good, but can be auto-generated)**
- `MEMORY_TYPE_CLEANUP_REGISTRY` (lines 303-310): Manual dict mapping

---

## Proposed Architecture

### Core Principle
Use the **same enum-driven metaprogramming pattern** from `plan_02_memory_conversion_clean.md`:
1. Pure data definitions (dicts) describing framework-specific operations
2. Auto-generated functions/classes using `eval()` and `type()`
3. Polymorphic dispatch through MemoryType enum

### New Structure

#### 1. Framework Operations Data (Pure Data)

```python
# openhcs/core/memory/framework_ops.py (~100 lines)

from openhcs.constants.constants import MemoryType

# Pure data - framework-specific operations as strings
_FRAMEWORK_OPS = {
    MemoryType.NUMPY: {
        'import_name': 'numpy',
        'lazy_getter': None,  # CPU, no lazy import needed
        'gpu_check': None,
        'stream_context': None,
        'cleanup_ops': None,  # CPU, no cleanup
        'scale_func': '_scale_numpy',
    },
    MemoryType.CUPY: {
        'import_name': 'cupy',
        'lazy_getter': 'cupy',
        'gpu_check': '{mod} is not None and hasattr({mod}, "cuda")',
        'stream_context': '{mod}.cuda.Stream()',
        'cleanup_ops': '{mod}.get_default_memory_pool().free_all_blocks(); {mod}.get_default_pinned_memory_pool().free_all_blocks(); {mod}.cuda.runtime.deviceSynchronize()',
        'scale_func': '_scale_cupy',
    },
    MemoryType.TORCH: {
        'import_name': 'torch',
        'lazy_getter': 'torch',
        'gpu_check': '{mod} is not None and hasattr({mod}, "cuda") and {mod}.cuda.is_available()',
        'stream_context': '{mod}.cuda.Stream()',
        'cleanup_ops': '{mod}.cuda.empty_cache(); {mod}.cuda.synchronize()',
        'scale_func': '_scale_torch',
    },
    # ... similar for tensorflow, jax, pyclesperanto
}
```

#### 2. Auto-Generated Decorators

```python
# Auto-generate all 6 memory type decorators using metaprogramming
def _create_memory_decorator(mem_type: MemoryType):
    """Factory function that creates a decorator for a specific memory type."""
    ops = _FRAMEWORK_OPS[mem_type]
    
    def decorator(func=None, *, input_type=mem_type.value, output_type=mem_type.value, 
                  oom_recovery=True, contract=None):
        def inner_decorator(func):
            # Apply base memory_types decorator
            func = memory_types(input_type=input_type, output_type=output_type, contract=contract)(func)
            
            # Apply dtype preservation (auto-generated)
            func = _create_dtype_wrapper(func, mem_type)
            
            # Apply GPU wrapper if needed (auto-generated)
            if ops['gpu_check'] is not None:
                func = _create_gpu_wrapper(func, mem_type, oom_recovery)
            
            return func
        
        return inner_decorator if func is None else inner_decorator(func)
    
    return decorator

# Auto-generate and attach to module
for mem_type in MemoryType:
    decorator_func = _create_memory_decorator(mem_type)
    decorator_func.__name__ = mem_type.value
    decorator_func.__doc__ = f"Decorator for {mem_type.value} memory type functions."
    globals()[mem_type.value] = decorator_func
```

**Result**: 6 decorators (540 lines) → ~80 lines (85% reduction)

#### 3. Auto-Generated Dtype Wrappers

```python
def _create_dtype_wrapper(func, mem_type: MemoryType):
    """Auto-generate dtype preservation wrapper for any memory type."""
    ops = _FRAMEWORK_OPS[mem_type]
    scale_func = globals()[ops['scale_func']]
    
    @functools.wraps(func)
    def dtype_wrapper(image, *args, dtype_conversion=None, slice_by_slice=False, **kwargs):
        if dtype_conversion is None:
            dtype_conversion = DtypeConversion.PRESERVE_INPUT
        
        original_dtype = image.dtype
        
        # Slice-by-slice processing (SHARED, not duplicated)
        if slice_by_slice and hasattr(image, 'ndim') and image.ndim == 3:
            result = _process_slices(image, func, args, kwargs)
        else:
            result = func(image, *args, **kwargs)
        
        # Apply dtype conversion using framework-specific scaling
        if hasattr(result, 'dtype') and dtype_conversion is not None:
            if dtype_conversion == DtypeConversion.PRESERVE_INPUT:
                if result.dtype != original_dtype:
                    result = scale_func(result, original_dtype)
            elif dtype_conversion != DtypeConversion.NATIVE_OUTPUT:
                target_dtype = dtype_conversion.numpy_dtype
                if target_dtype is not None:
                    result = scale_func(result, target_dtype)
        
        return result
    
    # Signature modification (SHARED function)
    _add_dtype_params_to_signature(dtype_wrapper, func)
    return dtype_wrapper
```

**Result**: 6 wrappers (900 lines) → ~120 lines shared + ~60 lines scaling (80% reduction)

#### 4. Auto-Generated Cleanup Functions

```python
# Auto-generate cleanup functions using enum dispatch
def _create_cleanup_function(mem_type: MemoryType):
    """Factory function that creates a cleanup function for a specific memory type."""
    ops = _FRAMEWORK_OPS[mem_type]
    
    if ops['cleanup_ops'] is None:
        # CPU type - no-op
        def cleanup(device_id=None):
            logger.debug(f"🔥 GPU CLEANUP: No-op for {mem_type.value} (CPU memory type)")
        return cleanup
    
    # Generate cleanup function from operation string
    cleanup_code = ops['cleanup_ops'].format(mod=ops['import_name'])
    
    def cleanup(device_id=None):
        framework = globals().get(ops['import_name'])
        if framework is None:
            logger.debug(f"{mem_type.value} not available, skipping cleanup")
            return
        
        try:
            # Execute cleanup operations
            exec(cleanup_code)
            logger.debug(f"🔥 GPU CLEANUP: Cleared {mem_type.value} GPU memory")
        except Exception as e:
            logger.warning(f"Failed to cleanup {mem_type.value} GPU memory: {e}")
    
    return cleanup

# Auto-generate cleanup registry
MEMORY_TYPE_CLEANUP_REGISTRY = {
    mem_type.value: _create_cleanup_function(mem_type)
    for mem_type in MemoryType
}
```

**Result**: 6 cleanup functions (250 lines) → ~50 lines (80% reduction)

#### 5. Auto-Generated Lazy Import Functions

```python
# Single factory function replaces 5 identical functions
def _create_lazy_getter(framework_name: str):
    """Factory function that creates a lazy import getter."""
    def getter():
        if framework_name not in _gpu_frameworks_cache:
            _gpu_frameworks_cache[framework_name] = optional_import(framework_name)
            if _gpu_frameworks_cache[framework_name] is not None:
                logger.debug(f"🔧 Lazy imported {framework_name} in thread {threading.current_thread().name}")
        return _gpu_frameworks_cache[framework_name]
    return getter

# Auto-generate all getters
for mem_type in MemoryType:
    ops = _FRAMEWORK_OPS[mem_type]
    if ops['lazy_getter'] is not None:
        getter_func = _create_lazy_getter(ops['import_name'])
        globals()[f"_get_{ops['import_name']}"] = getter_func
```

**Result**: 5 functions (50 lines) → ~15 lines (70% reduction)

---

## Implementation Plan

### Step 1: Create `framework_ops.py` with pure data definitions
**File**: `openhcs/core/memory/framework_ops.py` (new, ~150 lines)

Define `_FRAMEWORK_OPS` dict with all framework-specific operations as strings.

### Step 2: Consolidate scaling functions
**File**: `openhcs/core/memory/dtype_scaling.py` (new, ~100 lines)

Move and consolidate:
- `_scale_and_convert_numpy()` → `_scale_numpy()`
- `_scale_and_convert_cupy()` → `_scale_cupy()`  
- `_scale_and_convert_pyclesperanto()` → `_scale_pyclesperanto()`
- Add `_scale_torch()`, `_scale_tensorflow()`, `_scale_jax()` (currently missing, causing bugs)

### Step 3: Create shared slice processing function
**File**: `openhcs/core/memory/slice_processing.py` (new, ~60 lines)

Extract the 40 lines of identical slice-by-slice logic into a single shared function:
```python
def _process_slices(image, func, args, kwargs):
    """Shared slice-by-slice processing logic for all memory types."""
    # ... 40 lines of logic currently duplicated 6 times
```

### Step 4: Rewrite `decorators.py` with metaprogramming
**File**: `openhcs/core/memory/decorators.py` (1,940 lines → ~400 lines)

- Keep: `memory_types()` base decorator, `DtypeConversion` enum, materialization wrapping
- Replace: All 6 decorator functions with auto-generated versions
- Replace: All 6 dtype wrapper functions with single factory + auto-generation
- Replace: All 5 lazy getter functions with single factory + auto-generation
- Delete: All scaling functions (moved to dtype_scaling.py)

### Step 5: Rewrite `gpu_cleanup.py` with metaprogramming
**File**: `openhcs/core/memory/gpu_cleanup.py` (454 lines → ~150 lines)

- Replace: All 6 cleanup functions with auto-generated versions
- Keep: `cleanup_all_gpu_frameworks()`, `check_gpu_memory_usage()`, utility functions
- Auto-generate: `MEMORY_TYPE_CLEANUP_REGISTRY` from MemoryType enum

### Step 6: Update imports and exports
**File**: `openhcs/core/memory/__init__.py`

Add exports for new modules:
```python
from .framework_ops import _FRAMEWORK_OPS
from .dtype_scaling import _scale_numpy, _scale_cupy, _scale_pyclesperanto
```

### Step 7: Add MemoryType enum methods for cleanup
**File**: `openhcs/constants/constants.py`

Extend MemoryType enum with cleanup method:
```python
@property
def cleanup_func(self):
    """Get the cleanup function for this memory type."""
    from openhcs.core.memory.gpu_cleanup import MEMORY_TYPE_CLEANUP_REGISTRY
    return MEMORY_TYPE_CLEANUP_REGISTRY[self.value]
```

---

## Expected Results

### Line Count Reduction

| File | Before | After | Reduction |
|------|--------|-------|-----------|
| `decorators.py` | 1,940 | 400 | 79% |
| `gpu_cleanup.py` | 454 | 150 | 67% |
| **New files** | 0 | 310 | - |
| **Total** | **2,394** | **860** | **64%** |

**Note**: While total reduction is 64%, the actual code reduction is higher because new files contain pure data definitions (not logic duplication).

### Architecture Benefits

1. **Single Source of Truth**: Framework operations defined once in `_FRAMEWORK_OPS`
2. **Extensibility**: Adding a new memory type requires only adding one dict entry
3. **Consistency**: All decorators/wrappers/cleanup functions guaranteed identical structure
4. **Maintainability**: Bug fixes apply to all memory types automatically
5. **Testability**: Can test factory functions once instead of 6 separate implementations

### Validation Requirements

- All existing decorator functionality must work identically
- All dtype preservation behavior must be preserved
- All GPU cleanup operations must function correctly
- All tests must pass without modification
- No changes to public API (decorator names, signatures, behavior)

---

## Risk Assessment

**Low Risk**: This refactor follows the exact same pattern that successfully eliminated 93% of conversion code. The decorator/cleanup functions are even more repetitive than the conversion functions, making them ideal candidates for metaprogramming.

**Mitigation**: Implement incrementally, test each step, keep old code until new code is validated.

