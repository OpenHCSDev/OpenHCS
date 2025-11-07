# Code Editor Bug Investigation

## Problem Statement

When functions undergo a UI → Code → UI round trip through the code editor (in Pipeline Editor, Plate Manager, and Function List Editor), two specific issues occur:

1. The `enabled` parameter is completely lost/dropped during the loading process
2. The `slice_by_slice` parameter value is preserved, but its type hint is being lost

**Critical**: This bug ONLY affects OpenHCS registry functions. External libraries (pyclesperanto, skimage, cucim) work correctly.

## Root Cause Analysis

### Architecture Understanding

OpenHCS functions go through multiple decoration layers:

1. **Module-level decoration**: Functions are decorated with `@numpy_func` (or `@cupy_func`, etc.) which adds:
   - `input_memory_type` and `output_memory_type` attributes
   - `dtype_conversion` parameter (with type hint)
   - `slice_by_slice` parameter (with type hint)

2. **Registry-level wrapping**: During registry scanning (`OpenHCSRegistry.discover_functions()`):
   - Line 156: Sets `func.__processing_contract__ = contract` on the original function
   - Line 159: Calls `apply_contract_wrapper(func, contract)` which creates a wrapper that adds:
     - `enabled` parameter (for all contracts)
     - `slice_by_slice` parameter (for FLEXIBLE contracts, but it already exists from decorator)
   - Line 169: Stores the wrapped function in registry metadata
   - **BUG**: The wrapped function is NOT put back into the module!

3. **Code generation**: `pickle_to_python.py` generates import statements like:
   ```python
   from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel
   ```
   This imports from the module, which still has the unwrapped version (no `enabled` parameter).

### Why External Libraries Work

External libraries use virtual modules under the `openhcs.*` namespace (e.g., `openhcs.pyclesperanto`). These virtual modules are created in `func_registry.py` and populated with the wrapped versions from the registry. So when code imports from `openhcs.pyclesperanto`, it gets the wrapped version with all parameters.

## Testing Performed

### Test 1: Check metadata function
**File**: `test_metadata_module.py`
**Result**: 
- `metadata.func` has `enabled` and `slice_by_slice` ✓
- `metadata.func.__module__` is `openhcs.processing.backends.analysis.cell_counting_cpu` ✓
- `metadata.func` does NOT have `__processing_contract__` attribute ✗

### Test 2: Check if @wraps copies custom attributes
**File**: `test_wraps_attributes.py`
**Result**: `functools.wraps` DOES copy custom attributes ✓

### Test 3: Check wrapped function attributes
**File**: `test_wrapped_func_attributes.py`
**Result**: 
- Wrapped function does NOT have `__processing_contract__` ✗
- `__wrapped__` also does NOT have `__processing_contract__` ✗

### Test 4: Check original function in module
**File**: `test_check_original_func.py`
**Result**:
- Function in module does NOT have `__processing_contract__` ✗
- Function in module does NOT have `enabled` parameter ✗
- Function in module HAS `slice_by_slice` parameter (from decorator) ✓
- Function in module HAS `dtype_conversion` parameter (from decorator) ✓

### Test 5: Check import order and registry initialization
**File**: `test_import_order.py`
**Result**:
- Before registry init: function has NO `enabled` ✗
- After importing RegistryService: function has NO `enabled` ✗
- After calling `get_all_functions_with_metadata()`: function has NO `enabled` ✗

This confirms that even after registry initialization, the module still has the unwrapped version.

## Attempted Fixes

### Fix 1: Copy `__processing_contract__` attribute in wrapper
**File**: `openhcs/processing/backends/lib_registry/unified_registry.py`
**Change**: Added explicit copying of `__processing_contract__` attribute after creating wrapper (line 224-226)
**Result**: Did NOT fix the issue - attribute still not present on wrapped function

### Fix 2: Override function in module during registry scanning
**File**: `openhcs/processing/backends/lib_registry/openhcs_registry.py`
**Change**: Added `setattr(module, name, wrapped_func)` after wrapping (line 162)
**Result**: Did NOT fix the issue - module still has unwrapped version

### Fix 3: Update `_create_virtual_modules()` to override OpenHCS functions
**File**: `openhcs/processing/func_registry.py`
**Change**: Added logic to group OpenHCS functions by module and override them using `setattr()`
**Result**: NOT TESTED YET - debug logging shows `openhcs_functions_by_module` is empty

## Current Status

**FIXED**: The `enabled` parameter issue is now resolved!

### Root Cause
The modules were NOT in `sys.modules` when `_create_virtual_modules()` tried to override them. The registry was being loaded from cache, so `discover_functions()` wasn't being called, which meant the modules were never imported during that process.

### Solution
Modified `_create_virtual_modules()` in `openhcs/processing/func_registry.py` to import modules before overriding:
```python
# Import the module if it's not already in sys.modules
if real_module_path not in sys.modules:
    try:
        logger.debug(f"  Importing {real_module_path}...")
        importlib.import_module(real_module_path)
    except Exception as e:
        logger.warning(f"Could not import {real_module_path}: {e}")
        continue

module = sys.modules[real_module_path]
# Override each function with the registry-wrapped version
for func_name, wrapped_func in functions.items():
    setattr(module, func_name, wrapped_func)
```

After clearing the cache and re-initializing, the `enabled` parameter is now present in OpenHCS functions!

### Second Issue: `dtype_conversion` Type Hint Lost in UI

**Root Cause**: The `dtype_conversion` and `slice_by_slice` parameters are added by the `@numpy_func` decorator, which sets `__signature__` but NOT `__annotations__`. When `SignatureAnalyzer` calls `get_type_hints()`, it only reads from `__annotations__`, so these parameters are not found and fall back to `typing.Any`.

**Why this matters**: The UI uses `SignatureAnalyzer` to extract parameter types. When it gets `Any` instead of `Optional[DtypeConversion]`, the widget creation code doesn't recognize it as an enum and creates a string input instead of a dropdown.

**Solution**: Modified `SignatureAnalyzer._analyze_callable()` in `openhcs/introspection/signature_analyzer.py` to fall back to the signature annotation when a parameter is not in `type_hints`:

```python
# Try to get type from type_hints first, then fall back to signature annotation
# This is critical for parameters added by decorators (like dtype_conversion, slice_by_slice)
# which set __signature__ but not __annotations__
param_type = type_hints.get(param_name)
if param_type is None:
    # Fall back to signature annotation if available
    param_type = param.annotation if param.annotation != inspect.Parameter.empty else Any
```

**Result**: Now `SignatureAnalyzer` correctly returns `Optional[DtypeConversion]` for `dtype_conversion`, and the UI creates a dropdown widget instead of a string input.

## Summary

### Two Bugs Fixed

1. **`enabled` parameter lost during code editor round trip**
   - **Cause**: Registry wrapped functions but didn't override them in their modules
   - **Fix**: Import modules in `_create_virtual_modules()` before overriding functions with `setattr()`
   - **Files changed**: `openhcs/processing/func_registry.py`, `openhcs/processing/backends/lib_registry/openhcs_registry.py`

2. **`dtype_conversion` type hint treated as string instead of enum dropdown**
   - **Cause**: Decorators set `__signature__` but not `__annotations__`, so `get_type_hints()` didn't find the parameter
   - **Fix**: Fall back to signature annotation when parameter not in `type_hints`
   - **Files changed**: `openhcs/introspection/signature_analyzer.py`

### Key Insights

- **Module override timing**: Modules must be imported before `setattr()` can override their attributes
- **Type hint resolution**: `get_type_hints()` only reads `__annotations__`, not `__signature__`
- **Decorator parameter injection**: Parameters added via `__signature__` need special handling in introspection code

## Key Files

- `openhcs/processing/backends/lib_registry/openhcs_registry.py` - Registry scanning and wrapping
- `openhcs/processing/backends/lib_registry/unified_registry.py` - `apply_contract_wrapper()` method
- `openhcs/processing/func_registry.py` - Virtual module creation
- `openhcs/debug/pickle_to_python.py` - Code generation for UI → Code round trip
- `openhcs/core/memory/decorators.py` - Memory type decorators (`@numpy_func`, etc.)

## Questions to Answer

1. Why doesn't `functools.wraps` copy the `__processing_contract__` attribute even though it should?
2. Why doesn't `setattr(module, name, wrapped_func)` override the function in the module?
3. Should OpenHCS functions use virtual modules like external libraries, or should we fix the module override approach?
4. Is there a better place to do the module override (e.g., in `_create_virtual_modules()` instead of `discover_functions()`)?

