#!/usr/bin/env python3
"""
Test that both bugs are fixed:
1. enabled parameter is preserved
2. dtype_conversion type hint is preserved as enum (not Any)
"""

import sys
import inspect

# Force registry initialization FIRST
from openhcs.processing.func_registry import initialize_registry
initialize_registry()

# Import SignatureAnalyzer
from openhcs.introspection.signature_analyzer import SignatureAnalyzer

# Import widget creation utilities
from openhcs.ui.shared.widget_creation_registry import resolve_optional, is_enum

# Import a function that has all three parameters
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel

print("=" * 80)
print("Testing Code Editor Bug Fixes")
print("=" * 80)

print(f"\nFunction: {count_cells_multi_channel.__name__}")
print(f"Module: {count_cells_multi_channel.__module__}")

# Get signature
sig = inspect.signature(count_cells_multi_channel)

# Test 1: Check if enabled parameter exists
print("\n" + "=" * 80)
print("Test 1: enabled parameter exists")
print("=" * 80)

if 'enabled' in sig.parameters:
    param = sig.parameters['enabled']
    print(f"✓ PASS: 'enabled' parameter found")
    print(f"  annotation: {param.annotation}")
    print(f"  default: {param.default}")
else:
    print(f"✗ FAIL: 'enabled' parameter NOT found")
    sys.exit(1)

# Test 2: Check if dtype_conversion has correct type hint
print("\n" + "=" * 80)
print("Test 2: dtype_conversion type hint is Optional[DtypeConversion]")
print("=" * 80)

param_info = SignatureAnalyzer.analyze(count_cells_multi_channel)

if 'dtype_conversion' in param_info:
    info = param_info['dtype_conversion']
    print(f"✓ Found 'dtype_conversion' parameter")
    print(f"  param_type: {info.param_type}")
    
    # Check if it's not Any
    from typing import Any
    if info.param_type == Any:
        print(f"✗ FAIL: param_type is Any (should be Optional[DtypeConversion])")
        sys.exit(1)
    
    # Check if it resolves to an enum
    resolved = resolve_optional(info.param_type)
    if is_enum(resolved):
        print(f"✓ PASS: Resolves to enum: {resolved}")
    else:
        print(f"✗ FAIL: Does not resolve to enum (resolved to {resolved})")
        sys.exit(1)
else:
    print(f"✗ FAIL: 'dtype_conversion' parameter NOT found")
    sys.exit(1)

# Test 3: Check if slice_by_slice has correct type hint
print("\n" + "=" * 80)
print("Test 3: slice_by_slice type hint is bool")
print("=" * 80)

if 'slice_by_slice' in param_info:
    info = param_info['slice_by_slice']
    print(f"✓ Found 'slice_by_slice' parameter")
    print(f"  param_type: {info.param_type}")
    
    if info.param_type == bool:
        print(f"✓ PASS: param_type is bool")
    else:
        print(f"✗ FAIL: param_type is {info.param_type} (should be bool)")
        sys.exit(1)
else:
    print(f"✗ FAIL: 'slice_by_slice' parameter NOT found")
    sys.exit(1)

print("\n" + "=" * 80)
print("ALL TESTS PASSED! ✓")
print("=" * 80)
print("\nBoth bugs are fixed:")
print("1. ✓ enabled parameter is preserved")
print("2. ✓ dtype_conversion type hint is preserved as Optional[DtypeConversion]")
print("3. ✓ slice_by_slice type hint is preserved as bool")

