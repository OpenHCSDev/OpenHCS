#!/usr/bin/env python3
"""Simple test to check if enabled parameter exists."""

import sys
import inspect

# Force registry initialization
from openhcs.processing.func_registry import initialize_registry
initialize_registry()

# Import the function - this should trigger registry initialization
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel

print("Function:", count_cells_multi_channel.__name__)

sig = inspect.signature(count_cells_multi_channel)

if 'enabled' in sig.parameters:
    print("✓ 'enabled' parameter found!")
    param = sig.parameters['enabled']
    print(f"  annotation: {param.annotation}")
    print(f"  default: {param.default}")
else:
    print("✗ 'enabled' parameter NOT found")
    print("\nAll parameters:")
    for name in sig.parameters:
        print(f"  - {name}")

