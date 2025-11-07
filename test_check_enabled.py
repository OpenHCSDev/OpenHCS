#!/usr/bin/env python3
"""Check if enabled parameter exists after importing."""

import sys
import inspect

# Force registry initialization
from openhcs.processing.func_registry import FunctionRegistry
registry = FunctionRegistry()

# Now import the function
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel

print("Function:", count_cells_multi_channel.__name__)
print("Module:", count_cells_multi_channel.__module__)

sig = inspect.signature(count_cells_multi_channel)
print("\nParameters:")
for name in sig.parameters:
    print(f"  - {name}")

if 'enabled' in sig.parameters:
    print("\n✓ 'enabled' parameter found!")
else:
    print("\n✗ 'enabled' parameter NOT found")

