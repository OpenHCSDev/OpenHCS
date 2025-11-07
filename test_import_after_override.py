"""Test importing after override."""
import sys

# First, trigger the override by importing func_registry
print("=== Importing func_registry to trigger override ===")
from openhcs.processing import func_registry

# NOW import the function
print("\n=== Importing function AFTER override ===")
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel
import inspect

print(f"Function: {count_cells_multi_channel}")
sig = inspect.signature(count_cells_multi_channel)
print(f"Has 'enabled': {'enabled' in str(sig)}")
print(f"\nSignature parameters:")
for param_name, param in sig.parameters.items():
    if param_name in ['enabled', 'slice_by_slice', 'dtype_conversion']:
        print(f"  {param_name}: {param}")
