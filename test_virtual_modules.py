"""Test to check if virtual modules are overriding functions."""
import sys
import inspect
import logging

# Enable INFO logging to see what's happening
logging.basicConfig(level=logging.INFO, format='%(name)s - %(levelname)s - %(message)s')

# Import the function directly
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel

print("=== BEFORE IMPORTING func_registry ===")
print(f"Function ID: {id(count_cells_multi_channel)}")
print(f"Has 'enabled': {'enabled' in str(inspect.signature(count_cells_multi_channel))}")

# Now import func_registry which should call _create_virtual_modules()
print("\n=== IMPORTING func_registry ===")
from openhcs.processing import func_registry

# Check the module again
module = sys.modules['openhcs.processing.backends.analysis.cell_counting_cpu']
func_from_module = getattr(module, 'count_cells_multi_channel')

print(f"\n=== AFTER IMPORTING func_registry ===")
print(f"Function ID: {id(func_from_module)}")
print(f"Has 'enabled': {'enabled' in str(inspect.signature(func_from_module))}")
print(f"Same object as before? {func_from_module is count_cells_multi_channel}")
