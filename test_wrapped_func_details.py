"""Test to check wrapped function details."""
import sys
import inspect

# Import the function directly
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel

print("=== BEFORE REGISTRY ===")
print(f"Function: {count_cells_multi_channel}")
print(f"Signature: {inspect.signature(count_cells_multi_channel)}")

# Initialize registry
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
all_functions = RegistryService.get_all_functions_with_metadata()

# Find our function in registry
for key, metadata in all_functions.items():
    if 'count_cells_multi_channel' in key:
        print(f"\n=== REGISTRY METADATA ===")
        print(f"Key: {key}")
        print(f"metadata.func: {metadata.func}")
        print(f"Signature: {inspect.signature(metadata.func)}")
        print(f"Contract: {metadata.contract}")
        print(f"Has __wrapped__: {hasattr(metadata.func, '__wrapped__')}")
        if hasattr(metadata.func, '__wrapped__'):
            print(f"__wrapped__: {metadata.func.__wrapped__}")
            print(f"__wrapped__ signature: {inspect.signature(metadata.func.__wrapped__)}")
        break

# Check module
module = sys.modules['openhcs.processing.backends.analysis.cell_counting_cpu']
func_from_module = getattr(module, 'count_cells_multi_channel')

print(f"\n=== FROM MODULE ===")
print(f"Function: {func_from_module}")
print(f"Signature: {inspect.signature(func_from_module)}")
print(f"Same as original? {func_from_module is count_cells_multi_channel}")
