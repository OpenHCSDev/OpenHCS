"""Test to check sys.modules state after registry initialization."""
import sys

# Import the function directly from the module
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel

print("=== BEFORE REGISTRY INIT ===")
print(f"Has 'enabled': {'enabled' in count_cells_multi_channel.__code__.co_varnames}")
print(f"Has 'slice_by_slice': {'slice_by_slice' in count_cells_multi_channel.__code__.co_varnames}")

# Now initialize the registry
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
all_functions = RegistryService.get_all_functions_with_metadata()

print(f"\n=== REGISTRY HAS {len(all_functions)} FUNCTIONS ===")

# Find our function
found = False
for key, metadata in all_functions.items():
    if 'count_cells_multi_channel' in key:
        found = True
        print(f"\n=== FUNCTION FROM REGISTRY ===")
        print(f"Key: {key}")
        print(f"Has 'enabled': {'enabled' in metadata.func.__code__.co_varnames}")
        print(f"Has 'slice_by_slice': {'slice_by_slice' in metadata.func.__code__.co_varnames}")
        print(f"Params: {metadata.func.__code__.co_varnames[:metadata.func.__code__.co_argcount]}")
        print(f"Registry: {metadata.registry.library_name}")
        break

if not found:
    print("\n❌ count_cells_multi_channel NOT FOUND in registry!")
    print("Available keys:")
    for key in sorted(all_functions.keys()):
        if 'cell' in key.lower():
            print(f"  - {key}")

# Now trigger virtual module creation
print("\n=== IMPORTING func_registry ===")
from openhcs.processing import func_registry

# Re-check
module = sys.modules['openhcs.processing.backends.analysis.cell_counting_cpu']
func_from_module = getattr(module, 'count_cells_multi_channel')

print(f"\n=== AFTER func_registry IMPORT ===")
print(f"Function from module: {func_from_module}")
print(f"Has 'enabled': {'enabled' in func_from_module.__code__.co_varnames}")
print(f"Has 'slice_by_slice': {'slice_by_slice' in func_from_module.__code__.co_varnames}")
print(f"Params: {func_from_module.__code__.co_varnames[:func_from_module.__code__.co_argcount]}")
