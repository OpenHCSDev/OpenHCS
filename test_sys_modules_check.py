"""Test to check sys.modules state after registry initialization."""
import sys
import logging

# Enable debug logging
logging.basicConfig(level=logging.DEBUG)

# Import the function directly from the module
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel

print("=== BEFORE REGISTRY INIT ===")
print(f"Function from direct import: {count_cells_multi_channel}")
print(f"Has 'enabled' parameter: {'enabled' in count_cells_multi_channel.__code__.co_varnames}")
print(f"Has 'slice_by_slice' parameter: {'slice_by_slice' in count_cells_multi_channel.__code__.co_varnames}")
print(f"Parameters: {count_cells_multi_channel.__code__.co_varnames[:count_cells_multi_channel.__code__.co_argcount]}")

# Now initialize the registry
from openhcs.processing.backends.lib_registry.registry_service import RegistryService
all_functions = RegistryService.get_all_functions_with_metadata()

print("\n=== AFTER REGISTRY INIT (RegistryService.get_all_functions_with_metadata()) ===")
print(f"Function from direct import: {count_cells_multi_channel}")
print(f"Has 'enabled' parameter: {'enabled' in count_cells_multi_channel.__code__.co_varnames}")
print(f"Has 'slice_by_slice' parameter: {'slice_by_slice' in count_cells_multi_channel.__code__.co_varnames}")
print(f"Parameters: {count_cells_multi_channel.__code__.co_varnames[:count_cells_multi_channel.__code__.co_argcount]}")

# Check the function in sys.modules
module = sys.modules['openhcs.processing.backends.analysis.cell_counting_cpu']
func_from_module = getattr(module, 'count_cells_multi_channel')

print("\n=== FUNCTION FROM sys.modules ===")
print(f"Function from sys.modules: {func_from_module}")
print(f"Has 'enabled' parameter: {'enabled' in func_from_module.__code__.co_varnames}")
print(f"Has 'slice_by_slice' parameter: {'slice_by_slice' in func_from_module.__code__.co_varnames}")
print(f"Parameters: {func_from_module.__code__.co_varnames[:func_from_module.__code__.co_argcount]}")

# Check if they're the same object
print(f"\nAre they the same object? {count_cells_multi_channel is func_from_module}")

# Now trigger virtual module creation by importing func_registry
print("\n=== AFTER IMPORTING func_registry ===")
from openhcs.processing import func_registry

# Re-check
func_from_module_after = getattr(module, 'count_cells_multi_channel')
print(f"Function from sys.modules: {func_from_module_after}")
print(f"Has 'enabled' parameter: {'enabled' in func_from_module_after.__code__.co_varnames}")
print(f"Has 'slice_by_slice' parameter: {'slice_by_slice' in func_from_module_after.__code__.co_varnames}")
print(f"Parameters: {func_from_module_after.__code__.co_varnames[:func_from_module_after.__code__.co_argcount]}")

# Check metadata function
composite_key = None
for key, metadata in all_functions.items():
    if 'count_cells_multi_channel' in key:
        composite_key = key
        print(f"\n=== FUNCTION FROM REGISTRY METADATA ===")
        print(f"Composite key: {key}")
        print(f"Function: {metadata.func}")
        print(f"Has 'enabled' parameter: {'enabled' in metadata.func.__code__.co_varnames}")
        print(f"Has 'slice_by_slice' parameter: {'slice_by_slice' in metadata.func.__code__.co_varnames}")
        print(f"Parameters: {metadata.func.__code__.co_varnames[:metadata.func.__code__.co_argcount]}")
        print(f"Registry library_name: {metadata.registry.library_name}")
        break
