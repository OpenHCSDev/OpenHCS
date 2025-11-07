"""Test to check metadata.func.__module__ and __name__."""
from openhcs.processing.backends.lib_registry.registry_service import RegistryService

all_functions = RegistryService.get_all_functions_with_metadata()

# Find count_cells_multi_channel
for key, metadata in all_functions.items():
    if 'count_cells_multi_channel' in key:
        print(f"Key: {key}")
        print(f"metadata.func: {metadata.func}")
        print(f"metadata.func.__name__: {metadata.func.__name__}")
        print(f"metadata.func.__module__: {metadata.func.__module__}")
        print(f"metadata.registry.library_name: {metadata.registry.library_name}")
        print(f"metadata.original_name: {metadata.original_name if hasattr(metadata, 'original_name') else 'N/A'}")

        if hasattr(metadata.func, '__wrapped__'):
            print(f"\n__wrapped__.__name__: {metadata.func.__wrapped__.__name__}")
            print(f"__wrapped__.__module__: {metadata.func.__wrapped__.__module__}")
        break
