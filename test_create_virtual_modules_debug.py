"""Test _create_virtual_modules directly."""
import sys
import logging

# Enable DEBUG logging
logging.basicConfig(level=logging.DEBUG, format='%(name)s - %(message)s')

# Import function before registry
from openhcs.processing.backends.analysis.cell_counting_cpu import count_cells_multi_channel

print(f"=== BEFORE _create_virtual_modules ===")
print(f"count_cells_multi_channel has 'enabled': {'enabled' in count_cells_multi_channel.__code__.co_varnames}")

# Import func_registry which calls _create_virtual_modules
from openhcs.processing import func_registry

# Also manually call it to see logs
print(f"\n=== MANUALLY CALLING _create_virtual_modules ===")
func_registry._create_virtual_modules()

# Check module after
module = sys.modules['openhcs.processing.backends.analysis.cell_counting_cpu']
func_after = getattr(module, 'count_cells_multi_channel')

print(f"\n=== AFTER _create_virtual_modules ===")
print(f"count_cells_multi_channel has 'enabled': {'enabled' in func_after.__code__.co_varnames}")
print(f"Same object? {func_after is count_cells_multi_channel}")
