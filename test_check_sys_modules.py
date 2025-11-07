"""Check if modules are in sys.modules."""
import sys

# Import func_registry to trigger override
print("=== Before importing func_registry ===")
print(f"cell_counting_cpu in sys.modules: {'openhcs.processing.backends.analysis.cell_counting_cpu' in sys.modules}")

from openhcs.processing import func_registry

print(f"\n=== After importing func_registry ===")
print(f"cell_counting_cpu in sys.modules: {'openhcs.processing.backends.analysis.cell_counting_cpu' in sys.modules}")

# Now import the module
from openhcs.processing.backends.analysis import cell_counting_cpu

print(f"\n=== After importing cell_counting_cpu ===")
print(f"cell_counting_cpu in sys.modules: {'openhcs.processing.backends.analysis.cell_counting_cpu' in sys.modules}")

import inspect
sig = inspect.signature(cell_counting_cpu.count_cells_multi_channel)
print(f"Has 'enabled': {'enabled' in str(sig)}")
