"""Test sys.modules directly."""
import sys
import inspect

# Import func_registry to trigger override
from openhcs.processing import func_registry

# Get function directly from sys.modules (not using import)
module = sys.modules['openhcs.processing.backends.analysis.cell_counting_cpu']
func = getattr(module, 'count_cells_multi_channel')

print(f"Function from sys.modules: {func}")
sig = inspect.signature(func)
print(f"Has 'enabled': {'enabled' in str(sig)}")

print(f"\nSignature parameters:")
for param_name, param in sig.parameters.items():
    if param_name in ['enabled', 'slice_by_slice', 'dtype_conversion']:
        print(f"  {param_name}: {param}")
