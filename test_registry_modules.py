"""Test to check which modules are being scanned by OpenHCS registry."""
import logging
logging.basicConfig(level=logging.INFO)

from openhcs.processing.backends.lib_registry.openhcs_registry import OpenHCSRegistry

registry = OpenHCSRegistry()
modules = registry._get_openhcs_modules()

print(f"=== FOUND {len(modules)} MODULES ===")
for mod in sorted(modules):
    print(f"  - {mod}")

print(f"\n=== GETTING MODULES TO SCAN ===")
modules_to_scan = registry.get_modules_to_scan()
print(f"Found {len(modules_to_scan)} modules")
for mod_name, mod_obj in modules_to_scan:
    print(f"  - {mod_name}")

print(f"\n=== DISCOVERING FUNCTIONS ===")
try:
    functions = registry.discover_functions()
    print(f"Discovered {len(functions)} functions")
    for func_meta in functions[:5]:
        print(f"  - {func_meta.name}")
except Exception as e:
    print(f"ERROR: {e}")
    import traceback
    traceback.print_exc()
