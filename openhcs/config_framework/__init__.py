"""
Compatibility shim for the config framework now provided by the `objectstate` package.

This keeps imports like `import openhcs.config_framework.parametric_axes` working
while the actual implementation lives in the external ObjectState dependency.
"""

from __future__ import annotations

import importlib
import pkgutil
import sys
from types import ModuleType
from typing import Dict, Any


def _import_objectstate() -> ModuleType:
    """Import objectstate and register it under the openhcs.config_framework namespace."""
    base_mod = importlib.import_module("objectstate")

    # Alias base module for backward compatibility
    sys.modules[__name__] = base_mod

    # Mirror submodules so openhcs.config_framework.* resolves
    if hasattr(base_mod, "__path__"):
        for submod_info in pkgutil.iter_modules(base_mod.__path__):
            full_name = f"objectstate.{submod_info.name}"
            alias_name = f"{__name__}.{submod_info.name}"
            try:
                submod = importlib.import_module(full_name)
                sys.modules[alias_name] = submod
            except ModuleNotFoundError:
                # If optional submodule is missing, skip registration
                continue

    return base_mod


_objectstate_module = _import_objectstate()

# Re-export attributes for star-import compatibility
_export_candidates: Dict[str, Any] = {
    k: v for k, v in vars(_objectstate_module).items() if not k.startswith("_")
}
globals().update(_export_candidates)
__all__ = list(_export_candidates.keys())
