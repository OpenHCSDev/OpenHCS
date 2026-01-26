"""
Compatibility shim for the config framework now provided by the `objectstate` package.

This keeps imports like `import openhcs.config_framework.parametric_axes` working
while the actual implementation lives in the external ObjectState dependency.
"""

from __future__ import annotations

import importlib
import pkgutil
import logging
from pathlib import Path
import sys
from types import ModuleType
from typing import Dict, Any


logger = logging.getLogger(__name__)


def _import_objectstate() -> ModuleType:
    """Import objectstate and register it under the openhcs.config_framework namespace."""
    # Prefer the vendored ObjectState source tree (repo checkout) over any installed
    # site-packages version.
    #
    # This project vendors ObjectState under `external/ObjectState/src`. If we don't
    # put that on sys.path first, Python will import the globally installed
    # `objectstate` package (e.g., from site-packages), and fixes made to the vendored
    # code won't be used by the running app.
    repo_root = Path(__file__).resolve().parents[2]
    vendored_src = repo_root / "external" / "ObjectState" / "src"
    if vendored_src.exists():
        vendored_str = str(vendored_src)
        if vendored_str not in sys.path:
            sys.path.insert(0, vendored_str)

    base_mod = importlib.import_module("objectstate")

    # Diagnostic: record which ObjectState implementation is actually in use.
    # This is critical when debugging behavior differences between vendored vs
    # site-packages installs.
    try:
        logger.info(f"[ObjectState] Using objectstate from: {getattr(base_mod, '__file__', '<unknown>')}")
    except Exception:
        pass

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
