"""
Legacy compatibility shim: openhcs.io -> polystore.

Historically, OpenHCS exposed storage backends and FileManager under openhcs.io.
The implementation was extracted to the polystore package. This module keeps
old imports working (e.g., `from openhcs.io.filemanager import FileManager`)
by re-exporting polystore and aliasing its submodules.
"""

from __future__ import annotations

import importlib
import sys
from typing import Dict

try:
    import polystore as _polystore
except Exception as exc:  # pragma: no cover - only when dependency missing
    raise ImportError(
        "openhcs.io requires the 'polystore' package. Install openhcs with its "
        "dependencies or add polystore to your environment."
    ) from exc

# Re-export public API from polystore at the openhcs.io package level
__all__ = list(getattr(_polystore, "__all__", []))
globals().update({name: getattr(_polystore, name) for name in __all__})

# Alias common polystore submodules so openhcs.io.<module> imports keep working
_SUBMODULES = [
    "atomic",
    "backend_registry",
    "base",
    "config",
    "constants",
    "disk",
    "exceptions",
    "filemanager",
    "formats",
    "memory",
    "metadata_migration",
    "metadata_writer",
    "napari_stream",
    "fiji_stream",
    "omero_local",
    "roi",
    "roi_converters",
    "streaming",
    "streaming_constants",
    "utils",
    "virtual_workspace",
    "zarr",
    "zmq_config",
]

_aliased: Dict[str, object] = {}
for _name in _SUBMODULES:
    try:
        _module = importlib.import_module(f"polystore.{_name}")
    except Exception:
        # Ignore optional submodules that may not import in minimal installs
        continue
    sys.modules[f"{__name__}.{_name}"] = _module
    _aliased[_name] = _module
    globals()[_name] = _module

