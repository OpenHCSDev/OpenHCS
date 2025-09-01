"""
Microscope handler automatic discovery service.

Eliminates hardcoded imports by using pkgutil.walk_packages to discover
all handler implementations following OpenHCS generic solution principles.
"""

import pkgutil
import importlib
import logging
from typing import List

from .microscope_base import MICROSCOPE_HANDLERS

logger = logging.getLogger(__name__)

_discovery_completed = False


def discover_all_handlers() -> None:
    """Discover all microscope handlers by importing all modules."""
    global _discovery_completed
    if _discovery_completed:
        return

    import openhcs.microscopes
    for importer, modname, ispkg in pkgutil.walk_packages(
        openhcs.microscopes.__path__,
        prefix="openhcs.microscopes."
    ):
        if ispkg or 'handler_registry_service' in modname:
            continue
        try:
            importlib.import_module(modname)
        except ImportError:
            continue

    _discovery_completed = True
    logger.debug(f"Discovered {len(MICROSCOPE_HANDLERS)} microscope handlers")


def get_all_handler_types() -> List[str]:
    """Get list of all discovered handler types."""
    discover_all_handlers()
    return list(MICROSCOPE_HANDLERS.keys())


def is_handler_available(handler_type: str) -> bool:
    """Check if a handler type is available."""
    discover_all_handlers()
    return handler_type in MICROSCOPE_HANDLERS
