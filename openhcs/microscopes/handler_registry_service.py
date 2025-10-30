"""
Microscope handler automatic discovery service.

Eliminates hardcoded imports by using generic discovery to trigger
metaclass registration of all handler implementations.
"""

import logging
from typing import List

from openhcs.core.registry_discovery import discover_registry_classes_recursive
from .microscope_base import MICROSCOPE_HANDLERS, MicroscopeHandler

logger = logging.getLogger(__name__)

_discovery_completed = False


def discover_all_handlers() -> None:
    """
    Discover all microscope handlers by importing all modules.

    Uses generic discovery to find and import all MicroscopeHandler subclasses,
    which triggers their metaclass registration into MICROSCOPE_HANDLERS.

    The metaclass handles everything - modules without MicroscopeHandler subclasses
    or without _microscope_type simply don't register. No excludes needed.
    """
    global _discovery_completed
    if _discovery_completed:
        return

    import openhcs.microscopes

    # Use generic discovery to import all modules
    # The metaclass decides what registers based on skip_if_no_key
    _ = discover_registry_classes_recursive(
        package_path=openhcs.microscopes.__path__,
        package_prefix="openhcs.microscopes.",
        base_class=MicroscopeHandler
        # No exclude_modules - let the metaclass handle it!
    )

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
