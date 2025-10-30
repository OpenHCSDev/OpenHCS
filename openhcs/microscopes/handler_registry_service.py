"""
Microscope handler registry service.

Provides access to auto-discovered microscope handlers via LazyDiscoveryDict.
"""

import logging
from typing import List

from .microscope_base import MICROSCOPE_HANDLERS

logger = logging.getLogger(__name__)


def get_all_handler_types() -> List[str]:
    """Get list of all discovered handler types."""
    return list(MICROSCOPE_HANDLERS.keys())  # Auto-discovers on first access


def is_handler_available(handler_type: str) -> bool:
    """Check if a handler type is available."""
    return handler_type in MICROSCOPE_HANDLERS  # Auto-discovers on first access
