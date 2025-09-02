"""
Microscope-specific implementations for openhcs.

This package contains modules for different microscope types, each providing
concrete implementations of FilenameParser and MetadataHandler interfaces.

The package uses automatic discovery to find and register all handler implementations,
following OpenHCS generic solution principles. All handlers are automatically
discovered and registered via metaclass during discovery - no hardcoded imports needed.
"""

# Import base components and factory function
from openhcs.microscopes.microscope_base import create_microscope_handler

# Import registry service for automatic discovery
from openhcs.microscopes.handler_registry_service import (
    discover_all_handlers,
    get_all_handler_types,
    is_handler_available
)

# Note: Individual handlers are automatically discovered and registered via metaclass.
# No hardcoded imports needed - the discovery system handles everything automatically.

__all__ = [
    # Factory function - primary public API
    'create_microscope_handler',
    # Registry service functions
    'discover_all_handlers',
    'get_all_handler_types',
    'is_handler_available',
]
