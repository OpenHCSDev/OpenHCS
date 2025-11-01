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
    get_all_handler_types,
    is_handler_available
)

# Note: Individual handlers are automatically discovered via LazyDiscoveryDict on first access.
# No hardcoded imports or explicit discovery calls needed.

__all__ = [
    # Factory function - primary public API
    'create_microscope_handler',
    # Registry service functions
    'get_all_handler_types',
    'is_handler_available',
]
