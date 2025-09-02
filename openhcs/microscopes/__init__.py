"""
Microscope-specific implementations for openhcs.

This package contains modules for different microscope types, each providing
concrete implementations of FilenameParser and MetadataHandler interfaces.

The package uses automatic discovery to find and register all handler implementations,
following OpenHCS generic solution principles.
"""

# Import base components needed for registration
from openhcs.microscopes.microscope_base import MICROSCOPE_HANDLERS, METADATA_HANDLERS, create_microscope_handler

# Import registry service for automatic discovery
from openhcs.microscopes.handler_registry_service import (
    discover_all_handlers,
    get_all_handler_types,
    is_handler_available
)

# Discovery is now lazy - handlers are discovered when first needed

# Import handlers and components for backward compatibility
# These imports are now optional since discovery handles registration
try:
    from openhcs.microscopes.imagexpress import (
        ImageXpressHandler,
        ImageXpressFilenameParser,
        ImageXpressMetadataHandler
    )
except ImportError:
    ImageXpressHandler = None
    ImageXpressFilenameParser = None
    ImageXpressMetadataHandler = None

try:
    from openhcs.microscopes.opera_phenix import (
        OperaPhenixHandler,
        OperaPhenixFilenameParser,
        OperaPhenixMetadataHandler
    )
except ImportError:
    OperaPhenixHandler = None
    OperaPhenixFilenameParser = None
    OperaPhenixMetadataHandler = None

try:
    from openhcs.microscopes.openhcs import (
        OpenHCSMicroscopeHandler,
        OpenHCSMetadataHandler
    )
except ImportError:
    OpenHCSMicroscopeHandler = None
    OpenHCSMetadataHandler = None

# Note: Handlers are automatically registered via metaclass during discovery

__all__ = [
    # Factory function
    'create_microscope_handler',
    # Registry service
    'discover_all_handlers',
    'get_all_handler_types',
    'is_handler_available',
    # Handlers (may be None if not available)
    'ImageXpressHandler',
    'OperaPhenixHandler',
    'OpenHCSMicroscopeHandler',
    # Individual parsers and metadata handlers (may be None if not available)
    'ImageXpressFilenameParser',
    'ImageXpressMetadataHandler',
    'OperaPhenixFilenameParser',
    'OperaPhenixMetadataHandler',
    'OpenHCSMetadataHandler',
]
