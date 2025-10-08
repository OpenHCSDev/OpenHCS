"""
OMERO integration module for OpenHCS.

This module provides OMERO server integration including:
- Virtual backend for server-side execution
- OMERO microscope handler for native metadata
- Instance manager for automatic OMERO startup
- Docker Compose configuration for local testing

Core implementation files remain in their standard locations:
- Backend: openhcs.io.omero_local
- Microscope: openhcs.microscopes.omero
- Runtime: openhcs.runtime.omero_instance_manager

This module provides convenience imports and OMERO-specific infrastructure.
"""

# Re-export core OMERO classes for convenience
from openhcs.io.omero_local import OMEROLocalBackend, OMEROFileFormatRegistry
from openhcs.microscopes.omero import (
    OMEROMetadataHandler,
    OMEROFilenameParser,
    OMEROHandler
)
from openhcs.runtime.omero_instance_manager import (
    OMEROInstanceManager,
    DEFAULT_OMERO_HOST,
    DEFAULT_OMERO_PORT,
    DEFAULT_OMERO_WEB_PORT,
    DEFAULT_OMERO_USER,
    DEFAULT_OMERO_PASSWORD
)

__all__ = [
    # Backend
    'OMEROLocalBackend',
    'OMEROFileFormatRegistry',

    # Microscope
    'OMEROMetadataHandler',
    'OMEROFilenameParser',
    'OMEROHandler',

    # Instance Manager
    'OMEROInstanceManager',
    'DEFAULT_OMERO_HOST',
    'DEFAULT_OMERO_PORT',
    'DEFAULT_OMERO_WEB_PORT',
    'DEFAULT_OMERO_USER',
    'DEFAULT_OMERO_PASSWORD',
]

