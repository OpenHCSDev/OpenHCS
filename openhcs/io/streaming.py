"""
Streaming backend interfaces for OpenHCS.

This module provides abstract base classes for streaming data destinations
that send data to external systems without persistent storage capabilities.
"""

from abc import ABC
from openhcs.io.base import DataSink


class StreamingBackend(DataSink):
    """
    Abstract base class for streaming data destinations.

    Provides interface for backends that stream data to external systems
    (visualizers, networks, etc.) without persistent storage capabilities.

    Inherits only save operations from DataSink - no file system operations.
    Concrete implementations should use StorageBackendMeta for automatic registration.
    """
    
    # Only implements save() and save_batch() from DataSink
    # No additional abstract methods - streaming backends are minimal
    
    def cleanup(self) -> None:
        """
        Optional cleanup method for streaming backends.
        
        Override if backend needs resource cleanup (connections, shared memory, etc.).
        Default implementation is no-op.
        """
        pass
