"""
Abstract base classes for storage backends.

This module defines abstract interfaces for storage backends to support
features like pickling and multiprocessing with explicit contracts.
"""

from abc import ABC, abstractmethod
from typing import Optional, Dict, Any


class PicklableBackend(ABC):
    """
    Abstract base class for storage backends that support pickling with connection parameters.

    Backends must explicitly inherit from this ABC and implement the required methods
    to be safely pickled and unpickled in multiprocessing workers.

    This is particularly important for backends that maintain network connections
    (e.g., OMERO, remote databases) which cannot be pickled directly.
    """

    @abstractmethod
    def get_connection_params(self) -> Optional[Dict[str, Any]]:
        """
        Return connection parameters for worker process reconnection.

        Returns:
            Dictionary of connection parameters (host, port, username, etc.)
            or None if no connection parameters are available.

        Note:
            Passwords should NOT be included in connection params.
            They should be retrieved from environment variables in the worker.
        """
        pass

    @abstractmethod
    def set_connection_params(self, params: Optional[Dict[str, Any]]) -> None:
        """
        Set connection parameters (used during unpickling).

        Args:
            params: Dictionary of connection parameters or None
        """
        pass

