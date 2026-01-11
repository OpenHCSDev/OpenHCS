"""Function registry protocol for pluggable function lookup.

Allows applications to provide their own function registry implementation
without pyqt-formgen depending on specific function registry implementations.
"""

from typing import Protocol, Optional, Callable, Any, Dict


class FunctionRegistryProtocol(Protocol):
    """Protocol for function registries that provide function lookup and metadata.

    Applications can implement this protocol to provide their own function registry.

    Example:
        from pyqt_formgen.protocols import register_function_registry
        from myapp.registry import MyFunctionRegistry

        register_function_registry(MyFunctionRegistry())
    """

    def get_function_by_name(self, name: str) -> Optional[Callable]:
        """Get function by name.

        Args:
            name: Function name to lookup

        Returns:
            Function callable if found, None otherwise
        """
        ...

    def get_all_functions(self) -> Dict[str, Callable]:
        """Get all registered functions.

        Returns:
            Dictionary mapping function names to callables
        """
        ...

    def get_function_metadata(self, name: str) -> Optional[Dict[str, Any]]:
        """Get metadata for a function.

        Args:
            name: Function name

        Returns:
            Metadata dict if available, None otherwise
        """
        ...


# Global registry instance (set by application)
_function_registry: Optional[FunctionRegistryProtocol] = None


def register_function_registry(registry: FunctionRegistryProtocol) -> None:
    """Register a function registry implementation.

    Args:
        registry: Object implementing FunctionRegistryProtocol
    """
    global _function_registry
    _function_registry = registry


def get_function_registry() -> Optional[FunctionRegistryProtocol]:
    """Get the registered function registry.

    Returns:
        Registered registry or None if not registered
    """
    return _function_registry
