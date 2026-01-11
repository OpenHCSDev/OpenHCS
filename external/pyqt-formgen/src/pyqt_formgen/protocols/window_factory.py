"""Window factory protocol for creating scope-aware windows."""

from typing import Protocol, Optional, Any

from PyQt6.QtWidgets import QWidget


class WindowFactoryProtocol(Protocol):
    """Protocol for creating windows for a given scope."""

    def create_window_for_scope(self, scope_id: str, object_state: Optional[Any] = None) -> Optional[QWidget]:
        """Create and show a window for the given scope id."""
        ...


_window_factory: Optional[WindowFactoryProtocol] = None


def register_window_factory(factory: WindowFactoryProtocol) -> None:
    """Register a global window factory."""
    global _window_factory
    _window_factory = factory


def get_window_factory() -> Optional[WindowFactoryProtocol]:
    """Get the registered window factory."""
    return _window_factory

