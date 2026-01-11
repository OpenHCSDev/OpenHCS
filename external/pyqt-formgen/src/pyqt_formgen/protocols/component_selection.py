"""Component and function selection provider protocols."""

from typing import Protocol, Optional, Any, Iterable, List, Callable


class ComponentSelectionProvider(Protocol):
    """Protocol for component selection and display metadata."""

    def get_groupby_enum(self) -> Any:
        """Return the GroupBy enum (or compatible enum) used by the host app."""
        ...

    def get_component_keys(self, group_by: Any) -> List[str]:
        """Return available component keys for a given group_by."""
        ...

    def get_component_display_name(self, group_by: Any, component_key: str) -> Optional[str]:
        """Return a human-readable name for a component key."""
        ...

    def select_components(
        self,
        available_components: Iterable[str],
        selected_components: Iterable[str],
        group_by: Any,
        parent: Optional[Any] = None,
        **context: Any,
    ) -> Optional[List[str]]:
        """Show selection UI and return chosen components (or None if canceled)."""
        ...


class FunctionSelectionProvider(Protocol):
    """Protocol for selecting a function in UI."""

    def select_function(self, parent: Optional[Any] = None, **context: Any) -> Optional[Callable]:
        """Return a selected function or None."""
        ...


_component_selection_provider: Optional[ComponentSelectionProvider] = None
_function_selection_provider: Optional[FunctionSelectionProvider] = None


def register_component_selection_provider(provider: ComponentSelectionProvider) -> None:
    """Register a global component selection provider."""
    global _component_selection_provider
    _component_selection_provider = provider


def get_component_selection_provider() -> Optional[ComponentSelectionProvider]:
    """Get the registered component selection provider."""
    return _component_selection_provider


def register_function_selection_provider(provider: FunctionSelectionProvider) -> None:
    """Register a global function selection provider."""
    global _function_selection_provider
    _function_selection_provider = provider


def get_function_selection_provider() -> Optional[FunctionSelectionProvider]:
    """Get the registered function selection provider."""
    return _function_selection_provider

