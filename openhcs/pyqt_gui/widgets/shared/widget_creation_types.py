"""
Type-safe definitions for widget creation configuration.

Uses ABCs to enforce explicit contracts and enable static type checking.
"""

from abc import ABC, abstractmethod
from typing import TypedDict, Callable, Optional, Any, Dict, Type
from dataclasses import dataclass

# Import ParameterInfo ABC from shared UI module
from openhcs.ui.shared.parameter_info_types import ParameterInfoBase as ParameterInfo


class DisplayInfo(TypedDict, total=False):
    """Type-safe display information for a parameter."""
    field_label: str
    checkbox_label: str
    description: str


class FieldIds(TypedDict, total=False):
    """Type-safe field ID mapping."""
    widget_id: str
    optional_checkbox_id: str


class ParameterFormManager(ABC):
    """ABC for ParameterFormManager - enforces explicit interface."""

    # Properties that implementations must provide
    read_only: bool
    parameters: Dict[str, Any]
    nested_managers: Dict[str, Any]
    widgets: Dict[str, Any]
    reset_buttons: Dict[str, Any]
    color_scheme: Any
    config: Any
    service: Any
    _widget_ops: Any
    _on_build_complete_callbacks: list

    @abstractmethod
    def create_widget(self, param_name: str, param_type: Type, current_value: Any,
                     widget_id: str, parameter_info: Optional[Any] = None) -> Any:
        """Create a widget for a parameter."""
        pass

    @abstractmethod
    def update_parameter(self, param_name: str, value: Any) -> None:
        """Update a parameter value."""
        pass

    @abstractmethod
    def reset_parameter(self, param_name: str) -> None:
        """Reset a parameter to default."""
        pass

    @abstractmethod
    def _create_nested_form_inline(self, param_name: str, unwrapped_type: Type,
                                   current_value: Any) -> Any:
        """Create a nested form manager inline."""
        pass

    @abstractmethod
    def _make_widget_readonly(self, widget: Any) -> None:
        """Make a widget read-only."""
        pass

    @abstractmethod
    def _emit_parameter_change(self, param_name: str, value: Any) -> None:
        """Emit parameter change signal."""
        pass

    @abstractmethod
    def _apply_initial_enabled_styling(self) -> None:
        """Apply initial enabled styling."""
        pass

    @abstractmethod
    def _apply_to_nested_managers(self, callback: Callable[[str, Any], None]) -> None:
        """Apply callback to all nested managers."""
        pass


# Type aliases for handler signatures
WidgetOperationHandler = Callable[
    ['ParameterFormManager', 'ParameterInfo', DisplayInfo, FieldIds,
     Any, Optional[Type], Optional[Any], Optional[Any], Optional[Type],
     Optional[Type], Optional[Type]],
    Any
]

OptionalTitleHandler = Callable[
    ['ParameterFormManager', 'ParameterInfo', DisplayInfo, FieldIds,
     Any, Optional[Type]],
    Dict[str, Any]
]

CheckboxLogicHandler = Callable[
    ['ParameterFormManager', 'ParameterInfo', Any, Any, Any, Any, Any, Type],
    None
]


@dataclass
class WidgetCreationConfig:
    """Type-safe configuration for a widget creation type."""
    layout_type: str
    is_nested: bool
    create_container: WidgetOperationHandler
    setup_layout: Optional[WidgetOperationHandler]
    create_main_widget: WidgetOperationHandler
    needs_label: bool
    needs_reset_button: bool
    needs_unwrap_type: bool
    is_optional: bool = False
    needs_checkbox: bool = False
    create_title_widget: Optional[OptionalTitleHandler] = None
    connect_checkbox_logic: Optional[CheckboxLogicHandler] = None

