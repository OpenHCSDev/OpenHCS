"""
Type-safe definitions for widget creation configuration.

Replaces untyped dicts with TypedDict and Protocol classes to enable
static type checking and catch errors at development time.
"""

from typing import TypedDict, Protocol, Callable, Optional, Any, Dict, Type
from dataclasses import dataclass


class DisplayInfo(TypedDict, total=False):
    """Type-safe display information for a parameter."""
    field_label: str
    checkbox_label: str
    description: str


class FieldIds(TypedDict, total=False):
    """Type-safe field ID mapping."""
    widget_id: str
    optional_checkbox_id: str


class ParameterInfoProtocol(Protocol):
    """Protocol for parameter information objects."""
    name: str
    type: Type
    current_value: Any
    description: Optional[str]


class ParameterFormManagerProtocol(Protocol):
    """Protocol for ParameterFormManager to enable type checking."""
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
    
    def create_widget(self, param_name: str, param_type: Type, current_value: Any, 
                     widget_id: str, parameter_info: Optional[Any] = None) -> Any:
        """Create a widget for a parameter."""
        ...
    
    def update_parameter(self, param_name: str, value: Any) -> None:
        """Update a parameter value."""
        ...
    
    def reset_parameter(self, param_name: str) -> None:
        """Reset a parameter to default."""
        ...
    
    def _create_nested_form_inline(self, param_name: str, unwrapped_type: Type, 
                                   current_value: Any) -> Any:
        """Create a nested form manager inline."""
        ...
    
    def _make_widget_readonly(self, widget: Any) -> None:
        """Make a widget read-only."""
        ...
    
    def _emit_parameter_change(self, param_name: str, value: Any) -> None:
        """Emit parameter change signal."""
        ...
    
    def _apply_initial_enabled_styling(self) -> None:
        """Apply initial enabled styling."""
        ...
    
    def _apply_to_nested_managers(self, callback: Callable[[str, Any], None]) -> None:
        """Apply callback to all nested managers."""
        ...


# Type aliases for handler signatures
WidgetOperationHandler = Callable[
    ['ParameterFormManagerProtocol', 'ParameterInfoProtocol', DisplayInfo, FieldIds, 
     Any, Optional[Type], Optional[Any], Optional[Any], Optional[Type], 
     Optional[Type], Optional[Type]], 
    Any
]

OptionalTitleHandler = Callable[
    ['ParameterFormManagerProtocol', 'ParameterInfoProtocol', DisplayInfo, FieldIds, 
     Any, Optional[Type]], 
    Dict[str, Any]
]

CheckboxLogicHandler = Callable[
    ['ParameterFormManagerProtocol', 'ParameterInfoProtocol', Any, Any, Any, Any, Any, Type], 
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

