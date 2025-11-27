"""
React-quality UI framework for Python - Type-safe widget creation.

Uses ABC + dataclass with proper metaclass resolution.
All components MUST inherit from ParameterFormManager and implement the interface.

This is the Python equivalent of React's component interface:
- State management (parameters, nested_managers, widgets)
- Lifecycle hooks (_apply_initial_enabled_styling)
- Reactive updates (update_parameter, reset_parameter) - routed through FieldChangeDispatcher
- Component tree traversal (_apply_to_nested_managers)
"""

from abc import ABC, abstractmethod, ABCMeta
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


# Create a combined metaclass that works with both PyQt and ABC
# This must be done BEFORE defining the ABC class
from PyQt6.QtWidgets import QWidget

class _CombinedMeta(ABCMeta, type(QWidget)):
    """Combined metaclass for ABC + PyQt6 QWidget."""
    pass


class ParameterFormManager(ABC, metaclass=_CombinedMeta):
    """
    React-quality reactive form manager interface.

    All components MUST inherit from this ABC and implement all abstract methods.
    Uses dataclass for clean state declaration.

    Semantics (React equivalents):
    - State: parameters, nested_managers, widgets (like React state)
    - Lifecycle: _apply_initial_enabled_styling (like useEffect)
    - Reactive updates: update_parameter/reset_parameter routed through FieldChangeDispatcher
    - Component tree: _apply_to_nested_managers (like recursive component traversal)
    """

    # ==================== STATE ====================
    # These are like React component state
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

    # ==================== LIFECYCLE HOOKS ====================
    # These are like React useEffect hooks
    # DELETED: _emit_parameter_change - replaced by FieldChangeDispatcher

    # ==================== STATE MUTATIONS ====================
    # These are like React state setters

    @abstractmethod
    def update_parameter(self, param_name: str, value: Any) -> None:
        """
        Update parameter in data model.

        Equivalent to: setState(name, value)
        """
        pass

    @abstractmethod
    def reset_parameter(self, param_name: str) -> None:
        """
        Reset parameter to default value.

        Equivalent to: setState(name, defaultValue)
        """
        pass

    # ==================== WIDGET CREATION ====================
    # These are like React component rendering

    @abstractmethod
    def create_widget(self, param_name: str, param_type: Type, current_value: Any,
                     widget_id: str, parameter_info: Optional[Any] = None) -> Any:
        """
        Create a widget for a parameter.

        Equivalent to: render(<ParameterWidget ... />)
        """
        pass

    @abstractmethod
    def _create_nested_form_inline(self, param_name: str, unwrapped_type: Type,
                                   current_value: Any) -> Any:
        """
        Create nested form manager inline.

        Equivalent to: render(<NestedForm ... />)
        """
        pass

    @abstractmethod
    def _make_widget_readonly(self, widget: Any) -> None:
        """
        Make a widget read-only.

        Equivalent to: <input disabled={true} />
        """
        pass

    # ==================== COMPONENT TREE TRAVERSAL ====================
    # These are like React's recursive component tree operations

    @abstractmethod
    def _apply_to_nested_managers(self, callback: Callable[[str, Any], None]) -> None:
        """
        Apply operation to all nested managers recursively.

        Equivalent to: traverseComponentTree(callback)
        """
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

