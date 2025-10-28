"""
Widget creation configuration - parametric pattern.

Single source of truth for widget creation behavior (REGULAR and NESTED only).
Mirrors openhcs/core/memory/framework_config.py pattern.

Architecture:
- Widget handlers: Custom logic for complex operations
- Unified config: Single _WIDGET_CREATION_CONFIG dict with all metadata
- Parametric dispatch: Handlers can be callables or eval expressions

NOTE: OPTIONAL_NESTED widgets are too complex for parametrization (180+ lines with
      custom checkbox logic, title widgets, styling callbacks). They remain as a
      dedicated method. This config handles the simpler REGULAR and NESTED types.
"""

from enum import Enum
from typing import Any, Callable, Optional, Type, Tuple
import logging

logger = logging.getLogger(__name__)


class WidgetCreationType(Enum):
    """
    Enum for widget creation strategies - mirrors MemoryType pattern.

    PyQt6 uses 2 parametric types (REGULAR, NESTED) + 1 custom handler (OPTIONAL_NESTED).
    """
    REGULAR = "regular"
    NESTED = "nested"


# ============================================================================
# WIDGET CREATION HANDLERS - Special-case logic (like framework handlers)
# ============================================================================

def _unwrap_optional_type(param_type: Type) -> Type:
    """Unwrap Optional[T] to get T."""
    from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
    return (
        ParameterTypeUtils.get_optional_inner_type(param_type)
        if ParameterTypeUtils.is_optional_dataclass(param_type)
        else param_type
    )


def _create_optimized_reset_button(field_id: str, param_name: str, reset_callback):
    """
    Optimized reset button factory - reuses configuration to save ~0.15ms per button.

    This factory creates reset buttons with consistent styling and configuration,
    avoiding repeated property setting overhead.
    """
    from PyQt6.QtWidgets import QPushButton

    button = QPushButton("Reset")
    button.setObjectName(f"{field_id}_reset")
    button.setMaximumWidth(60)  # Standard reset button width
    button.clicked.connect(reset_callback)
    return button


def _create_nested_form(manager, param_info, display_info, field_ids, current_value, unwrapped_type) -> Any:
    """
    Handler for creating nested form.

    NOTE: This creates the nested manager AND stores it in manager.nested_managers.
    The caller should NOT try to store it again.
    """
    nested_manager = manager._create_nested_form_inline(
        param_info.name, unwrapped_type, current_value
    )
    # Store nested manager BEFORE building form (needed for reset button connection)
    manager.nested_managers[param_info.name] = nested_manager
    return nested_manager.build_form()


# ============================================================================
# UNIFIED WIDGET CREATION CONFIGURATION (like _FRAMEWORK_CONFIG)
# ============================================================================

_WIDGET_CREATION_CONFIG = {
    WidgetCreationType.REGULAR: {
        # Metadata
        'layout_type': 'QHBoxLayout',
        'is_nested': False,

        # Widget creation operations (eval expressions or callables)
        'create_container': 'QWidget()',
        'setup_layout': 'layout.setSpacing(CURRENT_LAYOUT.parameter_row_spacing); layout.setContentsMargins(*CURRENT_LAYOUT.parameter_row_margins)',
        'create_main_widget': 'manager.create_widget(param_info.name, param_info.type, current_value, field_ids["widget_id"])',

        # Feature flags
        'needs_label': True,
        'needs_reset_button': True,
        'needs_unwrap_type': False,
    },

    WidgetCreationType.NESTED: {
        # Metadata
        'layout_type': 'GroupBoxWithHelp',
        'is_nested': True,

        # Widget creation operations
        'create_container': 'GroupBoxWithHelp(title=display_info["field_label"], help_target=unwrapped_type, color_scheme=manager.config.color_scheme or PyQt6ColorScheme())',
        'setup_layout': None,  # GroupBox handles its own layout
        'create_main_widget': _create_nested_form,  # Callable handler

        # Feature flags
        'needs_label': False,
        'needs_reset_button': True,  # "Reset All" button in GroupBox title
        'needs_unwrap_type': True,
    },
}


# ============================================================================
# AUTO-GENERATE WIDGET OPERATIONS FROM CONFIG
# ============================================================================

def _make_widget_operation(expr_str: str, creation_type: WidgetCreationType):
    """
    Create operation from expression string (like _make_lambda_with_name).

    Converts eval expressions to lambdas with proper context.
    """
    if expr_str is None:
        return None

    # Create lambda with proper context
    # Context: manager, param_info, display_info, field_ids, current_value, unwrapped_type, layout, CURRENT_LAYOUT, QWidget, GroupBoxWithHelp, PyQt6ColorScheme
    lambda_expr = f'lambda manager, param_info, display_info, field_ids, current_value, unwrapped_type, layout, CURRENT_LAYOUT, QWidget, GroupBoxWithHelp, PyQt6ColorScheme: {expr_str}'
    operation = eval(lambda_expr)
    operation.__name__ = f'{creation_type.value}_operation'
    operation.__qualname__ = f'WidgetCreation.{creation_type.value}_operation'
    return operation


_WIDGET_OPERATIONS = {
    creation_type: {
        op_name: (
            _make_widget_operation(expr, creation_type)
            if isinstance(expr, str)
            else expr  # Already a callable
        )
        for op_name, expr in config.items()
        if op_name in ['create_container', 'setup_layout', 'create_main_widget']
    }
    for creation_type, config in _WIDGET_CREATION_CONFIG.items()
}


# ============================================================================
# UNIFIED WIDGET CREATION FUNCTION
# ============================================================================

def create_widget_parametric(manager, param_info, creation_type: WidgetCreationType):
    """
    UNIFIED: Create widget using parametric dispatch.

    Replaces _create_regular_parameter_widget and _create_nested_dataclass_widget.
    Does NOT handle OPTIONAL_NESTED (too complex - remains as dedicated method).

    Args:
        manager: ParameterFormManager instance
        param_info: Parameter information object
        creation_type: Widget creation type (REGULAR or NESTED)

    Returns:
        QWidget: Created widget container
    """
    from PyQt6.QtWidgets import QWidget, QHBoxLayout, QVBoxLayout, QPushButton
    from openhcs.pyqt_gui.widgets.shared.clickable_help_components import GroupBoxWithHelp, LabelWithHelp
    from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
    from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
    from openhcs.pyqt_gui.widgets.shared.layout_constants import CURRENT_LAYOUT
    import logging

    logger = logging.getLogger(__name__)

    # Get config and operations for this type
    config = _WIDGET_CREATION_CONFIG[creation_type]
    ops = _WIDGET_OPERATIONS[creation_type]

    # Prepare context
    display_info = manager.service.get_parameter_display_info(
        param_info.name, param_info.type, param_info.description
    )
    field_ids = manager.service.generate_field_ids_direct(manager.config.field_id, param_info.name)
    current_value = manager.parameters.get(param_info.name)
    unwrapped_type = _unwrap_optional_type(param_info.type) if config['needs_unwrap_type'] else None

    # Execute operations
    container = ops['create_container'](
        manager, param_info, display_info, field_ids, current_value, unwrapped_type,
        None, CURRENT_LAYOUT, QWidget, GroupBoxWithHelp, PyQt6ColorScheme
    )

    # Setup layout
    layout_type = config['layout_type']
    if layout_type == 'QHBoxLayout':
        layout = QHBoxLayout(container)
    elif layout_type == 'QVBoxLayout':
        layout = QVBoxLayout(container)
    else:  # GroupBoxWithHelp
        layout = container.layout()

    if ops['setup_layout']:
        ops['setup_layout'](
            manager, param_info, display_info, field_ids, current_value, unwrapped_type,
            layout, CURRENT_LAYOUT, QWidget, GroupBoxWithHelp, PyQt6ColorScheme
        )

    # Add label if needed
    if config['needs_label']:
        label = LabelWithHelp(
            text=display_info['field_label'],
            param_name=param_info.name,
            param_description=display_info['description'],
            param_type=param_info.type,
            color_scheme=manager.config.color_scheme or PyQt6ColorScheme()
        )
        layout.addWidget(label)

    # Add main widget
    main_widget = ops['create_main_widget'](
        manager, param_info, display_info, field_ids, current_value, unwrapped_type,
        layout, CURRENT_LAYOUT, QWidget, GroupBoxWithHelp, PyQt6ColorScheme
    )

    # For nested widgets, add to GroupBox
    # For regular widgets, add to layout
    if config['is_nested']:
        container.addWidget(main_widget)
    else:
        layout.addWidget(main_widget, 1)

    # Add reset button if needed
    if config['needs_reset_button'] and not manager.read_only:
        if config['is_nested']:
            # Nested: "Reset All" button in GroupBox title
            from PyQt6.QtWidgets import QPushButton
            reset_all_button = QPushButton("Reset All")
            reset_all_button.setMaximumWidth(80)
            reset_all_button.setToolTip(f"Reset all parameters in {display_info['field_label']} to defaults")
            # Connect to nested manager's reset_all_parameters
            nested_manager = manager.nested_managers.get(param_info.name)
            if nested_manager:
                reset_all_button.clicked.connect(lambda: nested_manager.reset_all_parameters())
            container.addTitleWidget(reset_all_button)
        else:
            # Regular: reset button in layout
            reset_button = _create_optimized_reset_button(
                manager.config.field_id,
                param_info.name,
                lambda: manager.reset_parameter(param_info.name)
            )
            layout.addWidget(reset_button)
            manager.reset_buttons[param_info.name] = reset_button

    # Store widget and connect signals
    if config['is_nested']:
        # For nested, store the GroupBox
        manager.widgets[param_info.name] = container
        logger.info(f"[CREATE_NESTED_DATACLASS] param_info.name={param_info.name}, stored GroupBoxWithHelp in manager.widgets")
    else:
        # For regular, store the main widget
        manager.widgets[param_info.name] = main_widget
        PyQt6WidgetEnhancer.connect_change_signal(main_widget, param_info.name, manager._emit_parameter_change)

        if manager.read_only:
            manager._make_widget_readonly(main_widget)

    return container


# ============================================================================
# VALIDATION
# ============================================================================

def _validate_widget_operations():
    """Validate that all widget creation types have required operations."""
    required_ops = ['create_container', 'create_main_widget']

    for creation_type, ops in _WIDGET_OPERATIONS.items():
        for op_name in required_ops:
            if op_name not in ops or ops[op_name] is None:
                raise RuntimeError(
                    f"{creation_type.value} widget creation missing operation: {op_name}"
                )

    logger.debug(f"✅ Validated {len(_WIDGET_OPERATIONS)} widget creation types")


# Run validation at module load time
_validate_widget_operations()

