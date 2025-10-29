"""
Widget creation configuration - parametric pattern.

Single source of truth for widget creation behavior (REGULAR, NESTED, and OPTIONAL_NESTED).
Mirrors openhcs/core/memory/framework_config.py pattern.

Architecture:
- Widget handlers: Custom logic for complex operations
- Unified config: Single _WIDGET_CREATION_CONFIG dict with all metadata
- Parametric dispatch: Handlers are typed callables (no eval strings)

All three widget types (REGULAR, NESTED, OPTIONAL_NESTED) are now parametrized.
OPTIONAL_NESTED reuses the same nested form creation logic as NESTED, with additional
handlers for checkbox title widget and None/instance toggle logic.
"""

from enum import Enum
from typing import Any, Callable, Optional, Type, Tuple
import logging

from .widget_creation_types import (
    ParameterFormManager, ParameterInfo, DisplayInfo, FieldIds,
    WidgetCreationConfig
)

logger = logging.getLogger(__name__)


class WidgetCreationType(Enum):
    """
    Enum for widget creation strategies - mirrors MemoryType pattern.

    PyQt6 uses 3 parametric types: REGULAR, NESTED, and OPTIONAL_NESTED.
    """
    REGULAR = "regular"
    NESTED = "nested"
    OPTIONAL_NESTED = "optional_nested"


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


def _create_nested_form(manager, param_info, display_info, field_ids, current_value, unwrapped_type, layout=None, CURRENT_LAYOUT=None, QWidget=None, GroupBoxWithHelp=None, PyQt6ColorScheme=None) -> Any:
    """
    Handler for creating nested form.

    NOTE: This creates the nested manager AND stores it in manager.nested_managers.
    The caller should NOT try to store it again.

    Extra parameters (layout, CURRENT_LAYOUT, etc.) are accepted but not used - they're
    part of the unified handler signature for consistency.
    """
    nested_manager = manager._create_nested_form_inline(
        param_info.name, unwrapped_type, current_value
    )
    # Store nested manager BEFORE building form (needed for reset button connection)
    manager.nested_managers[param_info.name] = nested_manager
    return nested_manager.build_form()


def _create_optional_title_widget(manager, param_info, display_info, field_ids, current_value, unwrapped_type):
    """
    Handler for creating optional dataclass title widget with checkbox.

    Creates: checkbox + title label + reset button + help button (all inline).
    Returns: (title_widget, checkbox) tuple for later connection.
    """
    from PyQt6.QtWidgets import QWidget, QHBoxLayout, QLabel, QPushButton
    from PyQt6.QtCore import Qt
    from PyQt6.QtGui import QFont
    from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import NoneAwareCheckBox
    from openhcs.pyqt_gui.widgets.shared.clickable_help_components import HelpButton

    title_widget = QWidget()
    title_layout = QHBoxLayout(title_widget)
    title_layout.setSpacing(5)
    title_layout.setContentsMargins(10, 5, 10, 5)

    # Checkbox (compact, no text)
    checkbox = NoneAwareCheckBox()
    checkbox.setObjectName(field_ids['optional_checkbox_id'])
    # Title checkbox ONLY controls None vs Instance, NOT the enabled field
    checkbox.setChecked(current_value is not None)
    checkbox.setMaximumWidth(20)
    title_layout.addWidget(checkbox)

    # Title label (clickable to toggle checkbox)
    title_label = QLabel(display_info['checkbox_label'])
    title_font = QFont()
    title_font.setBold(True)
    title_label.setFont(title_font)
    title_label.mousePressEvent = lambda e: checkbox.toggle()
    title_label.setCursor(Qt.CursorShape.PointingHandCursor)
    title_layout.addWidget(title_label)

    title_layout.addStretch()

    # Reset All button (will be connected later)
    reset_all_button = None
    if not manager.read_only:
        reset_all_button = QPushButton("Reset")
        reset_all_button.setMaximumWidth(60)
        reset_all_button.setFixedHeight(20)
        reset_all_button.setToolTip(f"Reset all parameters in {display_info['checkbox_label']} to defaults")
        title_layout.addWidget(reset_all_button)

    # Help button
    help_btn = HelpButton(help_target=unwrapped_type, text="?", color_scheme=manager.color_scheme)
    help_btn.setMaximumWidth(25)
    help_btn.setMaximumHeight(20)
    title_layout.addWidget(help_btn)

    return {
        'title_widget': title_widget,
        'checkbox': checkbox,
        'title_label': title_label,
        'help_btn': help_btn,
        'reset_all_button': reset_all_button,
    }


def _connect_optional_checkbox_logic(manager, param_info, checkbox, nested_form, nested_manager, title_label, help_btn, unwrapped_type):
    """
    Handler for connecting optional dataclass checkbox toggle logic.

    Checkbox controls None vs instance state (independent of enabled field).
    """
    from PyQt6.QtCore import QTimer
    from PyQt6.QtWidgets import QGraphicsOpacityEffect

    def on_checkbox_changed(checked):
        # Title checkbox controls whether config exists (None vs instance)
        nested_form.setEnabled(checked)

        if checked:
            # Config exists - create instance preserving the enabled field value
            current_param_value = manager.parameters.get(param_info.name)
            if current_param_value is None:
                # Create new instance with default enabled value
                new_instance = unwrapped_type()
                manager.update_parameter(param_info.name, new_instance)

            # Remove dimming for None state (title only)
            title_label.setStyleSheet("")
            help_btn.setEnabled(True)

            # Trigger the nested config's enabled handler to apply enabled styling
            QTimer.singleShot(0, nested_manager._apply_initial_enabled_styling)
        else:
            # Config is None - set to None and block inputs
            manager.update_parameter(param_info.name, None)

            # Apply dimming for None state
            title_label.setStyleSheet(f"color: {manager.color_scheme.to_hex(manager.color_scheme.text_disabled)};")
            help_btn.setEnabled(True)
            # ANTI-DUCK-TYPING: Use ABC-based widget discovery
            for widget in manager._widget_ops.get_all_value_widgets(nested_form):
                effect = QGraphicsOpacityEffect()
                effect.setOpacity(0.4)
                widget.setGraphicsEffect(effect)

    checkbox.toggled.connect(on_checkbox_changed)

    # Register callback for initial styling (deferred until after all widgets are created)
    def apply_initial_styling():
        on_checkbox_changed(checkbox.isChecked())

    manager._on_build_complete_callbacks.append(apply_initial_styling)


def _create_regular_container(manager: ParameterFormManager, param_info: ParameterInfo,
                             display_info: DisplayInfo, field_ids: FieldIds, current_value: Any,
                             unwrapped_type: Optional[Type], layout=None, CURRENT_LAYOUT=None,
                             QWidget=None, GroupBoxWithHelp=None, PyQt6ColorScheme=None) -> Any:
    """Create container for REGULAR widget type."""
    from PyQt6.QtWidgets import QWidget as QtWidget
    return QtWidget()


def _create_nested_container(manager: ParameterFormManager, param_info: ParameterInfo,
                            display_info: DisplayInfo, field_ids: FieldIds, current_value: Any,
                            unwrapped_type: Optional[Type], layout=None, CURRENT_LAYOUT=None,
                            QWidget=None, GroupBoxWithHelp=None, PyQt6ColorScheme=None) -> Any:
    """Create container for NESTED widget type."""
    from openhcs.pyqt_gui.widgets.shared.clickable_help_components import GroupBoxWithHelp as GBH
    from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme as PCS

    color_scheme = manager.config.color_scheme or PCS()
    return GBH(title=display_info['field_label'], help_target=unwrapped_type, color_scheme=color_scheme)


def _create_optional_nested_container(manager: ParameterFormManager, param_info: ParameterInfo,
                                     display_info: DisplayInfo, field_ids: FieldIds, current_value: Any,
                                     unwrapped_type: Optional[Type], layout=None, CURRENT_LAYOUT=None,
                                     QWidget=None, GroupBoxWithHelp=None, PyQt6ColorScheme=None) -> Any:
    """Create container for OPTIONAL_NESTED widget type."""
    from PyQt6.QtWidgets import QGroupBox
    return QGroupBox()


def _setup_regular_layout(manager: ParameterFormManager, param_info: ParameterInfo,
                         display_info: DisplayInfo, field_ids: FieldIds, current_value: Any,
                         unwrapped_type: Optional[Type], layout=None, CURRENT_LAYOUT=None,
                         QWidget=None, GroupBoxWithHelp=None, PyQt6ColorScheme=None) -> None:
    """Setup layout for REGULAR widget type."""
    layout.setSpacing(CURRENT_LAYOUT.parameter_row_spacing)
    layout.setContentsMargins(*CURRENT_LAYOUT.parameter_row_margins)


def _setup_optional_nested_layout(manager: ParameterFormManager, param_info: ParameterInfo,
                                 display_info: DisplayInfo, field_ids: FieldIds, current_value: Any,
                                 unwrapped_type: Optional[Type], container=None, QVBoxLayout=None,
                                 QWidget=None, GroupBoxWithHelp=None, PyQt6ColorScheme=None) -> None:
    """Setup layout for OPTIONAL_NESTED widget type."""
    from PyQt6.QtWidgets import QVBoxLayout as QVL
    container.setLayout(QVL())
    container.layout().setSpacing(0)
    container.layout().setContentsMargins(0, 0, 0, 0)


# ============================================================================
# UNIFIED WIDGET CREATION CONFIGURATION (typed, no eval strings)
# ============================================================================

_WIDGET_CREATION_CONFIG: dict[WidgetCreationType, WidgetCreationConfig] = {
    WidgetCreationType.REGULAR: WidgetCreationConfig(
        layout_type='QHBoxLayout',
        is_nested=False,
        create_container=_create_regular_container,
        setup_layout=_setup_regular_layout,
        create_main_widget=lambda manager, param_info, display_info, field_ids, current_value, unwrapped_type, *args, **kwargs:
            manager.create_widget(param_info.name, param_info.type, current_value, field_ids['widget_id']),
        needs_label=True,
        needs_reset_button=True,
        needs_unwrap_type=False,
    ),

    WidgetCreationType.NESTED: WidgetCreationConfig(
        layout_type='GroupBoxWithHelp',
        is_nested=True,
        create_container=_create_nested_container,
        setup_layout=None,
        create_main_widget=_create_nested_form,
        needs_label=False,
        needs_reset_button=True,
        needs_unwrap_type=True,
        is_optional=False,
    ),

    WidgetCreationType.OPTIONAL_NESTED: WidgetCreationConfig(
        layout_type='QGroupBox',
        is_nested=True,
        create_container=_create_optional_nested_container,
        setup_layout=_setup_optional_nested_layout,
        create_main_widget=_create_nested_form,
        needs_label=False,
        needs_reset_button=True,
        needs_unwrap_type=True,
        is_optional=True,
        needs_checkbox=True,
        create_title_widget=_create_optional_title_widget,
        connect_checkbox_logic=_connect_optional_checkbox_logic,
    ),
}


# ============================================================================
# WIDGET OPERATIONS - Direct access to typed config (no eval)
# ============================================================================

def _get_widget_operations(creation_type: WidgetCreationType) -> dict[str, Callable]:
    """Get typed widget operations for a creation type."""
    config = _WIDGET_CREATION_CONFIG[creation_type]
    ops = {
        'create_container': config.create_container,
        'create_main_widget': config.create_main_widget,
    }
    if config.setup_layout:
        ops['setup_layout'] = config.setup_layout
    if config.create_title_widget:
        ops['create_title_widget'] = config.create_title_widget
    if config.connect_checkbox_logic:
        ops['connect_checkbox_logic'] = config.connect_checkbox_logic
    return ops


# ============================================================================
# UNIFIED WIDGET CREATION FUNCTION
# ============================================================================

def create_widget_parametric(manager: ParameterFormManager, param_info: ParameterInfo,
                           creation_type: WidgetCreationType) -> Any:
    """
    UNIFIED: Create widget using parametric dispatch.

    Replaces _create_regular_parameter_widget, _create_nested_dataclass_widget,
    and _create_optional_dataclass_widget.

    Args:
        manager: ParameterFormManager instance
        param_info: Parameter information object
        creation_type: Widget creation type (REGULAR, NESTED, or OPTIONAL_NESTED)

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
    ops = _get_widget_operations(creation_type)

    # Prepare context
    display_info = manager.service.get_parameter_display_info(
        param_info.name, param_info.type, param_info.description
    )
    field_ids = manager.service.generate_field_ids_direct(manager.config.field_id, param_info.name)
    current_value = manager.parameters.get(param_info.name)
    unwrapped_type = _unwrap_optional_type(param_info.type) if config.needs_unwrap_type else None

    # Execute operations
    container = ops['create_container'](
        manager, param_info, display_info, field_ids, current_value, unwrapped_type,
        None, CURRENT_LAYOUT, QWidget, GroupBoxWithHelp, PyQt6ColorScheme
    )

    # Setup layout
    layout_type = config.layout_type
    if layout_type == 'QHBoxLayout':
        layout = QHBoxLayout(container)
    elif layout_type == 'QVBoxLayout':
        layout = QVBoxLayout(container)
    elif layout_type == 'QGroupBox':
        # OPTIONAL_NESTED: setup_layout creates the layout
        layout = None  # Will be set by setup_layout
    else:  # GroupBoxWithHelp
        layout = container.layout()

    if ops.get('setup_layout'):
        ops['setup_layout'](
            manager, param_info, display_info, field_ids, current_value, unwrapped_type,
            layout, CURRENT_LAYOUT, QWidget, GroupBoxWithHelp, PyQt6ColorScheme
        )
        # For OPTIONAL_NESTED, get the layout after setup
        if layout_type == 'QGroupBox':
            layout = container.layout()

    # Add title widget if needed (OPTIONAL_NESTED only)
    title_components = None
    if config.is_optional:
        title_components = ops['create_title_widget'](
            manager, param_info, display_info, field_ids, current_value, unwrapped_type
        )
        layout.addWidget(title_components['title_widget'])

    # Add label if needed (REGULAR only)
    if config.needs_label:
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

    # For nested widgets, add to container
    # For regular widgets, add to layout
    if config.is_nested:
        if config.is_optional:
            # OPTIONAL_NESTED: set enabled state based on current_value
            main_widget.setEnabled(current_value is not None)
        layout.addWidget(main_widget)
    else:
        layout.addWidget(main_widget, 1)

    # Add reset button if needed
    if config.needs_reset_button and not manager.read_only:
        if config.is_optional:
            # OPTIONAL_NESTED: reset button already in title widget, just connect it
            if title_components and title_components['reset_all_button']:
                nested_manager = manager.nested_managers.get(param_info.name)
                if nested_manager:
                    title_components['reset_all_button'].clicked.connect(lambda: nested_manager.reset_all_parameters())
        elif config.is_nested:
            # NESTED: "Reset All" button in GroupBox title
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
            # REGULAR: reset button in layout
            reset_button = _create_optimized_reset_button(
                manager.config.field_id,
                param_info.name,
                lambda: manager.reset_parameter(param_info.name)
            )
            layout.addWidget(reset_button)
            manager.reset_buttons[param_info.name] = reset_button

    # Connect checkbox logic if needed (OPTIONAL_NESTED only)
    if config.needs_checkbox and title_components:
        nested_manager = manager.nested_managers.get(param_info.name)
        if nested_manager:
            ops['connect_checkbox_logic'](
                manager, param_info,
                title_components['checkbox'],
                main_widget,
                nested_manager,
                title_components['title_label'],
                title_components['help_btn'],
                unwrapped_type
            )

    # Store widget and connect signals
    if config.is_nested:
        # For nested, store the GroupBox/container
        manager.widgets[param_info.name] = container
        logger.info(f"[CREATE_NESTED_DATACLASS] param_info.name={param_info.name}, stored container in manager.widgets")
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

def _validate_widget_operations() -> None:
    """Validate that all widget creation types have required operations."""
    for creation_type, config in _WIDGET_CREATION_CONFIG.items():
        if config.create_container is None:
            raise RuntimeError(f"{creation_type.value}: create_container is required")
        if config.create_main_widget is None:
            raise RuntimeError(f"{creation_type.value}: create_main_widget is required")

    logger.debug(f"✅ Validated {len(_WIDGET_CREATION_CONFIG)} widget creation types")


# Run validation at module load time
_validate_widget_operations()

