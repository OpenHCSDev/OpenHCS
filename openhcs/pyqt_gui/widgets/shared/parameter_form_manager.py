"""
Dramatically simplified PyQt parameter form manager.

This demonstrates how the widget implementation can be drastically simplified
by leveraging the comprehensive shared infrastructure we've built.
"""

import dataclasses
import logging
from typing import Any, Dict, Type, Optional
from dataclasses import replace
from PyQt6.QtWidgets import QWidget, QVBoxLayout, QHBoxLayout, QScrollArea, QLabel, QPushButton, QLineEdit, QCheckBox, QComboBox
from PyQt6.QtCore import Qt, pyqtSignal

# Imports for masking logic (moved from inline)
from openhcs.core.context.global_config import get_current_global_config, set_current_global_config
from openhcs.core.config import GlobalPipelineConfig

# Mathematical simplification: Shared dispatch tables to eliminate duplication
WIDGET_UPDATE_DISPATCH = [
    (QComboBox, 'update_combo_box'),
    ('get_selected_values', 'update_checkbox_group'),
    ('setChecked', lambda w, v: w.setChecked(bool(v))),
    ('setValue', lambda w, v: w.setValue(v or 0)),
    ('set_value', lambda w, v: w.set_value(v)),
    ('setText', lambda w, v: v is not None and w.setText(str(v))),
    ('clear', lambda w, v: v is None and w.clear())
]

WIDGET_GET_DISPATCH = [
    (QComboBox, lambda w: w.itemData(w.currentIndex()) if w.currentIndex() >= 0 else None),
    ('get_selected_values', lambda w: w.get_selected_values()),
    ('get_value', lambda w: w.get_value()),
    ('isChecked', lambda w: w.isChecked()),
    ('value', lambda w: None if (hasattr(w, 'specialValueText') and w.value() == w.minimum() and w.specialValueText()) else w.value()),
    ('text', lambda w: w.text())
]

logger = logging.getLogger(__name__)

# Import our comprehensive shared infrastructure
from openhcs.ui.shared.parameter_form_service import ParameterFormService, ParameterInfo
from openhcs.ui.shared.parameter_form_config_factory import pyqt_config
from openhcs.ui.shared.parameter_form_constants import CONSTANTS

from openhcs.ui.shared.widget_creation_registry import create_pyqt6_registry
from openhcs.ui.shared.ui_utils import format_param_name, format_field_id, format_reset_button_id
from .widget_strategies import PyQt6WidgetEnhancer

# Import PyQt-specific components
from .clickable_help_components import GroupBoxWithHelp, LabelWithHelp
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme

# Import OpenHCS core components
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils





class NoneAwareLineEdit(QLineEdit):
    """QLineEdit that properly handles None values for lazy dataclass contexts."""

    def get_value(self):
        """Get value, returning None for empty text instead of empty string."""
        text = self.text().strip()
        return None if text == "" else text

    def set_value(self, value):
        """Set value, handling None properly."""
        self.setText("" if value is None else str(value))


class ParameterFormManager(QWidget):
    """
    PyQt6 parameter form manager with simplified implementation.

    This implementation uses shared infrastructure while maintaining
    exact backward compatibility with the original API.

    Key improvements:
    - Internal implementation reduced by ~85%
    - Parameter analysis delegated to service layer
    - Widget creation patterns centralized
    - All magic strings eliminated
    - Type checking delegated to utilities
    - Clean, minimal implementation focused on core functionality
    """

    parameter_changed = pyqtSignal(str, object)  # param_name, value

    def __init__(self, parameters: Dict[str, Any], parameter_types: Dict[str, type],
                 field_id: str, dataclass_type: Type, parameter_info: Dict = None, parent=None,
                 use_scroll_area: bool = True, function_target=None,
                 color_scheme: Optional[PyQt6ColorScheme] = None, placeholder_prefix: str = None,
                 param_defaults: Dict[str, Any] = None):
        """
        Initialize PyQt parameter form manager with mathematically elegant single-parameter design.

        Args:
            parameters: Dictionary of parameter names to current values
            parameter_types: Dictionary of parameter names to types
            field_id: Unique identifier for the form
            dataclass_type: The dataclass type that deterministically controls all form behavior
            parameter_info: Optional parameter information dictionary
            parent: Optional parent widget
            use_scroll_area: Whether to use scroll area
            function_target: Optional function target for docstring fallback
            color_scheme: Optional PyQt color scheme
            placeholder_prefix: Prefix for placeholder text
        """
        QWidget.__init__(self, parent)

        # Store configuration parameters - dataclass_type is the single source of truth
        self.parent = parent  # Store parent for step-level config detection
        self.dataclass_type = dataclass_type
        self.placeholder_prefix = placeholder_prefix or CONSTANTS.DEFAULT_PLACEHOLDER_PREFIX

        # Convert old API to new config object internally
        if color_scheme is None:
            color_scheme = PyQt6ColorScheme()

        config = pyqt_config(
            field_id=field_id,
            color_scheme=color_scheme,
            function_target=function_target,
            use_scroll_area=use_scroll_area
        )
        config.parameter_info = parameter_info
        config.dataclass_type = dataclass_type
        config.placeholder_prefix = placeholder_prefix
        # Mathematical simplification: Cache lazy resolution check to avoid repeated calls
        config.is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type)
        config.is_global_config_editing = not config.is_lazy_dataclass

        # Initialize core attributes directly (avoid abstract class instantiation)
        self.parameters = parameters.copy()
        self.parameter_types = parameter_types
        self.config = config
        self.param_defaults = param_defaults or {}

        # Initialize service layer for business logic
        self.service = ParameterFormService()

        # Initialize tracking attributes
        self.widgets = {}
        self.reset_buttons = {}  # Track reset buttons for API compatibility
        self.nested_managers = {}

        # CRITICAL FIX: Track which fields have been explicitly set by users
        # This prevents placeholder updates from destroying user values
        self._user_set_fields: set = set()

        # Store public API attributes for backward compatibility
        self.field_id = field_id
        self.parameter_info = parameter_info or {}
        self.use_scroll_area = use_scroll_area
        self.function_target = function_target
        self.color_scheme = color_scheme
        # Note: dataclass_type already stored above

        # Analyze form structure once using service layer
        self.form_structure = self.service.analyze_parameters(
            parameters, parameter_types, config.field_id, config.parameter_info, self.dataclass_type
        )

        # Get widget creator from registry
        self.create_widget = create_pyqt6_registry()


        # Set up UI
        self.setup_ui()

        # CRITICAL FIX: Refresh placeholders after form is built to show inheritance
        self._refresh_all_placeholders_with_current_context()

    @classmethod
    def from_dataclass_instance(cls, dataclass_instance: Any, field_id: str,
                              placeholder_prefix: str = "Default",
                              parent=None, use_scroll_area: bool = True,
                              function_target=None, color_scheme=None,
                              force_show_all_fields: bool = False):
        """
        Create ParameterFormManager for editing entire dataclass instance.

        This replaces LazyDataclassEditor functionality by automatically extracting
        parameters from the dataclass instance and creating the form manager.

        Args:
            dataclass_instance: The dataclass instance to edit
            field_id: Unique identifier for the form
            placeholder_prefix: Prefix for placeholder text
            parent: Parent widget
            use_scroll_area: Whether to use scroll area
            function_target: Optional function target
            color_scheme: Optional color scheme

        Returns:
            ParameterFormManager configured for dataclass editing
        """
        from dataclasses import fields, is_dataclass

        if not is_dataclass(dataclass_instance):
            raise ValueError(f"{type(dataclass_instance)} is not a dataclass")

        # Mathematical simplification: Unified parameter extraction for both lazy and regular dataclasses
        is_lazy = hasattr(dataclass_instance, '_resolve_field_value')
        parameters = {}
        parameter_types = {}

        # CRITICAL FIX: Get dataclass type BEFORE the loop, not inside it
        dataclass_type = type(dataclass_instance)

        # Algebraic simplification: Single loop with conditional attribute access
        for field_obj in fields(dataclass_instance):
            parameters[field_obj.name] = (object.__getattribute__(dataclass_instance, field_obj.name) if is_lazy
                                        else getattr(dataclass_instance, field_obj.name))
            parameter_types[field_obj.name] = field_obj.type

        # Create ParameterFormManager with extracted data
        form_manager = cls(
            parameters=parameters,
            parameter_types=parameter_types,
            field_id=field_id,
            dataclass_type=dataclass_type,  # Use determined dataclass type
            parameter_info=None,
            parent=parent,
            use_scroll_area=use_scroll_area,
            function_target=function_target,
            color_scheme=color_scheme,
            placeholder_prefix=placeholder_prefix
        )

        # Store the original dataclass instance for reset operations
        form_manager._current_config_instance = dataclass_instance

        return form_manager

    def setup_ui(self):
        """Set up the UI layout."""
        layout = QVBoxLayout(self)

        # Build form content
        form_widget = self.build_form()

        # Add scroll area if requested
        if self.config.use_scroll_area:
            scroll_area = QScrollArea()
            scroll_area.setWidgetResizable(True)
            scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
            scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
            scroll_area.setWidget(form_widget)
            layout.addWidget(scroll_area)
        else:
            layout.addWidget(form_widget)

    def build_form(self) -> QWidget:
        """
        Build the complete form UI.

        Dramatically simplified by delegating analysis to service layer
        and using centralized widget creation patterns.
        """
        content_widget = QWidget()
        content_layout = QVBoxLayout(content_widget)

        # Use unified widget creation for all parameter types
        for param_info in self.form_structure.parameters:
            widget = self._create_parameter_widget_unified(param_info)
            content_layout.addWidget(widget)

        return content_widget

    def _create_parameter_widget_unified(self, param_info) -> QWidget:
        """Unified widget creation handling all parameter types."""
        return self._create_parameter_section(param_info)

    def _create_parameter_section(self, param_info) -> QWidget:
        """Mathematical simplification: Unified parameter section creation with dispatch table."""
        display_info = self.service.get_parameter_display_info(param_info.name, param_info.type, param_info.description)
        field_ids = self.service.generate_field_ids(self.config.field_id, param_info.name)

        # Algebraic simplification: Single expression for content type dispatch
        container, widgets = (
            self._build_optional_content(param_info, display_info, field_ids) if param_info.is_optional and param_info.is_nested
            else self._build_nested_content(param_info, display_info, field_ids) if param_info.is_nested
            else self._build_regular_content(param_info, display_info, field_ids)
        )

        # Unified widget registration
        self.widgets[param_info.name] = widgets['main']
        if 'reset_button' in widgets:
            self.reset_buttons[param_info.name] = widgets['reset_button']
        if 'widget' in widgets:
            PyQt6WidgetEnhancer.connect_change_signal(widgets['widget'], param_info.name, self._emit_parameter_change)

        return container

    def _build_regular_content(self, param_info, display_info, field_ids):
        container = QWidget()
        layout = QHBoxLayout(container)
        label = LabelWithHelp(
            text=display_info['field_label'], param_name=param_info.name,
            param_description=display_info['description'], param_type=param_info.type,
            color_scheme=self.config.color_scheme or PyQt6ColorScheme()
        )
        layout.addWidget(label)
        current_value = self.parameters.get(param_info.name)
        widget = self.create_widget(
            param_info.name, param_info.type, current_value,
            f"{self.field_id}_{param_info.name}",
            self.parameter_info.get(param_info.name)
        )
        # SIMPLIFIED: Use thread-local context during initial widget creation to avoid recursion
        if current_value is None and self.config.is_lazy_dataclass:
            placeholder_text = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                self.dataclass_type, param_info.name,
                placeholder_prefix=self.placeholder_prefix
            )
            if placeholder_text:
                # Apply placeholder to all widget types using PyQt6WidgetEnhancer
                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
        widget.setObjectName(field_ids['widget_id'])
        layout.addWidget(widget, 1)
        reset_button = QPushButton(CONSTANTS.RESET_BUTTON_TEXT)
        reset_button.setObjectName(field_ids['reset_button_id'])
        reset_button.setMaximumWidth(60)
        reset_button.clicked.connect(lambda: self.reset_parameter(param_info.name))
        layout.addWidget(reset_button)
        return container, {'main': widget, 'widget': widget, 'reset_button': reset_button}

    def _build_nested_content(self, param_info, display_info, field_ids):
        group_box = GroupBoxWithHelp(
            title=display_info['field_label'], help_target=param_info.type,
            color_scheme=self.config.color_scheme or PyQt6ColorScheme()
        )
        current_value = self.parameters.get(param_info.name)

        # Mathematical simplification: Unified nested type resolution
        nested_type = self._get_actual_nested_type_from_signature(param_info.type) or param_info.type

        # Algebraic simplification: Single conditional for lazy resolution
        if LazyDefaultPlaceholderService.has_lazy_resolution(nested_type):
            # Mathematical simplification: Inline instance creation without helper method
            if current_value and not isinstance(current_value, nested_type):
                # Convert base to lazy instance via direct field mapping
                from dataclasses import fields
                try:
                    lazy_instance = nested_type(**{f.name: getattr(current_value, f.name) for f in fields(current_value)})
                except Exception:
                    lazy_instance = nested_type()
            else:
                lazy_instance = current_value or nested_type()

            nested_manager = ParameterFormManager.from_dataclass_instance(
                dataclass_instance=lazy_instance,
                field_id=f"nested_{param_info.name}",
                placeholder_prefix=self.placeholder_prefix,
                parent=group_box, use_scroll_area=False,
                color_scheme=self.config.color_scheme
            )

            # Unified manager setup
            self.nested_managers[param_info.name] = nested_manager
            nested_manager.parameter_changed.connect(
                lambda name, value, parent_name=param_info.name: self._handle_nested_parameter_change(parent_name, None)
            )
            group_box.content_layout.addWidget(nested_manager)
        else:
            # Non-lazy fallback
            nested_form = self._create_nested_form_inline(param_info.name, param_info.type, current_value)
            group_box.content_layout.addWidget(nested_form)

        return group_box, {'main': group_box}

    def _get_actual_nested_type_from_signature(self, field_type: Type) -> Type:
        """Mathematical simplification: Extract nested type from Optional or return direct type."""
        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
        from dataclasses import is_dataclass

        # Algebraic simplification: Single expression for type extraction
        return (ParameterTypeUtils.get_optional_inner_type(field_type)
                if ParameterTypeUtils.is_optional_dataclass(field_type)
                else field_type if is_dataclass(field_type) else None)

    def _build_optional_content(self, param_info, display_info, field_ids):
        container = QWidget()
        layout = QVBoxLayout(container)
        checkbox = QCheckBox(display_info['field_label'])
        current_value = self.parameters.get(param_info.name)
        # Check if this is a step-level config that should start unchecked
        # This now works generically for any optional lazy dataclass parameter
        is_step_level_config = (hasattr(self, 'parent') and
                               hasattr(self.parent, '_step_level_configs') and
                               param_info.name in getattr(self.parent, '_step_level_configs', {}))

        if is_step_level_config:
            # Step-level configs start unchecked even if current_value is not None
            checkbox.setChecked(False)
            # Store the step-level config for later use
            if not hasattr(self, '_step_level_config_values'):
                self._step_level_config_values = {}
            self._step_level_config_values[param_info.name] = current_value
            # Set current_value to None for the form logic
            current_value = None
        else:
            checkbox.setChecked(current_value is not None)
        layout.addWidget(checkbox)
        inner_type = ParameterTypeUtils.get_optional_inner_type(param_info.type)
        # For step-level configs, use the stored config for nested content but keep checkbox unchecked
        nested_current_value = current_value
        if is_step_level_config and hasattr(self, '_step_level_config_values'):
            nested_current_value = self._step_level_config_values[param_info.name]

        nested_param_info = ParameterInfo(param_info.name, inner_type, nested_current_value, True, False)
        nested_widget, nested_widgets = self._build_nested_content(nested_param_info, display_info, field_ids)
        nested_widget.setEnabled(checkbox.isChecked())
        layout.addWidget(nested_widget)
        def toggle(state):
            enabled = state == 2
            nested_widget.setEnabled(enabled)
            new_value = inner_type() if enabled else None
            self.parameters[param_info.name] = new_value
            self.parameter_changed.emit(param_info.name, new_value)
        checkbox.stateChanged.connect(toggle)
        return container, {'main': container}

    def _create_nested_form_inline(self, param_name: str, param_type: Type, current_value: Any) -> Any:
        """Create nested form - inlined from create_nested_form."""
        # Extract nested parameters using service with parent context (handles both dataclass and non-dataclass contexts)
        nested_params, nested_types = self.service.extract_nested_parameters(
            current_value, param_type, self.dataclass_type
        )

        # Get field IDs from service
        field_ids = self.service.generate_field_ids(self.config.field_id, param_name)

        # Return nested manager with inherited configuration
        nested_manager = ParameterFormManager(
            nested_params,
            nested_types,
            field_ids['nested_field_id'],
            param_type,    # Use the actual nested dataclass type, not parent type
            None,  # parameter_info
            None,  # parent
            False,  # use_scroll_area
            None,   # function_target
            PyQt6ColorScheme(),  # color_scheme
            self.placeholder_prefix # Pass through placeholder prefix
        )

        # Store nested manager
        self.nested_managers[param_name] = nested_manager

        return nested_manager



    def _apply_placeholder_with_lazy_context(self, widget: QWidget, param_name: str, current_value: Any, masked_fields: Optional[set] = None) -> None:
        """Apply placeholder using current form state, not saved thread-local state."""
        # Only apply placeholder if value is None
        if current_value is not None:
            return

        # Mathematical simplification: Use cached lazy resolution check
        if not self.config.is_lazy_dataclass:
            return

        # CRITICAL FIX: Build context from current form values instead of using thread-local context
        current_form_context = self._build_context_from_current_form_values()

        # Get placeholder resolved against current form state
        placeholder_text = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            self.dataclass_type, param_name,
            app_config=current_form_context,  # Use current form context
            placeholder_prefix=self.placeholder_prefix
        )

        if placeholder_text is None:
            return

        # Apply placeholder using the working logic
        if hasattr(widget, 'setPlaceholderText'):
            widget.setPlaceholderText(placeholder_text)

        # Block signals to prevent placeholder application from triggering parameter updates
        widget.blockSignals(True)
        try:
            # Use PyQt6WidgetEnhancer logic for visual styling
            PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
        finally:
            # Always restore signal connections
            widget.blockSignals(False)

#    def _format_placeholder_text(self, raw_placeholder: Optional[str]) -> Optional[str]:
#        """Mathematical simplification: Use existing enum formatting utilities."""
#        return raw_placeholder  # Existing LazyDefaultPlaceholderService already handles enum formatting correctly





    def _build_context_from_current_form_values(self) -> Any:
        """Build context preserving complete inheritance hierarchy for MRO-based placeholder resolution."""
        from openhcs.core.context.global_config import get_current_global_config
        from openhcs.core.config import GlobalPipelineConfig
        from dataclasses import replace

        # Get current thread-local context as base - this contains ALL dataclass instances
        current_context = get_current_global_config(GlobalPipelineConfig)
        if not current_context:
            return None

        # CRITICAL FIX: Return the complete context with ALL dataclass instances
        # This preserves the full inheritance hierarchy needed for MRO-based resolution
        # The placeholder resolution system needs to see the complete hierarchy:
        # - well_filter_config: LazyWellFilterConfig(well_filter='2')
        # - step_well_filter_config: LazyStepWellFilterConfig(well_filter='5')
        # - step_materialization_config: LazyStepMaterializationConfig(well_filter=None)
        #
        # When resolving StepMaterializationConfig.well_filter, the MRO walk will:
        # 1. Check StepMaterializationConfig (well_filter=None) -> continue
        # 2. Check StepWellFilterConfig (well_filter='5') -> FOUND! Use this value
        # 3. Skip WellFilterConfig (well_filter='2') -> lower precedence

        # CRITICAL FIX: Collect current values from ALL nested managers (sibling forms)
        # This ensures placeholder resolution sees current unsaved values from all forms
        context_updates = {}

        # Update THIS form's dataclass instance
        form_field_name = self.field_id
        if hasattr(current_context, form_field_name):
            current_dataclass_instance = getattr(current_context, form_field_name)
            if current_dataclass_instance:
                # CRITICAL FIX: Get current widget values, not just stored parameters
                # This captures values that are typed but not yet saved to parameters
                current_form_values = self.parameters.copy()

                # CRITICAL FIX: Force read current widget values to capture unsaved typing
                for param_name, widget in self.widgets.items():
                    try:
                        widget_value = None

                        # Try multiple methods to get the current widget value
                        if hasattr(widget, 'get_value'):
                            widget_value = widget.get_value()
                        elif hasattr(widget, 'text'):
                            widget_value = widget.text()
                        elif hasattr(widget, 'isChecked'):
                            widget_value = widget.isChecked()
                        elif hasattr(widget, 'currentData'):
                            widget_value = widget.currentData()
                        elif hasattr(widget, 'value'):
                            widget_value = widget.value()
                        elif hasattr(widget, 'currentText'):
                            widget_value = widget.currentText()

                        # Update if widget has any value (including empty string)
                        if widget_value is not None:
                            # Convert empty string to None for consistency
                            if widget_value == "":
                                widget_value = None
                            current_form_values[param_name] = widget_value
                            print(f"🔍 WIDGET DEBUG: {self.field_id}.{param_name} widget value = '{widget_value}'")
                    except Exception as e:
                        print(f"🔍 WIDGET DEBUG: Failed to get {param_name} widget value: {e}")
                        pass

                # Update with current form values (including widget values)
                updated_instance = replace(current_dataclass_instance, **current_form_values)
                context_updates[form_field_name] = updated_instance

        # CRITICAL FIX: Also collect current values from all nested managers
        # This captures unsaved values from sibling forms like well_filter_config
        for nested_name, nested_manager in self.nested_managers.items():
            if hasattr(current_context, nested_name):
                current_nested_instance = getattr(current_context, nested_name)
                if current_nested_instance and hasattr(nested_manager, 'parameters'):
                    # CRITICAL FIX: Get current widget values directly, not just parameters
                    # This ensures we capture values that are typed but not yet saved to parameters
                    current_nested_values = {}

                    # First, get values from parameters
                    current_nested_values.update(nested_manager.parameters)
                    print(f"🔍 NESTED PARAMS DEBUG: {nested_name}.parameters = {nested_manager.parameters}")

                    # Then, override with current widget values to capture unsaved typing
                    for param_name, widget in nested_manager.widgets.items():
                        try:
                            widget_value = None

                            if hasattr(widget, 'get_value'):
                                widget_value = widget.get_value()
                            elif hasattr(widget, 'text'):
                                widget_value = widget.text()
                            elif hasattr(widget, 'isChecked'):
                                widget_value = widget.isChecked()
                            elif hasattr(widget, 'currentData'):
                                widget_value = widget.currentData()
                            elif hasattr(widget, 'value'):
                                widget_value = widget.value()
                            elif hasattr(widget, 'currentText'):
                                widget_value = widget.currentText()
                            else:
                                continue

                            # Update if widget has any value (including empty string)
                            if widget_value is not None:
                                # Convert empty string to None for consistency
                                if widget_value == "":
                                    widget_value = None
                                current_nested_values[param_name] = widget_value
                                print(f"🔍 NESTED WIDGET DEBUG: {nested_name}.{param_name} widget value = '{widget_value}'")
                        except Exception as e:
                            print(f"🔍 NESTED WIDGET DEBUG: Failed to get {nested_name}.{param_name} widget value: {e}")
                            pass

                    # Update nested instance with current form values (including widget values)
                    updated_nested = replace(current_nested_instance, **current_nested_values)
                    context_updates[nested_name] = updated_nested

        # Return updated context preserving COMPLETE inheritance hierarchy with current form values
        return replace(current_context, **context_updates) if context_updates else current_context

    def _refresh_all_placeholders_with_current_context(self) -> None:
        """Refresh all placeholders using current form values to show inheritance."""
        if not self.config.is_lazy_dataclass:
            return

        # Build context from current form values
        current_form_context = self._build_context_from_current_form_values()

        # Refresh placeholders for all None-valued fields
        for param_name, widget in self.widgets.items():
            current_value = self.parameters.get(param_name)
            if current_value is None:
                placeholder_text = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                    self.dataclass_type, param_name,
                    app_config=current_form_context,
                    placeholder_prefix=self.placeholder_prefix
                )
                if placeholder_text:
                    PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)

    def _emit_parameter_change(self, param_name: str, value: Any) -> None:
        """Handle parameter change from widget and update parameter data model."""
        # Convert value using service layer
        converted_value = self.service.convert_value_to_type(value, self.parameter_types.get(param_name, type(value)), param_name, self.dataclass_type)

        # Update parameter in data model
        self.parameters[param_name] = converted_value

        # CRITICAL FIX: Track that user explicitly set this field
        # This prevents placeholder updates from destroying user values
        self._user_set_fields.add(param_name)

        # Emit signal only once - this triggers sibling placeholder updates
        self.parameter_changed.emit(param_name, converted_value)



    def update_widget_value(self, widget: QWidget, value: Any, param_name: str = None, skip_context_behavior: bool = False) -> None:
        """Mathematical simplification: Unified widget update using shared dispatch."""
        self._execute_with_signal_blocking(widget, lambda: self._dispatch_widget_update(widget, value))

        # Only apply context behavior if not explicitly skipped (e.g., during reset operations)
        if not skip_context_behavior:
            self._apply_context_behavior(widget, value, param_name)

    def _dispatch_widget_update(self, widget: QWidget, value: Any) -> None:
        """Algebraic simplification: Single dispatch logic for all widget updates."""
        for matcher, updater in WIDGET_UPDATE_DISPATCH:
            if isinstance(widget, matcher) if isinstance(matcher, type) else hasattr(widget, matcher):
                if isinstance(updater, str):
                    getattr(self, f'_{updater}')(widget, value)
                else:
                    updater(widget, value)
                return



    def _update_combo_box(self, widget: QComboBox, value: Any) -> None:
        """Update combo box with value matching."""
        widget.setCurrentIndex(-1 if value is None else
                             next((i for i in range(widget.count()) if widget.itemData(i) == value), -1))

    def _update_checkbox_group(self, widget: QWidget, value: Any) -> None:
        """Update checkbox group using functional operations."""
        if hasattr(widget, '_checkboxes') and isinstance(value, list):
            # Functional: reset all, then set selected
            [cb.setChecked(False) for cb in widget._checkboxes.values()]
            [widget._checkboxes[v].setChecked(True) for v in value if v in widget._checkboxes]

    def _execute_with_signal_blocking(self, widget: QWidget, operation: callable) -> None:
        """Execute operation with signal blocking - stateless utility."""
        widget.blockSignals(True)
        operation()
        widget.blockSignals(False)

    def _apply_context_behavior(self, widget: QWidget, value: Any, param_name: str) -> None:
        """Apply lazy placeholder context behavior - pure function of inputs."""
        if not param_name or not self.dataclass_type:
            return

        if value is None and self.config.is_lazy_dataclass:
            # CRITICAL FIX: Use orchestrator-specific context instead of thread-local context
            current_form_context = self._build_context_from_current_form_values()
            placeholder_text = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                self.dataclass_type, param_name,
                app_config=current_form_context,
                placeholder_prefix=self.placeholder_prefix
            )
            if placeholder_text:
                # Apply placeholder to all widget types using PyQt6WidgetEnhancer
                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
        elif value is not None:
            PyQt6WidgetEnhancer._clear_placeholder_state(widget)


    def get_widget_value(self, widget: QWidget) -> Any:
        """Mathematical simplification: Unified widget value extraction using shared dispatch."""
        for matcher, extractor in WIDGET_GET_DISPATCH:
            if isinstance(widget, matcher) if isinstance(matcher, type) else hasattr(widget, matcher):
                return extractor(widget)
        return None

    # Framework-specific methods for backward compatibility

    def reset_all_parameters(self) -> None:
        """Reset all parameters - let reset_parameter handle everything."""
        for param_name in self.parameters.keys():
            self.reset_parameter(param_name)

        # Handle nested managers once at the end
        if self.dataclass_type and self.nested_managers:
            current_config = getattr(self, '_current_config_instance', None)
            if current_config:
                self.service.reset_nested_managers(self.nested_managers, self.dataclass_type, current_config)



    def update_parameter(self, param_name: str, value: Any) -> None:
        """Update parameter value using shared service layer."""

        if param_name in self.parameters:
            # Convert value using service layer
            converted_value = self.service.convert_value_to_type(value, self.parameter_types.get(param_name, type(value)), param_name, self.dataclass_type)

            # Update parameter in data model
            self.parameters[param_name] = converted_value

            # CRITICAL FIX: Track that user explicitly set this field
            # This prevents placeholder updates from destroying user values
            self._user_set_fields.add(param_name)

            # Update corresponding widget if it exists
            if param_name in self.widgets:
                self.update_widget_value(self.widgets[param_name], converted_value)

            # Emit signal for PyQt6 compatibility
            self.parameter_changed.emit(param_name, converted_value)

    def _is_function_parameter(self, param_name: str) -> bool:
        """
        Detect if parameter is a function parameter vs dataclass field.

        Function parameters should not be reset against dataclass types.
        This prevents the critical bug where step editor tries to reset
        function parameters like 'group_by' against GlobalPipelineConfig.
        """
        if not self.function_target or not self.dataclass_type:
            return False

        # Check if parameter exists in dataclass fields
        try:
            import dataclasses
            if dataclasses.is_dataclass(self.dataclass_type):
                field_names = {field.name for field in dataclasses.fields(self.dataclass_type)}
                # If parameter is NOT in dataclass fields, it's a function parameter
                return param_name not in field_names
        except Exception:
            # If we can't determine, assume it's a function parameter to be safe
            return True

        return False

    def reset_parameter(self, param_name: str, default_value: Any = None) -> None:
        """Reset parameter with streamlined logic."""
        if param_name not in self.parameters:
            return

        # CRITICAL FIX: Set updated context at the very beginning of reset process
        # This ensures all lazy resolutions during reset use current form values
        from openhcs.core.context.global_config import set_current_global_config, get_current_global_config
        from openhcs.core.config import GlobalPipelineConfig

        updated_context = self._build_context_from_current_form_values()
        original_context = get_current_global_config(GlobalPipelineConfig)

        try:
            if updated_context:
                set_current_global_config(GlobalPipelineConfig, updated_context)

            # Resolve reset value using dispatch
            reset_value = default_value or self._get_reset_value(param_name)
            print(f"🔍 RESET DEBUG: {param_name} reset_value = {reset_value}, is_lazy_dataclass = {self.config.is_lazy_dataclass}")

            # Apply reset with functional operations
            self.parameters[param_name] = reset_value

            # Mathematical simplification: Simple reset logic
            # 1. Remove from user-set tracking
            if hasattr(self, '_user_set_fields'):
                self._user_set_fields.discard(param_name)

            # 2. Update widget value first
            if param_name in self.widgets:
                widget = self.widgets[param_name]
                self.update_widget_value(widget, reset_value, param_name)

            # 3. CRITICAL FIX: Apply placeholder using current form values, not saved context
            # This ensures the placeholder reflects the current form state after reset
            if reset_value is None and self.config.is_lazy_dataclass and param_name in self.widgets:
                widget = self.widgets[param_name]
                self._apply_placeholder_with_lazy_context(widget, param_name, reset_value)

            # 4. CRITICAL FIX: For nested forms, emit parameter change to trigger parent's sibling updates
            # This ensures that when a field is reset in a nested form, sibling forms see the updated inheritance
            # The parent form manager has access to all sibling managers and can trigger proper updates

            self.nested_managers.get(param_name) and hasattr(self.nested_managers[param_name], 'reset_all_parameters') and self.nested_managers[param_name].reset_all_parameters()
            self.parameter_changed.emit(param_name, reset_value)
        finally:
            # Restore original context after all parameter changes and lazy resolutions are complete
            if original_context:
                set_current_global_config(GlobalPipelineConfig, original_context)
                print(f"🔍 CONTEXT DEBUG: Restored original context in reset_parameter")

    def _get_reset_value(self, param_name: str) -> Any:
        """Get reset value using context dispatch."""
        if self.dataclass_type:
            reset_value = self.service.get_reset_value_for_parameter(
                param_name, self.parameter_types.get(param_name), self.dataclass_type, not self.config.is_lazy_dataclass)
            return reset_value
        else:
            # Function parameter reset: use param_defaults directly
            return self.param_defaults.get(param_name)



    def get_current_values(self) -> Dict[str, Any]:
        """
        Get current parameter values preserving lazy dataclass structure.

        This fixes the lazy default materialization override saving issue by ensuring
        that lazy dataclasses maintain their structure when values are retrieved.
        """
        # Start with a copy of current parameters
        current_values = self.parameters.copy()

        # Validate optional dataclass checkbox states
        self._validate_optional_dataclass_checkbox_states(current_values)

        # Collect values from nested managers, respecting optional dataclass checkbox states
        self._apply_to_nested_managers(
            lambda name, manager: self._process_nested_values_if_checkbox_enabled(
                name, manager, current_values
            )
        )

        # Lazy dataclasses are now handled by LazyDataclassEditor, so no structure preservation needed
        return current_values

    def _get_optional_checkbox_state(self, param_name: str) -> Optional[bool]:
        """Get checkbox state for optional dataclass parameter."""
        param_type = self.parameter_types.get(param_name)
        if not (param_type and self.service._type_utils.is_optional_dataclass(param_type)):
            return None

        widget = self.widgets.get(param_name)
        checkbox = self._find_checkbox_in_container(widget) if widget else None
        return checkbox.isChecked() if checkbox else None

    def _validate_optional_dataclass_checkbox_states(self, current_values: Dict[str, Any]) -> None:
        """Update parameter values based on checkbox states."""
        for param_name in self.widgets.keys():
            checkbox_state = self._get_optional_checkbox_state(param_name)
            if checkbox_state is True and current_values[param_name] is None:
                # Check if we have a stored step-level config
                if hasattr(self, '_step_level_config_values') and param_name in self._step_level_config_values:
                    # Use stored step-level config
                    current_values[param_name] = self._step_level_config_values[param_name]
                elif hasattr(self, 'param_defaults') and param_name in self.param_defaults:
                    # Step editor provides step-level configs in param_defaults
                    current_values[param_name] = self.param_defaults[param_name]
                else:
                    # Standard behavior: create default instance
                    param_type = self.parameter_types[param_name]
                    inner_type = self.service._type_utils.get_optional_inner_type(param_type)
                    current_values[param_name] = inner_type()
            elif checkbox_state is False:
                # Clear value when checkbox is unchecked
                current_values[param_name] = None

    def _handle_nested_parameter_change(self, parent_name: str, value: Any) -> None:
        """Handle nested parameter changes by reconstructing the entire dataclass."""
        print(f"🔍 DEBUG: _handle_nested_parameter_change called for '{parent_name}' with value: {value}")

        if self._get_optional_checkbox_state(parent_name) is not False:
            # Reconstruct the entire dataclass from current nested values
            nested_manager = self.nested_managers.get(parent_name)
            print(f"🔍 DEBUG: Found nested manager for '{parent_name}': {nested_manager is not None}")

            if nested_manager:
                nested_values = nested_manager.get_current_values()
                print(f"🔍 DEBUG: Nested values: {nested_values}")

                nested_type = self.parameter_types.get(parent_name)
                if nested_type:
                    if self.service._type_utils.is_optional_dataclass(nested_type):
                        nested_type = self.service._type_utils.get_optional_inner_type(nested_type)

                    reconstructed_instance = self._rebuild_nested_dataclass_instance(nested_values, nested_type, parent_name)
                    print(f"🔍 DEBUG: Reconstructed instance: {reconstructed_instance}")

                    # Update sibling placeholders with updated context directly
                    print(f"🔍 DEBUG: Calling _update_sibling_placeholders_with_updated_context")
                    # CRITICAL FIX: Pass the nested manager's dataclass type, not the parent's type
                    nested_dataclass_type = nested_manager.dataclass_type if nested_manager else nested_type
                    # CRITICAL FIX: Exclude the manager that was just modified to preserve its concrete input
                    self._update_sibling_placeholders_with_updated_context(parent_name, reconstructed_instance, nested_dataclass_type, exclude_manager=parent_name)

                    self.parameter_changed.emit(parent_name, reconstructed_instance)

    def _update_sibling_placeholders_with_updated_context(self, changed_field_name: str, new_value: Any, changed_dataclass_type: type = None, exclude_manager: str = None) -> None:
        """Update sibling manager placeholders with the updated context directly.

        Args:
            changed_field_name: Name of the field that was changed
            new_value: New value of the field
            changed_dataclass_type: Type of the dataclass that was changed
            exclude_manager: Name of the manager to exclude from updates (the one that was just modified)
        """
        from openhcs.core.context.global_config import get_current_global_config
        from openhcs.core.config import GlobalPipelineConfig
        from dataclasses import replace

        print(f"🔍 DEBUG: Updating sibling placeholders for field '{changed_field_name}' with value: {new_value}")

        # CRITICAL FIX: Get context with current form values instead of saved thread-local context
        # This ensures sibling updates use current unsaved values (like "23") not saved values (like "1")
        current_context = self._build_context_from_current_form_values()

        # DEBUG: Show what context we built
        print(f"🔍 CONTEXT BUILD DEBUG: Built context for sibling updates:")
        if current_context and hasattr(current_context, 'step_well_filter_config'):
            step_config = current_context.step_well_filter_config
            print(f"  step_well_filter_config.well_filter = '{step_config.well_filter}'")

        print(f"🔍 DEBUG: step_well_filter_config type: {type(getattr(current_context, 'step_well_filter_config', None))}")
        print(f"🔍 DEBUG: step_materialization_config type: {type(getattr(current_context, 'step_materialization_config', None))}")

        if current_context:
            # Create updated context with the new value
            updated_context = replace(current_context, **{changed_field_name: new_value})
            print(f"🔍 DEBUG: Created updated context with {changed_field_name} = {new_value}")

            # PYTHON INHERITANCE APPROACH: Check inheritance relationships using Python's type system
            print(f"🔍 DEBUG: Checking {len(self.nested_managers)} sibling managers for inheritance relationships")

            # CRITICAL FIX: Use the passed dataclass type (from nested manager) instead of parent's type
            if changed_dataclass_type is None:
                # Fallback to self.dataclass_type for backward compatibility
                changed_dataclass_type = self.dataclass_type

            if not changed_dataclass_type:
                print(f"🔍 DEBUG: Could not determine changed dataclass type")
                return

            print(f"🔍 DEBUG: Changed dataclass type: {changed_dataclass_type.__name__} (from nested manager)")

            # CRITICAL DEBUG: List all managers to see if streaming configs are present
            all_manager_names = list(self.nested_managers.keys())
            print(f"🔍 DEBUG: All managers: {all_manager_names}")

            for manager_name, manager in self.nested_managers.items():
                # CRITICAL FIX: Skip the manager that was just modified to preserve its concrete input
                if exclude_manager and manager_name == exclude_manager:
                    print(f"🔍 DEBUG: Skipping manager '{manager_name}' (was just modified - preserving concrete input)")
                    continue

                manager_dataclass_type = getattr(manager, 'dataclass_type', None)
                if manager_dataclass_type is None:
                    print(f"🔍 DEBUG: Skipping manager '{manager_name}' (no dataclass_type)")
                    continue

                print(f"🔍 DEBUG: Checking manager '{manager_name}' ({manager_dataclass_type.__name__})")

                # Check if this manager has any None fields that inherit from the changed dataclass
                has_affected_fields = self._manager_has_inheritance_from_dataclass(manager, changed_dataclass_type)

                if has_affected_fields:
                    print(f"🔍 DEBUG: Manager '{manager_name}' has inheritance from {changed_dataclass_type.__name__} - refreshing")
                    # Track which dataclass triggered this inheritance update for rightmost parent logic
                    manager._last_changed_dataclass_name = changed_dataclass_type.__name__
                    manager.refresh_placeholder_text_with_context(updated_context, changed_dataclass_type)
                else:
                    # REDUCED DEBUG: Only show streaming configs to reduce output
                    if 'streaming' in manager_name:
                        print(f"🔍 DEBUG: *** STREAMING *** Manager '{manager_name}' has no inheritance from {changed_dataclass_type.__name__} - skipping")
                    # Skip debug for other managers to prevent BrokenPipeError
        else:
            print(f"🔍 DEBUG: No current context found - cannot update sibling inheritance")

    def _manager_has_inheritance_from_dataclass(self, manager, changed_dataclass_type: type) -> bool:
        """Check if manager has fields that should inherit from changed dataclass."""
        # Check each field to see if it should inherit from the changed dataclass
        for param_name, current_value in manager.parameters.items():
            # Simple rule: Only None values that are NOT user-set can inherit
            is_user_set = hasattr(manager, '_user_set_fields') and param_name in manager._user_set_fields

            if current_value is None and not is_user_set:
                # Use the simplified field inheritance check
                if self._should_allow_inheritance(manager.dataclass_type, param_name, changed_dataclass_type):
                    return True
        return False

    def _should_allow_inheritance(self, target_dataclass_type: type, field_name: str, source_dataclass_type: type) -> bool:
        """RADICAL SIMPLIFICATION: Use Python's MRO directly like super() would."""
        from dataclasses import fields, is_dataclass
        import dataclasses

        if not (is_dataclass(target_dataclass_type) and is_dataclass(source_dataclass_type)):
            return False

        # Get base classes (unwrap lazy classes)
        target_base = target_dataclass_type.__bases__[0] if target_dataclass_type.__bases__ else target_dataclass_type
        source_base = source_dataclass_type.__bases__[0] if source_dataclass_type.__bases__ else source_dataclass_type

        # CRITICAL FIX: For lazy dataclasses, check the actual instance value, not static defaults
        # This is because inherit_as_none configs have static defaults but None instance values
        if hasattr(self, 'parameters') and field_name in self.parameters:
            current_instance_value = self.parameters[field_name]
            # If the current instance has a concrete value (not None), it doesn't inherit
            if current_instance_value is not None:
                return False
        else:
            # Fallback to static field check for non-lazy dataclasses
            if field_name in target_base.__annotations__:
                target_fields = {f.name: f for f in fields(target_base)}
                if field_name in target_fields:
                    target_field = target_fields[field_name]
                    target_default = target_field.default if target_field.default is not dataclasses.MISSING else None

                    # If target has its own concrete value, it doesn't inherit
                    if target_default is not None:
                        return False

        # Use MRO to find next appropriate parent for inheritance
        return self._is_next_in_mro_with_field(target_base, source_base, field_name)

    def _is_next_in_mro_with_field(self, target_class: type, source_class: type, field_name: str) -> bool:
        """Check if source_class is the next class in target's MRO that should provide the field value.

        FIELD-SPECIFIC LOGIC:
        - Skip None values only if there's a concrete value later in MRO
        - If no concrete value exists, inherit the None value from the first class that defines it
        """
        from dataclasses import fields, is_dataclass
        import dataclasses

        # First pass: Check if there's ANY concrete value in the MRO
        has_concrete_value = False
        for mro_class in target_class.__mro__[1:]:
            if is_dataclass(mro_class):
                mro_fields = {f.name: f for f in fields(mro_class)}
                if field_name in mro_fields:
                    field_obj = mro_fields[field_name]
                    field_default = field_obj.default if field_obj.default is not dataclasses.MISSING else None
                    if field_default is not None:
                        has_concrete_value = True
                        break

        # Second pass: Find the appropriate class to inherit from
        for mro_class in target_class.__mro__[1:]:  # Skip self
            if is_dataclass(mro_class):
                mro_fields = {f.name: f for f in fields(mro_class)}
                if field_name in mro_fields:
                    field_obj = mro_fields[field_name]
                    field_default = field_obj.default if field_obj.default is not dataclasses.MISSING else None

                    if has_concrete_value:
                        # Skip None values when concrete value exists later
                        if field_default is not None:
                            return mro_class == source_class
                    else:
                        # No concrete value exists - inherit from first class that defines it
                        return mro_class == source_class

        return False





    def _get_config_name_for_class(self, dataclass_type: type) -> str:
        """Get the config field name for a dataclass type using dynamic naming."""
        from openhcs.core.lazy_config import _camel_to_snake

        # Use the same naming convention as the dynamic field injection system
        return _camel_to_snake(dataclass_type.__name__)



    def _find_most_specific_intermediate_source(self, rightmost_definer: type, ultimate_source: type, field_name: str) -> type:
        """
        Find the most specific intermediate source between rightmost definer and ultimate source.

        For example, if StreamingConfig inherits from StepWellFilterConfig, and StepWellFilterConfig
        inherits from WellFilterConfig, then when checking inheritance from WellFilterConfig,
        we should find StepWellFilterConfig as the more specific intermediate source.

        Args:
            rightmost_definer: The rightmost parent that defines the field (e.g., StreamingConfig)
            ultimate_source: The ultimate source being checked (e.g., WellFilterConfig)
            field_name: The field name being checked

        Returns:
            The most specific intermediate source, or None if no intermediate source exists
        """
        from dataclasses import fields, is_dataclass

        if not issubclass(rightmost_definer, ultimate_source):
            return None

        # Walk up the MRO from rightmost_definer to ultimate_source
        # Find the most specific class that defines the field and is between them
        most_specific_intermediate = None

        for cls in rightmost_definer.__mro__[1:]:  # Skip rightmost_definer itself
            if cls == ultimate_source:
                # Reached ultimate source, stop searching
                break

            if is_dataclass(cls):
                cls_fields = {f.name: f for f in fields(cls)}
                if field_name in cls_fields:
                    # This class defines the field and is between rightmost_definer and ultimate_source
                    if most_specific_intermediate is None or issubclass(cls, most_specific_intermediate):
                        most_specific_intermediate = cls

        return most_specific_intermediate





    def _process_nested_values_if_checkbox_enabled(self, param_name: str, manager: Any,
                                                 current_values: Dict[str, Any]) -> None:
        """Process nested values only if checkbox is enabled."""
        if self._get_optional_checkbox_state(param_name) is not False:
            self._process_nested_values(param_name, manager.get_current_values(), current_values)



    def _find_checkbox_in_container(self, container: QWidget) -> Optional['QCheckBox']:
        """Find the checkbox widget within an optional dataclass container."""
        from PyQt6.QtWidgets import QCheckBox

        # Check if the container itself is a checkbox
        if isinstance(container, QCheckBox):
            return container

        # Search for checkbox in container's children
        for child in container.findChildren(QCheckBox):
            return child  # Return the first checkbox found

        return None


    def refresh_placeholder_text(self) -> None:
        """
        Refresh placeholder text for all widgets to reflect current GlobalPipelineConfig.

        This method should be called when the GlobalPipelineConfig changes to ensure
        that lazy dataclass forms show updated placeholder text.

        CRITICAL FIX: Now includes inheritance-aware placeholder updates for all fields.
        """
        # Only refresh for lazy dataclasses (PipelineConfig forms)
        if not self.dataclass_type:
            return

        is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(self.dataclass_type)

        if not is_lazy_dataclass:
            return

        print(f"🔍 DEBUG: refresh_placeholder_text for {self.dataclass_type.__name__}")
        print(f"🔍 DEBUG: Current parameters: {self.parameters}")

        # Get current context for inheritance-aware placeholder updates
        from openhcs.core.context.global_config import get_current_global_config
        from openhcs.core.config import GlobalPipelineConfig

        current_context = get_current_global_config(GlobalPipelineConfig)
        print(f"🔍 DEBUG: Current thread-local context for placeholder resolution: {current_context}")
        if hasattr(current_context, 'step_well_filter_config'):
            print(f"🔍 DEBUG: step_well_filter_config in context: {current_context.step_well_filter_config}")

        # CRITICAL FIX: Use inheritance-aware placeholder refresh for ALL fields
        # This ensures inheritance works on window open and reset, not just on field changes
        self.refresh_placeholder_text_with_context(current_context)

        # Recursively refresh nested managers
        self._apply_to_nested_managers(lambda name, manager: manager.refresh_placeholder_text())

    def refresh_placeholder_text_with_context(self, updated_context: Any, changed_dataclass_type: type = None) -> None:
        """
        Refresh placeholder text using a specific context instead of thread-local context.

        This is used for sibling inheritance where we want to show placeholders
        based on an updated context that hasn't been committed to thread-local yet.

        Args:
            updated_context: The updated context to use for placeholder resolution
            changed_dataclass_type: The dataclass type that triggered this update (for inheritance checking)
        """
        # Only refresh for lazy dataclasses
        if not self.dataclass_type:
            return

        is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(self.dataclass_type)
        if not is_lazy_dataclass:
            return

        print(f"🔍 DEBUG: refresh_placeholder_text_with_context for {self.dataclass_type.__name__}")
        print(f"🔍 DEBUG: Using updated context: {updated_context}")

        # Mathematical simplification: Simple rule - only update placeholders for None values that aren't user-set
        for param_name, widget in self.widgets.items():
            current_value = self.parameters.get(param_name)
            is_user_set = hasattr(self, '_user_set_fields') and param_name in self._user_set_fields

            # CRITICAL FIX: Only refresh placeholders if field value is None AND not user-set
            if current_value is not None or is_user_set:
                continue

            # Simple inheritance check: only update if inheritance is allowed
            if changed_dataclass_type and not self._should_allow_inheritance(self.dataclass_type, param_name, changed_dataclass_type):
                continue

            # Get updated placeholder and apply it
            updated_placeholder = LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                self.dataclass_type, param_name,
                app_config=updated_context,
                placeholder_prefix=self.placeholder_prefix
            )

            if updated_placeholder:
                # CRITICAL FIX: Only update placeholder text, NEVER modify field values
                # Field values are sacred and reserved for explicit user input only

                # Update the widget placeholder to show the inherited value
                widget.blockSignals(True)
                try:
                    # Apply the updated placeholder text
                    if hasattr(widget, 'setPlaceholderText'):
                        widget.setPlaceholderText(updated_placeholder)

                    # Apply placeholder using PyQt6WidgetEnhancer for visual styling
                    PyQt6WidgetEnhancer.apply_placeholder_text(widget, updated_placeholder)
                finally:
                    widget.blockSignals(False)
            else:
                print(f"🔍 DEBUG: No inheritance relationship for '{param_name}' (placeholder unchanged)")

    def _rebuild_nested_dataclass_instance(self, nested_values: Dict[str, Any],
                                         nested_type: Type, param_name: str) -> Any:
        """
        Rebuild nested dataclass instance from current values.

        This method handles both lazy and non-lazy dataclasses by checking the nested_type
        itself rather than the parent dataclass type.

        Args:
            nested_values: Current values from nested manager
            nested_type: The dataclass type to create
            param_name: Parameter name for context

        Returns:
            Reconstructed dataclass instance
        """
        # Check if the nested type itself is a lazy dataclass
        # This is the correct check - we need to examine the nested type, not the parent
        nested_type_is_lazy = LazyDefaultPlaceholderService.has_lazy_resolution(nested_type)

        # CRITICAL FIX: Filter out None values that match field defaults for both lazy and non-lazy
        # This prevents explicit None values from appearing in config output
        from dataclasses import fields
        import dataclasses

        # Get field defaults for this dataclass
        field_defaults = {}
        for field in fields(nested_type):
            if field.default is not dataclasses.MISSING:
                field_defaults[field.name] = field.default
            elif field.default_factory is not dataclasses.MISSING:
                field_defaults[field.name] = None  # default_factory fields default to None
            else:
                field_defaults[field.name] = None  # required fields default to None

        # Filter out values that match their field defaults
        filtered_values = {}
        for k, v in nested_values.items():
            field_default = field_defaults.get(k, None)
            # Only include if value differs from field default
            if v != field_default:
                filtered_values[k] = v

        # CRITICAL FIX: For lazy dataclasses, always use updated context during construction
        # This ensures lazy field resolution uses current form values, not saved values
        if nested_type_is_lazy:
            print(f"🔍 CONTEXT DEBUG: Setting updated context for lazy construction of {nested_type.__name__}")
            # Get current context with form values for lazy resolution
            updated_context = self._build_context_from_current_form_values()
            if updated_context:
                from openhcs.core.context.global_config import set_current_global_config, get_current_global_config
                from openhcs.core.config import GlobalPipelineConfig

                original_context = get_current_global_config(GlobalPipelineConfig)
                # CRITICAL FIX: Don't restore context immediately - let it stay active
                # The issue is that lazy resolution happens AFTER construction, so we need
                # the context to remain active until the field is actually accessed
                set_current_global_config(GlobalPipelineConfig, updated_context)
                print(f"🔍 CONTEXT DEBUG: Set context with step_well_filter_config.well_filter = '{updated_context.step_well_filter_config.well_filter}' - NOT RESTORING YET")

                # Construct with updated context for lazy resolution
                if filtered_values:
                    result = nested_type(**filtered_values)
                else:
                    result = nested_type()

                print(f"🔍 CONTEXT DEBUG: Constructed {result} - context still active")

                # DON'T restore context here - let it stay active for lazy resolution
                # The context will be restored later or by the caller

                return result

        # Non-lazy fallback: construct normally
        if filtered_values:
            return nested_type(**filtered_values)
        else:
            return nested_type()

    def _apply_to_nested_managers(self, operation_func: callable) -> None:
        """Apply operation to all nested managers."""
        for param_name, nested_manager in self.nested_managers.items():
            operation_func(param_name, nested_manager)

    def _process_nested_values(self, param_name: str, nested_values: Dict[str, Any], current_values: Dict[str, Any]) -> None:
        """Process nested values and rebuild dataclass instance."""
        nested_type = self.parameter_types.get(param_name)
        if nested_type and nested_values:
            if self.service._type_utils.is_optional_dataclass(nested_type):
                nested_type = self.service._type_utils.get_optional_inner_type(nested_type)
            rebuilt_instance = self._rebuild_nested_dataclass_instance(nested_values, nested_type, param_name)
            current_values[param_name] = rebuilt_instance