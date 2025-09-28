"""
Dramatically simplified PyQt parameter form manager.

This demonstrates how the widget implementation can be drastically simplified
by leveraging the comprehensive shared infrastructure we've built.
"""

import dataclasses
import logging
from typing import Any, Dict, Type, Optional, Callable
from dataclasses import replace
from PyQt6.QtWidgets import QWidget, QVBoxLayout, QHBoxLayout, QScrollArea, QLabel, QPushButton, QLineEdit, QCheckBox, QComboBox
from PyQt6.QtCore import Qt, pyqtSignal

# SIMPLIFIED: Removed thread-local imports - dual-axis resolver handles context automatically
from openhcs.core.config import GlobalPipelineConfig

# Mathematical simplification: Shared dispatch tables to eliminate duplication
WIDGET_UPDATE_DISPATCH = [
    (QComboBox, 'update_combo_box'),
    ('get_selected_values', 'update_checkbox_group'),
    ('setChecked', lambda w, v: w.setChecked(bool(v))),
    ('setValue', lambda w, v: w.setValue(v if v is not None else w.minimum())),  # CRITICAL FIX: Set to minimum for None values to enable placeholder
    ('set_value', lambda w, v: w.set_value(v)),
    ('setText', lambda w, v: v is not None and w.setText(str(v)) or (v is None and w.clear())),  # CRITICAL FIX: Handle None values by clearing
    # REMOVED: ('clear', lambda w, v: v is None and w.clear()) - Redundant with setText fix above
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
from .layout_constants import CURRENT_LAYOUT

# Import OpenHCS core components
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
# Old field path detection removed - using simple field name matching
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


class NoneAwareIntEdit(QLineEdit):
    """QLineEdit that only allows digits and properly handles None values for integer fields."""

    def __init__(self, parent=None):
        super().__init__(parent)
        # Set up input validation to only allow digits
        from PyQt6.QtGui import QIntValidator
        self.setValidator(QIntValidator())

    def get_value(self):
        """Get value, returning None for empty text or converting to int."""
        text = self.text().strip()
        if text == "":
            return None
        try:
            return int(text)
        except ValueError:
            return None

    def set_value(self, value):
        """Set value, handling None properly."""
        if value is None:
            self.setText("")
        else:
            self.setText(str(value))


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
                 field_id: str, dataclass_type: Type,
                 parameter_info: Dict = None, parent=None,
                 use_scroll_area: bool = True, function_target=None,
                 color_scheme: Optional[PyQt6ColorScheme] = None, placeholder_prefix: str = None,
                 param_defaults: Dict[str, Any] = None, global_config_type: Optional[Type] = None,
                 context_event_coordinator=None, orchestrator=None, is_concrete_instance: bool = None):
        """
        Initialize PyQt parameter form manager with dual-axis resolution.

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

        # SIMPLIFIED: Dual-axis resolver handles context discovery automatically via stack introspection
        # No need for manual context provider management

        # Store configuration parameters - dataclass_type is the single source of truth
        # Note: parent is already set by QWidget.__init__(parent), don't override it
        self.dataclass_type = dataclass_type
        self.global_config_type = global_config_type  # Store for nested manager inheritance
        self.placeholder_prefix = placeholder_prefix or CONSTANTS.DEFAULT_PLACEHOLDER_PREFIX
        self.orchestrator = orchestrator  # Store orchestrator for compiler-grade placeholder resolution

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
        config.global_config_type = global_config_type
        config.placeholder_prefix = placeholder_prefix

        # CRITICAL FIX: Determine editing mode based on context hierarchy
        if is_concrete_instance is not None:
            # Explicit instance-based detection: Use the passed parameter directly
            config.is_lazy_dataclass = not is_concrete_instance
            config.is_global_config_editing = is_concrete_instance
        elif global_config_type is not None:
            # Check if we're editing the global config type directly OR if parent is in global editing mode
            if dataclass_type == global_config_type:
                # Direct global config editing
                config.is_global_config_editing = True
                config.is_lazy_dataclass = False
            elif parent and hasattr(parent, 'config') and parent.config.is_global_config_editing:
                # Inherit global editing mode from parent (nested dataclass in global config)
                config.is_global_config_editing = True
                config.is_lazy_dataclass = False
            else:
                # Regular lazy dataclass editing
                config.is_global_config_editing = False
                config.is_lazy_dataclass = True
        else:
            # Auto-detection mode: Use lazy resolution check (backward compatibility)
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
        self.reset_fields = set()  # Track fields that have been explicitly reset to show inheritance

        # CRITICAL FIX: Track which fields have been explicitly set by users
        # This prevents placeholder updates from destroying user values
        self._user_set_fields: set = set()

        # SHARED RESET STATE: Track reset fields across all nested managers within this form
        # This enables coordination between nested managers for inheritance resolution
        if hasattr(parent, 'shared_reset_fields'):
            # Nested manager: use parent's shared reset state
            self.shared_reset_fields = parent.shared_reset_fields
        else:
            # Root manager: create new shared reset state
            self.shared_reset_fields = set()

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
        self._widget_creator = create_pyqt6_registry()


        # ContextEventCoordinator removed - new context system handles updates automatically
        self._context_event_coordinator = None

        # Set up UI
        self.setup_ui()

        # NOTE: Placeholder refresh moved to from_dataclass_instance after user-set detection

    def create_widget(self, param_name: str, param_type: Type, current_value: Any,
                     widget_id: str, parameter_info: Any = None) -> Any:
        """Create widget using the registry creator function."""
        print(f"🔍 WIDGET CREATE: Creating {param_name} (type={param_type}, value={current_value})")
        widget = self._widget_creator(param_name, param_type, current_value, widget_id, parameter_info)
        print(f"🔍 WIDGET CREATE: Result = {widget} (type={type(widget)})")

        if widget is None:
            print(f"🔍 WIDGET CREATE: ERROR - Widget is None! Creating fallback...")
            from PyQt6.QtWidgets import QLabel
            widget = QLabel(f"ERROR: Widget creation failed for {param_name}")

        return widget

    def _get_placeholder_text(self, param_name: str) -> Optional[str]:
        """Get placeholder text using simplified contextvars system."""
        if self.config.is_lazy_dataclass:
            from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

            # Use simplified placeholder service with stored orchestrator context
            return LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
                self.dataclass_type,
                param_name,
                placeholder_prefix=self.placeholder_prefix,
                context_obj=self.orchestrator  # Use stored orchestrator for context
            )
        return None





    @classmethod
    def _should_field_show_as_placeholder(cls, dataclass_instance: Any, field_name: str, raw_value: Any) -> bool:
        """Check if field should show as placeholder (inherited) vs concrete (explicitly set)."""
        # If explicitly set, show concrete value
        if field_name in getattr(dataclass_instance, '_explicitly_set_fields', set()):
            return False

        # CRITICAL FIX: If raw_value is None, always show as placeholder
        # None values in lazy dataclasses should inherit from parent configs
        if raw_value is None:
            return True

        # If matches global config value, show as placeholder
        global_config_type = getattr(dataclass_instance, '_global_config_type', None)
        if global_config_type:
            global_config = get_current_global_config(global_config_type)
            if global_config and hasattr(global_config, field_name):
                return raw_value == getattr(global_config, field_name)

        return False

    def _get_placeholder_text_with_context(self, param_name: str, temporary_context: Any) -> Optional[str]:
        """Get placeholder text using a specific temporary context for live updates."""
        if not self.config.is_lazy_dataclass:
            return None

        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

        # Use simplified placeholder service with explicit context
        return LazyDefaultPlaceholderService.get_lazy_resolved_placeholder(
            self.dataclass_type,
            param_name,
            placeholder_prefix=self.placeholder_prefix,
            context_obj=temporary_context
        )

    @classmethod
    def from_dataclass_instance(cls, dataclass_instance: Any, field_id: str,
                              placeholder_prefix: str = "Default",
                              parent=None, use_scroll_area: bool = True,
                              function_target=None, color_scheme=None,
                              force_show_all_fields: bool = False,
                              global_config_type: Optional[Type] = None,
                              context_event_coordinator=None, orchestrator=None):
        """
        Create ParameterFormManager for editing entire dataclass instance.

        Args:
            dataclass_instance: The dataclass instance to edit
            field_id: Unique identifier for the form
            placeholder_prefix: Prefix for placeholder text
            parent: Parent widget
            use_scroll_area: Whether to use scroll area
            function_target: Optional function target
            color_scheme: Optional color scheme
            force_show_all_fields: Whether to show all fields
            global_config_type: Optional global config type

        Returns:
            ParameterFormManager configured for dataclass editing
        """
        # SIMPLIFIED: Dual-axis resolver handles context discovery automatically
        from dataclasses import fields, is_dataclass

        if not is_dataclass(dataclass_instance):
            raise ValueError(f"{type(dataclass_instance)} is not a dataclass")

        # Mathematical simplification: Unified parameter extraction for both lazy and regular dataclasses
        is_lazy_instance = hasattr(dataclass_instance, '_resolve_field_value')
        is_concrete_instance = not is_lazy_instance
        parameters = {}
        parameter_types = {}

        # CRITICAL FIX: Get dataclass type BEFORE the loop, not inside it
        dataclass_type = type(dataclass_instance)

        # CRITICAL FIX: Extract raw values and preserve None for placeholder display
        # For lazy dataclasses, check if values match global config inheritance
        is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type)

        for field_obj in fields(dataclass_instance):
            # CRITICAL FIX: Always use object.__getattribute__ to get raw values (not resolved values)
            # This is essential for both lazy and non-lazy dataclasses to preserve None for placeholder display
            raw_value = object.__getattribute__(dataclass_instance, field_obj.name)

            # CRITICAL FIX: For lazy dataclasses, check if field was explicitly set vs inherited
            # Use existing infrastructure to determine if field should show as placeholder
            if is_lazy_dataclass and raw_value is not None:
                should_show_as_placeholder = cls._should_field_show_as_placeholder(
                    dataclass_instance, field_obj.name, raw_value
                )
                if should_show_as_placeholder:
                    raw_value = None

            # For inherited fields (raw_value is None), keep as None to trigger placeholders
            # For user-set fields (raw_value is not None), use the raw value
            parameters[field_obj.name] = raw_value
            parameter_types[field_obj.name] = field_obj.type

        # SIMPLIFIED: Create ParameterFormManager using dual-axis resolution
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
            placeholder_prefix=placeholder_prefix,
            param_defaults=None,
            global_config_type=global_config_type,  # CRITICAL FIX: Pass global_config_type through
            context_event_coordinator=context_event_coordinator,  # CRITICAL FIX: Pass orchestrator-specific coordinator
            orchestrator=orchestrator,  # CRITICAL FIX: Pass orchestrator for compiler-grade placeholder resolution
            is_concrete_instance=is_concrete_instance  # CRITICAL FIX: Pass instance type for correct reset behavior
        )

        # Store the original dataclass instance for reset operations
        form_manager._current_config_instance = dataclass_instance

        # CRITICAL FIX: Check which parameters were explicitly set for ALL dataclasses
        # This uses the extracted parameters that were already processed during form creation
        dataclass_type_name = type(dataclass_instance).__name__
        is_lazy = hasattr(dataclass_instance, '_is_lazy_dataclass') or 'Lazy' in dataclass_type_name

        print(f"🔍 USER-SET DETECTION: Checking {dataclass_type_name}, is_lazy={is_lazy}")

        # Apply user-set detection to BOTH lazy and non-lazy dataclasses
        print(f"🔍 USER-SET DETECTION: Starting detection for {dataclass_type_name}")

        # CORRECT APPROACH: Check the extracted parameters (which contain raw values)
        # These were extracted using object.__getattribute__ during form creation
        for field_name, raw_value in parameters.items():
            # Get resolved value for logging (this may trigger resolution)
            resolved_value = getattr(dataclass_instance, field_name)

            # SIMPLE RULE: Raw non-None = user-set, Raw None = inherited
            if raw_value is not None:
                form_manager._user_set_fields.add(field_name)
                print(f"🔍 USER-SET DETECTION: {field_name} raw={raw_value} resolved={resolved_value} -> marked as user-set")
            else:
                print(f"🔍 USER-SET DETECTION: {field_name} raw={raw_value} resolved={resolved_value} -> not user-set")

        print(f"🔍 USER-SET DETECTION: Final user_set_fields = {form_manager._user_set_fields}")

        # CRITICAL FIX: Refresh placeholders AFTER user-set detection to show correct concrete/placeholder state
        form_manager._refresh_all_placeholders_with_current_context()

        # CRITICAL FIX: Ensure nested managers also get their placeholders refreshed after full hierarchy is built
        # This fixes the issue where nested dataclass placeholders don't load properly on initial form creation
        form_manager._apply_to_nested_managers(lambda name, manager: manager.refresh_placeholder_text())

        return form_manager



    def setup_ui(self):
        """Set up the UI layout."""
        layout = QVBoxLayout(self)
        # Apply configurable layout settings
        layout.setSpacing(CURRENT_LAYOUT.main_layout_spacing)
        layout.setContentsMargins(*CURRENT_LAYOUT.main_layout_margins)

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
        # Apply configurable content layout settings
        content_layout.setSpacing(CURRENT_LAYOUT.content_layout_spacing)
        content_layout.setContentsMargins(*CURRENT_LAYOUT.content_layout_margins)

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

        # Direct field ID generation - no artificial complexity
        field_ids = self.service.generate_field_ids_direct(self.config.field_id, param_info.name)

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
        # Apply configurable parameter row layout settings
        layout.setSpacing(CURRENT_LAYOUT.parameter_row_spacing)
        layout.setContentsMargins(*CURRENT_LAYOUT.parameter_row_margins)

        # ENHANCEMENT: Extract field documentation dynamically if description is missing
        # Now uses caching and lazy dataclass resolution for better performance
        description = display_info['description']
        if not description or description.startswith("Parameter: "):
            from openhcs.textual_tui.widgets.shared.signature_analyzer import SignatureAnalyzer
            extracted_description = SignatureAnalyzer.extract_field_documentation(self.dataclass_type, param_info.name)
            if extracted_description:
                description = extracted_description

        label = LabelWithHelp(
            text=display_info['field_label'], param_name=param_info.name,
            param_description=description, param_type=param_info.type,
            color_scheme=self.config.color_scheme or PyQt6ColorScheme()
        )
        layout.addWidget(label)
        current_value = self.parameters.get(param_info.name)
        widget = self.create_widget(
            param_info.name, param_info.type, current_value,
            f"{self.field_id}_{param_info.name}",
            self.parameter_info.get(param_info.name)
        )
        # SIMPLIFIED: Use dual-axis resolution for placeholder text
        if current_value is None:
            placeholder_text = self._get_placeholder_text(param_info.name)
            if placeholder_text:
                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
        widget.setObjectName(field_ids['widget_id'])
        layout.addWidget(widget, 1)
        reset_button = QPushButton(CONSTANTS.RESET_BUTTON_TEXT)
        reset_button.setObjectName(field_ids['reset_button_id'])
        reset_button.setMaximumWidth(CURRENT_LAYOUT.reset_button_width)
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
            # Get actual field path from FieldPathDetector (no artificial "nested_" prefix)
            # For function parameters (no parent dataclass), use parameter name directly
            if self.dataclass_type is None:
                field_path = param_info.name
            else:
                field_path = self.service.get_field_path_with_fail_loud(self.dataclass_type, nested_type)

            # Mathematical simplification: Inline instance creation without helper method
            if current_value and not isinstance(current_value, nested_type):
                # Convert base to lazy instance via direct field mapping
                from dataclasses import fields
                try:
                    # CRITICAL FIX: Use object.__getattribute__ to get raw values and avoid triggering lazy resolution
                    if hasattr(current_value, '_resolve_field_value'):
                        # Source is lazy dataclass - get raw values to preserve None vs concrete distinction
                        field_values = {f.name: object.__getattribute__(current_value, f.name) for f in fields(current_value)}
                    else:
                        # Source is regular dataclass - use normal getattr
                        field_values = {f.name: getattr(current_value, f.name) for f in fields(current_value)}

                    # Create lazy instance using raw value approach to avoid triggering resolution
                    lazy_instance = object.__new__(nested_type)
                    for field_name, value in field_values.items():
                        object.__setattr__(lazy_instance, field_name, value)

                    # Initialize any required lazy dataclass attributes
                    if hasattr(nested_type, '_is_lazy_dataclass'):
                        object.__setattr__(lazy_instance, '_is_lazy_dataclass', True)
                except Exception:
                    lazy_instance = nested_type()
            else:
                lazy_instance = current_value or nested_type()

            nested_manager = ParameterFormManager.from_dataclass_instance(
                dataclass_instance=lazy_instance,
                field_id=field_path,  # Use actual dataclass field name directly
                placeholder_prefix=self.placeholder_prefix,
                parent=group_box, use_scroll_area=False,
                color_scheme=self.config.color_scheme,
                global_config_type=self.global_config_type,  # CRITICAL FIX: Pass global_config_type to nested managers
                context_event_coordinator=None,  # ContextEventCoordinator removed - new context system handles updates
                orchestrator=self.orchestrator  # CRITICAL FIX: Pass orchestrator for compiler-grade placeholder resolution
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
        # Apply configurable optional parameter layout settings
        layout.setSpacing(CURRENT_LAYOUT.optional_layout_spacing)
        layout.setContentsMargins(*CURRENT_LAYOUT.optional_layout_margins)

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
        """Create nested form - use actual field path instead of artificial field IDs"""
        # Get actual field path from FieldPathDetector (no artificial "nested_" prefix)
        # For function parameters (no parent dataclass), use parameter name directly
        if self.dataclass_type is None:
            field_path = param_name
        else:
            field_path = self.service.get_field_path_with_fail_loud(self.dataclass_type, param_type)

        # Extract nested parameters using service with parent context (handles both dataclass and non-dataclass contexts)
        nested_params, nested_types = self.service.extract_nested_parameters(
            current_value, param_type, self.dataclass_type
        )

        # CRITICAL FIX: Inherit editing mode from parent
        # If parent is in global config editing mode, nested managers should also be in global config editing mode
        is_concrete_instance = self.config.is_global_config_editing

        # Create nested manager with actual field path (no artificial field ID generation)
        nested_manager = ParameterFormManager(
            nested_params,
            nested_types,
            field_path,  # Use actual dataclass field name directly
            param_type,    # Use the actual nested dataclass type, not parent type
            None,  # parameter_info
            self,  # parent - CRITICAL FIX: Pass self as parent to share reset state
            False,  # use_scroll_area
            None,   # function_target
            PyQt6ColorScheme(),  # color_scheme
            self.placeholder_prefix, # Pass through placeholder prefix
            None,  # param_defaults
            self.global_config_type,  # CRITICAL FIX: Pass global_config_type to nested managers
            getattr(self, '_context_event_coordinator', None),  # CRITICAL FIX: Pass coordinator to nested forms
            self.orchestrator,  # CRITICAL FIX: Pass orchestrator for compiler-grade placeholder resolution
            is_concrete_instance  # CRITICAL FIX: Pass instance type for correct reset behavior
        )

        # Store nested manager
        self.nested_managers[param_name] = nested_manager

        return nested_manager



    def _apply_placeholder_with_lazy_context(self, widget: QWidget, param_name: str, current_value: Any, masked_fields: Optional[set] = None) -> None:
        """Apply placeholder using current form state, not saved thread-local state."""
        # Only apply placeholder if value is None
        if current_value is not None:
            return

        # SIMPLIFIED: Use dual-axis resolution for all placeholder text
        placeholder_text = self._get_placeholder_text(param_name)
        if placeholder_text:
            PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)










    def _refresh_all_placeholders_with_current_context(self) -> None:
        """Refresh all placeholders using simplified contextvars system."""
        if not self.config.is_lazy_dataclass:
            return

        # Apply placeholders using simplified system
        for param_name, widget in self.widgets.items():
            current_value = self.parameters.get(param_name)

            if current_value is None:
                # Use simplified placeholder resolution
                placeholder_text = self._get_placeholder_text(param_name)
                if placeholder_text:
                    PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
            else:
                # Clear placeholder state for non-None values
                PyQt6WidgetEnhancer._clear_placeholder_state(widget)

    def _refresh_all_placeholders_with_temporary_context(self, temporary_context: Any) -> None:
        """Refresh all placeholders - simplified to use regular placeholder resolution."""
        # Just use regular placeholder resolution - the simplified system doesn't need complex temporary contexts
        self._refresh_all_placeholders_with_current_context()

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



    def update_widget_value(self, widget: QWidget, value: Any, param_name: str = None, skip_context_behavior: bool = False, exclude_field: str = None) -> None:
        """Mathematical simplification: Unified widget update using shared dispatch."""
        self._execute_with_signal_blocking(widget, lambda: self._dispatch_widget_update(widget, value))

        # Only apply context behavior if not explicitly skipped (e.g., during reset operations)
        if not skip_context_behavior:
            self._apply_context_behavior(widget, value, param_name, exclude_field)

    def _dispatch_widget_update(self, widget: QWidget, value: Any) -> None:
        """Algebraic simplification: Single dispatch logic for all widget updates."""
        for matcher, updater in WIDGET_UPDATE_DISPATCH:
            if isinstance(widget, matcher) if isinstance(matcher, type) else hasattr(widget, matcher):
                if isinstance(updater, str):
                    getattr(self, f'_{updater}')(widget, value)
                else:
                    updater(widget, value)
                return

    def _clear_widget_to_default_state(self, widget: QWidget) -> None:
        """Clear widget to its default/empty state for reset operations."""
        from PyQt6.QtWidgets import QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QCheckBox, QTextEdit

        if isinstance(widget, QLineEdit):
            widget.clear()
        elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
            widget.setValue(widget.minimum())
        elif isinstance(widget, QComboBox):
            widget.setCurrentIndex(-1)  # No selection
        elif isinstance(widget, QCheckBox):
            widget.setChecked(False)
        elif isinstance(widget, QTextEdit):
            widget.clear()
        else:
            # For custom widgets, try to call clear() if available
            if hasattr(widget, 'clear'):
                widget.clear()
            else:
                print(f"⚠️ WARNING: Don't know how to clear {type(widget).__name__}")

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

    def _apply_context_behavior(self, widget: QWidget, value: Any, param_name: str, exclude_field: str = None) -> None:
        """Apply lazy placeholder context behavior - pure function of inputs."""
        if not param_name or not self.dataclass_type:
            return

        if value is None and self.config.is_lazy_dataclass:
            # SIMPLIFIED: Use dual-axis resolution for placeholder text
            placeholder_text = self._get_placeholder_text(param_name)
            if placeholder_text:
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
        # CRITICAL FIX: Create a copy of keys to avoid "dictionary changed during iteration" error
        # reset_parameter can modify self.parameters by removing keys, so we need a stable list
        param_names = list(self.parameters.keys())
        for param_name in param_names:
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
        """Reset parameter with predictable behavior."""
        if param_name not in self.parameters:
            return

        # SIMPLIFIED: Handle function forms vs config forms
        if hasattr(self, 'param_defaults') and self.param_defaults and param_name in self.param_defaults:
            # Function form - reset to static defaults
            reset_value = self.param_defaults[param_name]
            self.parameters[param_name] = reset_value

            if param_name in self.widgets:
                widget = self.widgets[param_name]
                self.update_widget_value(widget, reset_value, param_name, skip_context_behavior=True)

            self.parameter_changed.emit(param_name, reset_value)
            return

        # Config form - use context-aware reset value
        reset_value = self._get_reset_value(param_name)
        self.parameters[param_name] = reset_value

        # Track reset fields only for lazy behavior (when reset_value is None)
        if reset_value is None:
            self.reset_fields.add(param_name)
            # SHARED RESET STATE: Also add to shared reset state for coordination with nested managers
            field_path = f"{self.field_id}.{param_name}"
            self.shared_reset_fields.add(field_path)
        else:
            # For concrete values, remove from reset tracking
            self.reset_fields.discard(param_name)
            field_path = f"{self.field_id}.{param_name}"
            self.shared_reset_fields.discard(field_path)

        # Update widget with reset value
        if param_name in self.widgets:
            widget = self.widgets[param_name]
            self.update_widget_value(widget, reset_value, param_name)

            # Apply placeholder only if reset value is None (lazy behavior)
            if reset_value is None:
                # Use simplified placeholder resolution after reset
                placeholder_text = self._get_placeholder_text(param_name)
                if placeholder_text:
                    PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)

        # Emit parameter change to notify other components
        self.parameter_changed.emit(param_name, reset_value)

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

    def get_user_modified_values(self) -> Dict[str, Any]:
        """
        Get only values that were explicitly set by the user (non-None raw values).

        For lazy dataclasses, this preserves lazy resolution for unmodified fields
        by only returning fields where the raw value is not None.
        """
        if not hasattr(self.config, '_resolve_field_value'):
            # For non-lazy dataclasses, return all current values
            return self.get_current_values()

        user_modified = {}
        current_values = self.get_current_values()

        # Only include fields where the raw value is not None
        for field_name, value in current_values.items():
            if value is not None:
                user_modified[field_name] = value

        return user_modified

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
            if checkbox_state is False:
                # Checkbox unchecked - parameter should be None
                current_values[param_name] = None
            elif checkbox_state is True and current_values[param_name] is None:
                # Checkbox checked but parameter is None - create default instance
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

                    # ❌ MANUAL SIBLING COORDINATION REMOVED: Enhanced decorator events system handles this automatically

                    self.parameter_changed.emit(parent_name, reconstructed_instance)

    # ❌ MANUAL SIBLING COORDINATION REMOVED: Enhanced decorator events system handles this automatically

    # ❌ MANUAL INHERITANCE CHECKING REMOVED: Enhanced decorator events system handles this automatically







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
        """SIMPLIFIED: Refresh placeholder text using dual-axis resolution."""
        if not self.dataclass_type:
            return

        is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(self.dataclass_type)
        if not is_lazy_dataclass:
            return

        # SIMPLIFIED: Use dual-axis resolution directly
        self._refresh_all_placeholders_with_current_context()

        # Recursively refresh nested managers
        self._apply_to_nested_managers(lambda name, manager: manager.refresh_placeholder_text())

    def refresh_placeholder_text_with_context(self, updated_context: Any, changed_dataclass_type: type = None) -> None:
        """Refresh placeholder text using temporary context from current form values.

        This enables live placeholder updates by using a temporary copy of the dataclass
        with current field values, allowing placeholders to update as the user types
        without saving the actual values.
        """
        if not self.dataclass_type:
            return

        is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(self.dataclass_type)
        if not is_lazy_dataclass:
            return

        # Use the updated context (temporary copy with current form values) for placeholder resolution
        self._refresh_all_placeholders_with_temporary_context(updated_context)

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

        # CRITICAL FIX: For lazy dataclasses, DO NOT modify thread-local context
        # Lazy dataclasses should only READ from thread-local config, never WRITE to it
        # The thread-local GlobalPipelineConfig should remain untouched during PipelineConfig editing
        if nested_type_is_lazy:
            print(f"🔍 CONTEXT DEBUG: Constructing lazy {nested_type.__name__} without modifying thread-local context")
            # Do NOT call set_current_global_config - let lazy resolution use the original thread-local context

            # Construct with original thread-local context for lazy resolution
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