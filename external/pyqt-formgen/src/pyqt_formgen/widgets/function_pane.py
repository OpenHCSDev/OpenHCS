"""
Function Pane Widget for PyQt6

Individual function display with parameter editing capabilities.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
from typing import Any, Dict, Callable, Optional, Tuple, List

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QScrollArea, QGroupBox, QSizePolicy
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

from python_introspect import SignatureAnalyzer

# Import PyQt6 help components (using same pattern as Textual TUI)
from pyqt_formgen.theming import ColorScheme

logger = logging.getLogger(__name__)


class FunctionPaneWidget(QWidget):
    """
    PyQt6 Function Pane Widget.
    
    Displays individual function with editable parameters and control buttons.
    Preserves all business logic from Textual version with clean PyQt6 UI.
    """
    
    # Signals
    parameter_changed = pyqtSignal(int, str, object)  # index, param_name, value
    function_changed = pyqtSignal(int)  # index
    add_function = pyqtSignal(int)  # index
    remove_function = pyqtSignal(int)  # index
    move_function = pyqtSignal(int, int)  # index, direction
    reset_parameters = pyqtSignal(int)  # index
    
    def __init__(self, func_item: Tuple[Callable, Dict], index: int, service_adapter, color_scheme: Optional[ColorScheme] = None,
                 step_instance=None, scope_id: Optional[str] = None, parent=None):
        """
        Initialize the function pane widget.

        Args:
            func_item: Tuple of (function, kwargs)
            index: Function index in the list
            service_adapter: PyQt service adapter for dialogs and operations
            color_scheme: Color scheme for UI components
            step_instance: Step instance for context hierarchy (Function → Step → Pipeline → Global)
            scope_id: Scope identifier for cross-window live context updates
            parent: Parent widget
        """
        super().__init__(parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or ColorScheme()

        # Core dependencies
        self.service_adapter = service_adapter

        # CRITICAL: Store step instance for context hierarchy
        self.step_instance = step_instance

        # CRITICAL: Store scope_id for cross-window live context updates
        self.scope_id = scope_id

        # Business logic state (extracted from Textual version)
        self.func, self.kwargs = func_item
        self.index = index
        self.show_parameters = True
        
        # Parameter management (extracted from Textual version)
        if self.func:
            param_info = SignatureAnalyzer.analyze(self.func)

            # Store function signature defaults
            self.param_defaults = {name: info.default_value for name, info in param_info.items()}
        else:
            self.param_defaults = {}

        # Form manager will be created in create_parameter_form() when UI is built
        self.form_manager = None
        
        # Internal kwargs tracking (extracted from Textual version)
        self._internal_kwargs = self.kwargs.copy()
        
        # UI components
        self.parameter_widgets: Dict[str, QWidget] = {}

        # Scope color scheme (used for title color, not border) - init before setup_ui
        self._scope_color_scheme = None

        # Setup UI
        self.setup_ui()
        self.setup_connections()
        
        logger.debug(f"Function pane widget initialized for index {index}")
    
    def setup_ui(self):
        """Setup the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(8, 6, 8, 6)
        layout.setSpacing(4)

        # Combined header with title and buttons on same row
        header_widget = self.create_combined_header()
        layout.addWidget(header_widget)

        # Parameter form (if function exists and parameters shown)
        if self.func and self.show_parameters:
            parameter_frame = self.create_parameter_form()
            layout.addWidget(parameter_frame)

        # Set size policy to only take minimum vertical space needed
        # This prevents function panes from expanding to fill all available space
        # and allows the scroll area in function_list_editor to handle overflow
        size_policy = QSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Minimum)
        self.setSizePolicy(size_policy)

        # Set styling - subtle border, match window theme
        self.setStyleSheet(f"""
            FunctionPaneWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 4px;
            }}
        """)

    def set_scope_color_scheme(self, scheme) -> None:
        """Set scope color scheme for title color styling (no border on FunctionPaneWidget)."""
        logger.info(f"🎨 FunctionPaneWidget.set_scope_color_scheme: scheme={scheme is not None}, has_func_name_label={hasattr(self, 'func_name_label')}, has_parameters_groupbox={hasattr(self, 'parameters_groupbox')}")
        self._scope_color_scheme = scheme
        # Update function name label color
        if hasattr(self, 'func_name_label') and scheme:
            from pyqt_formgen.widgets.shared.scope_color_utils import tint_color_perceptual
            accent_color = tint_color_perceptual(scheme.base_color_rgb, 1)
            logger.info(f"🎨 FunctionPaneWidget: Setting func_name_label color to {accent_color.name()}")
            self.func_name_label.setStyleSheet(f"color: {accent_color.name()};")
        # Update parameters groupbox title color
        if hasattr(self, 'parameters_groupbox'):
            logger.info(f"🎨 FunctionPaneWidget: Applying parameters_groupbox styling")
            self._apply_parameters_groupbox_styling()

    def _apply_parameters_groupbox_styling(self) -> None:
        """Apply styling to the Parameters groupbox with scope accent color if available."""
        # Use scope accent color if available, otherwise default
        if self._scope_color_scheme:
            from pyqt_formgen.widgets.shared.scope_color_utils import tint_color_perceptual
            accent_color = tint_color_perceptual(self._scope_color_scheme.base_color_rgb, 1)
            title_color = accent_color.name()
        else:
            title_color = self.color_scheme.to_hex(self.color_scheme.text_accent)

        self.parameters_groupbox.setStyleSheet(f"""
            QGroupBox {{
                font-weight: bold;
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 3px;
                margin-top: 10px;
                padding-top: 10px;
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
            }}
            QGroupBox::title {{
                subcontrol-origin: margin;
                left: 10px;
                padding: 0 5px 0 5px;
                color: {title_color};
            }}
        """)
    
    def create_combined_header(self) -> QWidget:
        """
        Create combined header with title and buttons on the same row.

        Returns:
            Widget containing title and control buttons
        """
        # Use plain QWidget - no frame border, let parent styling handle background
        header = QWidget()
        layout = QHBoxLayout(header)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(8)

        # Function name with help functionality (left side)
        if self.func:
            func_name = self.func.__name__
            func_module = self.func.__module__

            # Function name - store as instance attr for scope accent styling
            self.func_name_label = QLabel(f"🔧 {func_name}")
            self.func_name_label.setFont(QFont("Arial", 10, QFont.Weight.Bold))
            self.func_name_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
            layout.addWidget(self.func_name_label)

            # Help indicator for function (import locally to avoid circular imports)
            from pyqt_formgen.widgets.shared.clickable_help_components import HelpIndicator
            help_indicator = HelpIndicator(help_target=self.func, color_scheme=self.color_scheme)
            layout.addWidget(help_indicator)

            # Module info - subtle, truncated
            if func_module:
                # Show only last 2 parts of module path for compactness
                parts = func_module.split('.')
                short_module = '.'.join(parts[-2:]) if len(parts) > 2 else func_module
                module_label = QLabel(f"({short_module})")
                module_label.setFont(QFont("Arial", 8))
                module_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_disabled)};")
                layout.addWidget(module_label)
        else:
            name_label = QLabel("No Function Selected")
            name_label.setFont(QFont("Arial", 10))
            name_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.status_error)};")
            layout.addWidget(name_label)

        layout.addStretch()

        # Control buttons (right side) - minimal styling, match window theme
        # Button configurations
        button_configs = [
            ("↑", "move_up", "Move function up"),
            ("↓", "move_down", "Move function down"),
            ("Add", "add_func", "Add new function"),
            ("Del", "remove_func", "Delete this function"),
            ("Reset", "reset_all", "Reset all parameters"),
        ]

        button_style = f"""
            QPushButton {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                border: none;
                border-radius: 3px;
                padding: 4px 8px;
            }}
            QPushButton:hover {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.button_hover_bg)};
            }}
            QPushButton:pressed {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.button_pressed_bg)};
            }}
        """

        for name, action, tooltip in button_configs:
            button = QPushButton(name)
            button.setToolTip(tooltip)
            button.setStyleSheet(button_style)

            # Connect button to action
            button.clicked.connect(lambda checked, a=action: self.handle_button_action(a))

            layout.addWidget(button)

        return header
    
    def create_parameter_form(self) -> QWidget:
        """
        Create the parameter form using extracted business logic.
        
        Returns:
            Widget containing parameter form
        """
        # Store as instance attribute for scope accent styling
        self.parameters_groupbox = QGroupBox("Parameters")
        self._apply_parameters_groupbox_styling()
        group_box = self.parameters_groupbox
        
        layout = QVBoxLayout(group_box)

        # Create the ParameterFormManager with help and reset functionality
        # Import the enhanced PyQt6 ParameterFormManager
        from pyqt_formgen.forms import ParameterFormManager as PyQtParameterFormManager, FormManagerConfig

        # Create form manager with initial_values to load saved kwargs
        # CRITICAL: Pass step_instance as context_obj for lazy resolution hierarchy
        # Function parameters → Step → Pipeline → Global
        # CRITICAL: Pass scope_id for cross-window live context updates (real-time placeholder sync)
        # IMPORTANT UI BEHAVIOR:
        # - FunctionListWidget already wraps all FunctionPaneWidgets in a QScrollArea.
        # - If we also enable a scroll area inside ParameterFormManager here, the
        #   inner scroll will expand to fill the available height, making the
        #   "Parameters" pane look like it stretches to consume all vertical
        #   space even when only a few rows are present.
        # - To keep each function pane only as tall as its content, we explicitly
        #   disable the inner scroll area and let the outer FunctionListWidget
        #   handle scrolling for long forms.

        # Optional imports - stub if not available
        try:
            from objectstate import ObjectState, ObjectStateRegistry
        except ImportError:
            ObjectState = None  # type: ignore
            ObjectStateRegistry = None  # type: ignore

        try:
            from pyqt_formgen.services.scope_token_service import ScopeTokenService
        except ImportError:
            ScopeTokenService = None  # type: ignore

        # Build function-specific scope: step_scope::func_N
        step_scope = self.scope_id or "no_scope"
        func_scope_id = ScopeTokenService.build_scope_id(step_scope, self.func)

        # Check if ObjectState already exists (e.g., from time travel restore)
        # If so, reuse it to preserve restored state; otherwise create new
        existing_state = ObjectStateRegistry.get_by_scope(func_scope_id)
        if existing_state:
            func_state = existing_state
            self._func_state = None  # Don't cleanup - we didn't create it
        else:
            # Get parent state (step state) from registry for context inheritance
            parent_state = ObjectStateRegistry.get_by_scope(step_scope)
            func_state = ObjectState(
                object_instance=self.func,
                scope_id=func_scope_id,
                parent_state=parent_state,
                initial_values=self.kwargs,
            )
            ObjectStateRegistry.register(func_state)
            self._func_state = func_state  # Store for cleanup

        self.form_manager = PyQtParameterFormManager(
            state=func_state,
            config=FormManagerConfig(
                parent=self,                      # Pass self as parent widget
                color_scheme=self.color_scheme,   # Pass color_scheme for consistent theming
                use_scroll_area=False,            # Let outer FunctionListWidget manage scrolling
            )
        )

        # Connect parameter changes
        self.form_manager.parameter_changed.connect(
            lambda param_name, value: self.handle_parameter_change(param_name, value)
        )

        layout.addWidget(self.form_manager)

        return group_box

    def cleanup_object_state(self) -> None:
        """Unregister ObjectState on widget destruction."""
        try:
            from objectstate import ObjectStateRegistry
            if hasattr(self, '_func_state') and self._func_state:
                ObjectStateRegistry.unregister(self._func_state)
                self._func_state = None
        except ImportError:
            pass  # ObjectStateRegistry not available

    def create_parameter_widget(self, param_name: str, param_type: type, current_value: Any) -> Optional[QWidget]:
        """
        Create parameter widget based on type.

        Args:
            param_name: Parameter name
            param_type: Parameter type
            current_value: Current parameter value

        Returns:
            Widget for parameter editing or None
        """
        from PyQt6.QtWidgets import QLineEdit
        from pyqt_formgen.widgets import (
            NoScrollSpinBox, NoScrollDoubleSpinBox
        )

        # Boolean parameters
        if param_type == bool:
            from pyqt_formgen.widgets import NoneAwareCheckBox
            widget = NoneAwareCheckBox()
            widget.set_value(current_value)  # Use set_value to handle None properly
            widget.toggled.connect(lambda checked: self.handle_parameter_change(param_name, checked))
            return widget

        # Integer parameters
        elif param_type == int:
            widget = NoScrollSpinBox()
            widget.setRange(-999999, 999999)
            widget.setValue(int(current_value) if current_value is not None else 0)
            widget.valueChanged.connect(lambda value: self.handle_parameter_change(param_name, value))
            return widget

        # Float parameters
        elif param_type == float:
            widget = NoScrollDoubleSpinBox()
            widget.setRange(-999999.0, 999999.0)
            widget.setDecimals(6)
            widget.setValue(float(current_value) if current_value is not None else 0.0)
            widget.valueChanged.connect(lambda value: self.handle_parameter_change(param_name, value))
            return widget

        # Enum parameters
        elif any(base.__name__ == 'Enum' for base in param_type.__bases__):
            from pyqt_formgen.forms.widget_strategies import create_enum_widget_unified

            # Use the single source of truth for enum widget creation
            widget = create_enum_widget_unified(param_type, current_value)

            widget.currentIndexChanged.connect(
                lambda index: self.handle_parameter_change(param_name, widget.itemData(index))
            )
            return widget

        # String and other parameters
        else:
            widget = QLineEdit()
            widget.setText(str(current_value) if current_value is not None else "")
            widget.textChanged.connect(lambda text: self.handle_parameter_change(param_name, text))
            return widget
    
    def setup_connections(self):
        """Setup signal/slot connections."""
        pass  # Connections are set up in widget creation
    
    def handle_button_action(self, action: str):
        """
        Handle button actions (extracted from Textual version).
        
        Args:
            action: Action identifier
        """
        if action == "move_up":
            self.move_function.emit(self.index, -1)
        elif action == "move_down":
            self.move_function.emit(self.index, 1)
        elif action == "add_func":
            self.add_function.emit(self.index + 1)
        elif action == "remove_func":
            self.remove_function.emit(self.index)
        elif action == "reset_all":
            self.reset_all_parameters()
    
    def handle_parameter_change(self, param_name: str, value: Any):
        """
        Handle parameter value changes (extracted from Textual version).

        Args:
            param_name: Full path like "func_0.sigma" or just "func_0.param_name"
            value: New parameter value
        """
        # Extract leaf field name from full path
        # "func_0.sigma" -> "sigma"
        leaf_field = param_name.split('.')[-1]

        # Update internal kwargs without triggering reactive update
        self._internal_kwargs[leaf_field] = value

        # The form manager already has the updated value (it emitted this signal)
        # No need to call update_parameter() again - that would be redundant

        # Emit parameter changed signal to notify parent (function list editor)
        self.parameter_changed.emit(self.index, leaf_field, value)

        logger.debug(f"Parameter changed: {param_name} = {value}")
    
    def reset_all_parameters(self):
        """Reset all parameters to default values using PyQt6 form manager."""
        if not self.form_manager:
            return

        # Reset all parameters - form manager will use signature defaults from param_defaults
        for param_name in list(self.form_manager.parameters.keys()):
            self.form_manager.reset_parameter(param_name)

        # Update internal kwargs to match the reset values
        self._internal_kwargs = self._func_state.get_current_values()

        # Emit parameter changed signals for each reset parameter
        for param_name, default_value in self.param_defaults.items():
            self.parameter_changed.emit(self.index, param_name, default_value)

        self.reset_parameters.emit(self.index)
    
    def update_widget_value(self, widget: QWidget, value: Any):
        """
        Update widget value without triggering signals.
        
        Args:
            widget: Widget to update
            value: New value
        """
        from PyQt6.QtWidgets import QLineEdit, QCheckBox, QSpinBox, QDoubleSpinBox, QComboBox
        # Import the no-scroll classes from single source of truth
        from pyqt_formgen.widgets import (
            NoScrollSpinBox, NoScrollDoubleSpinBox, NoScrollComboBox
        )
        
        # Temporarily block signals to avoid recursion
        widget.blockSignals(True)
        
        try:
            if isinstance(widget, QCheckBox):
                widget.setChecked(bool(value))
            elif isinstance(widget, (QSpinBox, NoScrollSpinBox)):
                widget.setValue(int(value) if value is not None else 0)
            elif isinstance(widget, (QDoubleSpinBox, NoScrollDoubleSpinBox)):
                widget.setValue(float(value) if value is not None else 0.0)
            elif isinstance(widget, (QComboBox, NoScrollComboBox)):
                for i in range(widget.count()):
                    if widget.itemData(i) == value:
                        widget.setCurrentIndex(i)
                        break
            elif isinstance(widget, QLineEdit):
                widget.setText(str(value) if value is not None else "")
        finally:
            widget.blockSignals(False)
    
    def get_current_kwargs(self) -> Dict[str, Any]:
        """
        Get current kwargs values (extracted from Textual version).
        
        Returns:
            Current parameter values
        """
        return self._internal_kwargs.copy()
    
    def sync_kwargs(self):
        """Sync internal kwargs to main kwargs (extracted from Textual version)."""
        self.kwargs = self._internal_kwargs.copy()
    
    def update_function(self, func_item: Tuple[Callable, Dict]):
        """
        Update the function and parameters.
        
        Args:
            func_item: New function item tuple
        """
        self.func, self.kwargs = func_item
        self._internal_kwargs = self.kwargs.copy()
        
        # Update parameter defaults
        if self.func:
            param_info = SignatureAnalyzer.analyze(self.func)
            # Store function signature defaults
            self.param_defaults = {name: info.default_value for name, info in param_info.items()}
        else:
            self.param_defaults = {}

        # Form manager will be recreated in create_parameter_form() when UI is rebuilt
        self.form_manager = None

        # Rebuild UI (this will create the form manager in create_parameter_form())
        self.setup_ui()
        
        logger.debug(f"Updated function for index {self.index}")


class FunctionListWidget(QWidget):
    """
    PyQt6 Function List Widget.
    
    Container for multiple FunctionPaneWidgets with list management.
    """
    
    # Signals
    functions_changed = pyqtSignal(list)  # List of function items
    
    def __init__(self, service_adapter, color_scheme: Optional[ColorScheme] = None, parent=None):
        """
        Initialize the function list widget.
        
        Args:
            service_adapter: PyQt service adapter
            parent: Parent widget
        """
        super().__init__(parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or ColorScheme()
        
        self.service_adapter = service_adapter
        self.functions: List[Tuple[Callable, Dict]] = []
        self.function_panes: List[FunctionPaneWidget] = []
        
        # Setup UI
        self.setup_ui()
    
    def setup_ui(self):
        """Setup the user interface."""
        layout = QVBoxLayout(self)
        
        # Scroll area for function panes
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        
        # Container widget for function panes
        self.container_widget = QWidget()
        self.container_layout = QVBoxLayout(self.container_widget)
        self.container_layout.setSpacing(5)
        
        scroll_area.setWidget(self.container_widget)
        layout.addWidget(scroll_area)
        
        # Add function button
        add_button = QPushButton("Add Function")
        add_button.clicked.connect(lambda: self.add_function_at_index(len(self.functions)))
        layout.addWidget(add_button)
    
    def update_function_list(self):
        """Update the function list display."""
        # Clear existing panes - CRITICAL: Manually unregister form managers BEFORE deleteLater()
        # This prevents RuntimeError when new widgets try to connect to deleted managers
        for pane in self.function_panes:
            # Unregister ObjectState
            if hasattr(pane, 'cleanup_object_state'):
                pane.cleanup_object_state()
            # Explicitly unregister the form manager before scheduling deletion
            if hasattr(pane, 'form_manager') and pane.form_manager is not None:
                try:
                    pane.form_manager.unregister_from_cross_window_updates()
                except RuntimeError:
                    pass  # Already deleted
            pane.deleteLater()  # Schedule for deletion - triggers destroyed signal
        self.function_panes.clear()
        
        # Create new panes
        for i, func_item in enumerate(self.functions):
            pane = FunctionPaneWidget(func_item, i, self.service_adapter, color_scheme=self.color_scheme)
            
            # Connect signals
            pane.parameter_changed.connect(self.on_parameter_changed)
            pane.add_function.connect(self.add_function_at_index)
            pane.remove_function.connect(self.remove_function_at_index)
            pane.move_function.connect(self.move_function)
            
            self.function_panes.append(pane)
            self.container_layout.addWidget(pane)
        
        self.container_layout.addStretch()
    
    def add_function_at_index(self, index: int):
        """Add function at specific index."""
        # Placeholder function
        new_func_item = (lambda x: x, {})
        self.functions.insert(index, new_func_item)
        self.update_function_list()
        self.functions_changed.emit(self.functions)
    
    def remove_function_at_index(self, index: int):
        """Remove function at specific index."""
        if 0 <= index < len(self.functions):
            self.functions.pop(index)
            self.update_function_list()
            self.functions_changed.emit(self.functions)
    
    def move_function(self, index: int, direction: int):
        """Move function up or down."""
        new_index = index + direction
        if 0 <= new_index < len(self.functions):
            self.functions[index], self.functions[new_index] = self.functions[new_index], self.functions[index]
            self.update_function_list()
            self.functions_changed.emit(self.functions)
    
    def on_parameter_changed(self, index: int, param_name: str, value: Any):
        """Handle parameter changes."""
        if 0 <= index < len(self.functions):
            func, kwargs = self.functions[index]
            new_kwargs = kwargs.copy()
            new_kwargs[param_name] = value
            self.functions[index] = (func, new_kwargs)
            self.functions_changed.emit(self.functions)
