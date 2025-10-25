"""
Function Pane Widget for PyQt6

Individual function display with parameter editing capabilities.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
from typing import Any, Dict, Callable, Optional, Tuple

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, 
    QFrame, QScrollArea, QGroupBox
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

from openhcs.introspection.signature_analyzer import SignatureAnalyzer

# Import PyQt6 help components (using same pattern as Textual TUI)
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme

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
    
    def __init__(self, func_item: Tuple[Callable, Dict], index: int, service_adapter, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """
        Initialize the function pane widget.
        
        Args:
            func_item: Tuple of (function, kwargs)
            index: Function index in the list
            service_adapter: PyQt service adapter for dialogs and operations
            parent: Parent widget
        """
        super().__init__(parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        
        # Core dependencies
        self.service_adapter = service_adapter
        
        # Business logic state (extracted from Textual version)
        self.func, self.kwargs = func_item
        self.index = index
        self.show_parameters = True
        
        # Parameter management (extracted from Textual version)
        if self.func:
            param_info = SignatureAnalyzer.analyze(self.func)

            # Store function signature defaults
            self.param_defaults = {name: info.default_value for name, info in param_info.items()}

            print(f"🔍 FUNCTION PANE: func={self.func.__name__}, kwargs={self.kwargs}")
        else:
            self.param_defaults = {}

        # Form manager will be created in create_parameter_form() when UI is built
        self.form_manager = None
        
        # Internal kwargs tracking (extracted from Textual version)
        self._internal_kwargs = self.kwargs.copy()
        
        # UI components
        self.parameter_widgets: Dict[str, QWidget] = {}
        
        # Setup UI
        self.setup_ui()
        self.setup_connections()
        
        logger.debug(f"Function pane widget initialized for index {index}")
    
    def setup_ui(self):
        """Setup the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(5, 5, 5, 5)
        layout.setSpacing(5)

        # Combined header with title and buttons on same row
        header_frame = self.create_combined_header()
        layout.addWidget(header_frame)

        # Parameter form (if function exists and parameters shown)
        if self.func and self.show_parameters:
            parameter_frame = self.create_parameter_form()
            layout.addWidget(parameter_frame)

        # Set styling
        self.setStyleSheet(f"""
            FunctionPaneWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.window_bg)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 5px;
                margin: 2px;
            }}
        """)
    
    def create_combined_header(self) -> QWidget:
        """
        Create combined header with title and buttons on the same row.

        Returns:
            Widget containing title and control buttons
        """
        frame = QFrame()
        frame.setFrameStyle(QFrame.Shape.Box)
        frame.setStyleSheet(f"""
            QFrame {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.separator_color)};
                border-radius: 3px;
                padding: 5px;
            }}
        """)

        layout = QHBoxLayout(frame)
        layout.setSpacing(10)

        # Function name with help functionality (left side)
        if self.func:
            func_name = self.func.__name__
            func_module = self.func.__module__

            # Function name with help
            name_label = QLabel(f"🔧 {func_name}")
            name_label.setFont(QFont("Arial", 10, QFont.Weight.Bold))
            name_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
            layout.addWidget(name_label)

            # Help indicator for function (import locally to avoid circular imports)
            from openhcs.pyqt_gui.widgets.shared.clickable_help_components import HelpIndicator
            help_indicator = HelpIndicator(help_target=self.func, color_scheme=self.color_scheme)
            layout.addWidget(help_indicator)

            # Module info
            if func_module:
                module_label = QLabel(f"({func_module})")
                module_label.setFont(QFont("Arial", 8))
                module_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_disabled)};")
                layout.addWidget(module_label)
        else:
            name_label = QLabel("No Function Selected")
            name_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.status_error)};")
            layout.addWidget(name_label)

        layout.addStretch()

        # Control buttons (right side) - using parameter form manager style
        from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
        style_gen = StyleSheetGenerator(self.color_scheme)
        button_styles = style_gen.generate_config_button_styles()

        # Button configurations
        button_configs = [
            ("↑", "move_up", "Move function up"),
            ("↓", "move_down", "Move function down"),
            ("Add", "add_func", "Add new function"),
            ("Delete", "remove_func", "Delete this function"),
            ("Reset", "reset_all", "Reset all parameters"),
        ]

        for name, action, tooltip in button_configs:
            button = QPushButton(name)
            button.setToolTip(tooltip)
            button.setMaximumWidth(60)

            # Use reset button style for all buttons (consistent with parameter form manager)
            button.setStyleSheet(button_styles["reset"])

            # Connect button to action
            button.clicked.connect(lambda checked, a=action: self.handle_button_action(a))

            layout.addWidget(button)

        return frame
    
    def create_parameter_form(self) -> QWidget:
        """
        Create the parameter form using extracted business logic.
        
        Returns:
            Widget containing parameter form
        """
        group_box = QGroupBox("Parameters")
        group_box.setStyleSheet(f"""
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
                color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};
            }}
        """)
        
        layout = QVBoxLayout(group_box)

        # Create the ParameterFormManager with help and reset functionality
        # Import the enhanced PyQt6 ParameterFormManager
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager as PyQtParameterFormManager

        # Create form manager with initial_values to load saved kwargs
        self.form_manager = PyQtParameterFormManager(
            object_instance=self.func,       # Pass function as the object to build form for
            field_id=f"func_{self.index}",   # Use function index as field identifier
            parent=self,                     # Pass self as parent widget
            context_obj=None,                # Functions don't need context for placeholder resolution
            initial_values=self.kwargs,      # Pass saved kwargs to populate form fields
            color_scheme=self.color_scheme   # Pass color_scheme for consistent theming
        )

        # Connect parameter changes
        self.form_manager.parameter_changed.connect(
            lambda param_name, value: self.handle_parameter_change(param_name, value)
        )

        layout.addWidget(self.form_manager)
        
        return group_box
    
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
        from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import (
            NoScrollSpinBox, NoScrollDoubleSpinBox
        )

        # Boolean parameters
        if param_type == bool:
            from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import NoneAwareCheckBox
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
            from openhcs.pyqt_gui.widgets.shared.widget_strategies import create_enum_widget_unified

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
            param_name: Name of the parameter
            value: New parameter value
        """
        # Update internal kwargs without triggering reactive update
        self._internal_kwargs[param_name] = value

        # The form manager already has the updated value (it emitted this signal)
        # No need to call update_parameter() again - that would be redundant

        # Emit parameter changed signal to notify parent (function list editor)
        self.parameter_changed.emit(self.index, param_name, value)

        logger.debug(f"Parameter changed: {param_name} = {value}")
    
    def reset_all_parameters(self):
        """Reset all parameters to default values using PyQt6 form manager."""
        logger.info(f"🔍 RESET: reset_all_parameters called for function {self.index}")
        logger.info(f"🔍 RESET: self.param_defaults = {self.param_defaults}")

        if not self.form_manager:
            logger.warning("🔍 RESET: No form_manager found!")
            return

        logger.info(f"🔍 RESET: form_manager.parameters = {self.form_manager.parameters}")

        # Reset all parameters - form manager will use signature defaults from param_defaults
        for param_name in list(self.form_manager.parameters.keys()):
            logger.info(f"🔍 RESET: Resetting {param_name}")
            self.form_manager.reset_parameter(param_name)

        # Update internal kwargs to match the reset values
        self._internal_kwargs = self.form_manager.get_current_values()
        logger.info(f"🔍 RESET: After reset, _internal_kwargs = {self._internal_kwargs}")

        # Emit parameter changed signals for each reset parameter
        for param_name, default_value in self.param_defaults.items():
            self.parameter_changed.emit(self.index, param_name, default_value)

        self.reset_parameters.emit(self.index)
        logger.info(f"🔍 RESET: Reset complete for function {self.index}")
    
    def update_widget_value(self, widget: QWidget, value: Any):
        """
        Update widget value without triggering signals.
        
        Args:
            widget: Widget to update
            value: New value
        """
        from PyQt6.QtWidgets import QLineEdit, QCheckBox, QSpinBox, QDoubleSpinBox, QComboBox
        # Import the no-scroll classes from single source of truth
        from openhcs.pyqt_gui.widgets.shared.no_scroll_spinbox import (
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
    
    def __init__(self, service_adapter, color_scheme: Optional[PyQt6ColorScheme] = None, parent=None):
        """
        Initialize the function list widget.
        
        Args:
            service_adapter: PyQt service adapter
            parent: Parent widget
        """
        super().__init__(parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        
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
