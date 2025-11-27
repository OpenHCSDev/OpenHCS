"""
Function List Editor Widget for PyQt6 GUI.

Mirrors the Textual TUI FunctionListEditorWidget with sophisticated parameter forms.
Displays a scrollable list of function panes with Add/Load/Save/Code controls.
"""

import logging
import os
from typing import List, Union, Dict, Optional

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, 
    QScrollArea
)
from PyQt6.QtCore import Qt, pyqtSignal

from openhcs.processing.backends.lib_registry.registry_service import RegistryService
from openhcs.ui.shared.pattern_data_manager import PatternDataManager
from openhcs.pyqt_gui.widgets.function_pane import FunctionPaneWidget
from openhcs.constants.constants import GroupBy
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.widgets.shared.widget_strategies import _get_enum_display_text

logger = logging.getLogger(__name__)


class FunctionListEditorWidget(QWidget):
    """
    Function list editor widget that mirrors Textual TUI functionality.
    
    Displays functions with parameter editing, Add/Delete/Reset buttons,
    and Load/Save/Code functionality.
    """
    
    # Signals
    function_pattern_changed = pyqtSignal()
    
    def __init__(self, initial_functions: Union[List, Dict, callable, None] = None,
                 step_identifier: str = None, service_adapter=None, color_scheme: Optional[PyQt6ColorScheme] = None,
                 step_instance=None, scope_id: Optional[str] = None, parent=None):
        super().__init__(parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or PyQt6ColorScheme()

        # Initialize services (reuse existing business logic)
        self.registry_service = RegistryService()
        self.data_manager = PatternDataManager()
        self.service_adapter = service_adapter

        # Step identifier for cache isolation
        self.step_identifier = step_identifier or f"widget_{id(self)}"

        # CRITICAL: Store step instance for context hierarchy (Function → Step → Pipeline → Global)
        self.step_instance = step_instance

        # CRITICAL: Store scope_id for cross-window live context updates
        self.scope_id = scope_id

        # Step configuration properties (mirrors Textual TUI)
        self.current_group_by = None  # Current GroupBy setting from step editor
        self.current_variable_components = []  # Current VariableComponents list from step editor
        self.selected_channel = None  # Currently selected channel
        self.available_channels = []  # Available channels from orchestrator
        self.is_dict_mode = False  # Whether we're in channel-specific mode

        # Component selection cache per GroupBy (mirrors Textual TUI)
        self.component_selections = {}

        # Initialize pattern data and mode
        self._initialize_pattern_data(initial_functions)

        # UI components
        self.function_panes = []

        self.setup_ui()
        self.setup_connections()

        logger.debug(f"Function list editor initialized with {len(self.functions)} functions")

    def _initialize_pattern_data(self, initial_functions):
        """Initialize pattern data from various input formats (mirrors Textual TUI logic)."""
        print(f"🔍 FUNC LIST EDITOR _initialize_pattern_data: initial_functions = {initial_functions}")
        if initial_functions is None:
            self.pattern_data = []
            self.is_dict_mode = False
            self.functions = []
        elif callable(initial_functions):
            # Single callable: treat as [(callable, {})]
            self.pattern_data = [(initial_functions, {})]
            self.is_dict_mode = False
            self.functions = [(initial_functions, {})]
        elif isinstance(initial_functions, tuple) and len(initial_functions) == 2 and callable(initial_functions[0]) and isinstance(initial_functions[1], dict):
            # Single tuple (callable, kwargs): treat as [(callable, kwargs)]
            self.pattern_data = [initial_functions]
            self.is_dict_mode = False
            self.functions = [initial_functions]
        elif isinstance(initial_functions, list):
            print("🔍 FUNC LIST EDITOR: initial_functions is a list, calling _normalize_function_list")
            self.pattern_data = initial_functions
            self.is_dict_mode = False
            self.functions = self._normalize_function_list(initial_functions)
            print(f"🔍 FUNC LIST EDITOR: self.functions AFTER normalize = {self.functions}")
        elif isinstance(initial_functions, dict):
            # Convert any integer keys to string keys for consistency
            normalized_dict = {}
            for key, value in initial_functions.items():
                str_key = str(key)
                normalized_dict[str_key] = self._normalize_function_list(value) if value else []

            self.pattern_data = normalized_dict
            self.is_dict_mode = True

            # Set selected channel to first key and load its functions
            if normalized_dict:
                self.selected_channel = next(iter(normalized_dict.keys()))
                self.functions = normalized_dict[self.selected_channel]
            else:
                self.selected_channel = None
                self.functions = []
        else:
            logger.warning(f"Unknown initial_functions type: {type(initial_functions)}")
            self.pattern_data = []
            self.is_dict_mode = False
            self.functions = []

    def _normalize_function_list(self, func_list):
        """Normalize function list using PatternDataManager."""
        print(f"🔍 NORMALIZE: INPUT = {func_list}")
        # Handle single tuple (function, kwargs) case - wrap in list
        if isinstance(func_list, tuple) and len(func_list) == 2 and callable(func_list[0]) and isinstance(func_list[1], dict):
            func_list = [func_list]
        # Handle single callable case - wrap in list with empty kwargs
        elif callable(func_list):
            func_list = [(func_list, {})]
        # Handle empty or None case
        elif not func_list:
            return []

        normalized = []
        for i, item in enumerate(func_list):
            print(f"🔍 NORMALIZE: Processing item {i}: {item}")
            func, kwargs = self.data_manager.extract_func_and_kwargs(item)
            print(f"🔍 NORMALIZE: Extracted func={func.__name__ if func else None}, kwargs={kwargs}")
            if func:
                normalized.append((func, kwargs))
        print(f"🔍 NORMALIZE: OUTPUT = {normalized}")
        return normalized
    
    def setup_ui(self):
        """Setup the user interface."""
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(8)
        
        # Header with controls (mirrors Textual TUI)
        header_layout = QHBoxLayout()
        
        functions_label = QLabel("Functions")
        functions_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-weight: bold; font-size: 14px;")
        header_layout.addWidget(functions_label)
        
        header_layout.addStretch()
        
        # Control buttons (mirrors Textual TUI)
        add_btn = QPushButton("Add")
        add_btn.setMaximumWidth(60)
        add_btn.setStyleSheet(self._get_button_style())
        add_btn.clicked.connect(self.add_function)
        header_layout.addWidget(add_btn)

        # Code button supersedes Load/Save buttons (provides both functionality via text editor)
        code_btn = QPushButton("Code")
        code_btn.setMaximumWidth(60)
        code_btn.setStyleSheet(self._get_button_style())
        code_btn.clicked.connect(self.edit_function_code)
        header_layout.addWidget(code_btn)

        # Component selection button (mirrors Textual TUI)
        self.component_btn = QPushButton(self._get_component_button_text())
        self.component_btn.setMaximumWidth(120)
        self.component_btn.setStyleSheet(self._get_button_style())
        self.component_btn.clicked.connect(self.show_component_selection_dialog)
        self.component_btn.setEnabled(not self._is_component_button_disabled())
        header_layout.addWidget(self.component_btn)

        # Channel navigation buttons (only in dict mode with multiple channels, mirrors Textual TUI)
        self.prev_channel_btn = QPushButton("<")
        self.prev_channel_btn.setMaximumWidth(30)
        self.prev_channel_btn.setStyleSheet(self._get_button_style())
        self.prev_channel_btn.clicked.connect(lambda: self._navigate_channel(-1))
        header_layout.addWidget(self.prev_channel_btn)

        self.next_channel_btn = QPushButton(">")
        self.next_channel_btn.setMaximumWidth(30)
        self.next_channel_btn.setStyleSheet(self._get_button_style())
        self.next_channel_btn.clicked.connect(lambda: self._navigate_channel(1))
        header_layout.addWidget(self.next_channel_btn)

        # Update navigation button visibility
        self._update_navigation_buttons()

        header_layout.addStretch()
        layout.addLayout(header_layout)
        
        # Scrollable function list (mirrors Textual TUI)
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.scroll_area.setStyleSheet(f"""
            QScrollArea {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 4px;
            }}
        """)
        
        # Function list container
        self.function_container = QWidget()
        self.function_layout = QVBoxLayout(self.function_container)
        self.function_layout.setAlignment(Qt.AlignmentFlag.AlignTop)
        self.function_layout.setSpacing(8)
        
        # Populate function list
        self._populate_function_list()
        
        self.scroll_area.setWidget(self.function_container)
        layout.addWidget(self.scroll_area)
    
    def _get_button_style(self) -> str:
        """Get consistent button styling."""
        return """
            QPushButton {
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: white;
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_light)};
                border-radius: 3px;
                padding: 6px 12px;
                font-size: 11px;
            }
            QPushButton:hover {
                background-color: {self.color_scheme.to_hex(self.color_scheme.button_hover_bg)};
            }
            QPushButton:pressed {
                background-color: {self.color_scheme.to_hex(self.color_scheme.button_pressed_bg)};
            }
        """
    
    def _populate_function_list(self):
        """Populate function list with panes (mirrors Textual TUI)."""
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

        # Clear layout
        while self.function_layout.count():
            child = self.function_layout.takeAt(0)
            if child.widget():
                # Unregister form manager if it exists
                widget = child.widget()
                if hasattr(widget, 'form_manager') and widget.form_manager is not None:
                    try:
                        widget.form_manager.unregister_from_cross_window_updates()
                    except RuntimeError:
                        pass  # Already deleted
                widget.deleteLater()  # Schedule for deletion instead of just orphaning
        
        if not self.functions:
            # Show empty state
            empty_label = QLabel("No functions defined. Click 'Add' to begin.")
            empty_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            empty_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_disabled)}; font-style: italic; padding: 20px;")
            self.function_layout.addWidget(empty_label)
        else:
            # Create function panes
            for i, func_item in enumerate(self.functions):
                print(f"🔍 FUNC LIST EDITOR: Creating pane {i} with func_item = {func_item}")
                pane = FunctionPaneWidget(func_item, i, self.service_adapter, color_scheme=self.color_scheme,
                                         step_instance=self.step_instance, scope_id=self.scope_id)

                # Connect signals (using actual FunctionPaneWidget signal names)
                pane.move_function.connect(self._move_function)
                pane.add_function.connect(self._add_function_at_index)
                pane.remove_function.connect(self._remove_function)
                pane.parameter_changed.connect(self._on_parameter_changed)

                self.function_panes.append(pane)
                self.function_layout.addWidget(pane)

                # CRITICAL FIX: Apply initial enabled styling for function panes
                # This ensures that when the function pattern editor opens, disabled functions
                # show the correct dimmed styling immediately, not just after toggling
                if hasattr(pane, 'form_manager') and pane.form_manager is not None:
                    # Use QTimer to ensure this runs after the widget is fully constructed
                    from PyQt6.QtCore import QTimer
                    QTimer.singleShot(0, lambda p=pane: self._apply_initial_enabled_styling_to_pane(p))
    
    def _apply_initial_enabled_styling_to_pane(self, pane):
        """Apply initial enabled styling to a function pane.

        This is called after a function pane is created to ensure that disabled functions
        show the correct dimmed styling immediately when the function pattern editor opens.

        Args:
            pane: FunctionPaneWidget instance to apply styling to
        """
        try:
            if hasattr(pane, 'form_manager') and pane.form_manager is not None:
                # Check if the form manager has an enabled field
                if 'enabled' in pane.form_manager.parameters:
                    # CRITICAL FIX: Call the service method, not a non-existent manager method
                    pane.form_manager._enabled_field_styling_service.apply_initial_enabled_styling(pane.form_manager)
        except Exception as e:
            # Log error but don't crash the UI
            import logging
            logger = logging.getLogger(__name__)
            logger.warning(f"Failed to apply initial enabled styling to function pane: {e}")

    def setup_connections(self):
        """Setup signal/slot connections."""
        pass
    
    def add_function(self):
        """Add a new function (mirrors Textual TUI)."""
        from openhcs.pyqt_gui.dialogs.function_selector_dialog import FunctionSelectorDialog

        # Show function selector dialog (reuses Textual TUI logic)
        selected_function = FunctionSelectorDialog.select_function(parent=self)

        if selected_function:
            # Add function to list (same logic as Textual TUI)
            new_func_item = (selected_function, {})
            self.functions.append(new_func_item)
            self._update_pattern_data()
            self._populate_function_list()
            self.function_pattern_changed.emit()
            logger.debug(f"Added function: {selected_function.__name__}")
    

    
    def edit_function_code(self):
        """Edit function pattern as code (simple and direct)."""
        logger.debug("Edit function code clicked - opening code editor")

        # Validation guard: Check for empty patterns
        if not self.functions and not self.pattern_data:
            if self.service_adapter:
                self.service_adapter.show_info_dialog("No function pattern to edit. Add functions first.")
            return

        try:
            # Update pattern data first
            self._update_pattern_data()

            # Generate complete Python code with imports
            python_code = self._generate_complete_python_code()

            # Create simple code editor service
            from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService
            editor_service = SimpleCodeEditorService(self)

            # Check if user wants external editor (check environment variable)
            use_external = os.environ.get('OPENHCS_USE_EXTERNAL_EDITOR', '').lower() in ('1', 'true', 'yes')

            # Launch editor with callback and code_type for clean mode toggle
            editor_service.edit_code(
                initial_content=python_code,
                title="Edit Function Pattern",
                callback=self._handle_edited_pattern,
                use_external=use_external,
                code_type='function',
                code_data={'pattern_data': self.pattern_data, 'clean_mode': False}
            )

        except Exception as e:
            logger.error(f"Failed to launch code editor: {e}")
            if self.service_adapter:
                self.service_adapter.show_error_dialog(f"Failed to launch code editor: {str(e)}")

    def _generate_complete_python_code(self) -> str:
        """Generate complete Python code with imports (following debug module approach)."""
        # Use complete function pattern code generation from pickle_to_python
        from openhcs.debug.pickle_to_python import generate_complete_function_pattern_code

        # Disable clean_mode to preserve all parameters when same function appears multiple times
        # This prevents parsing issues when the same function has different parameter sets
        return generate_complete_function_pattern_code(self.pattern_data, clean_mode=False)

    def _handle_edited_pattern(self, edited_code: str) -> None:
        """Handle the edited pattern code from code editor."""
        try:
            # Ensure we have a string
            if not isinstance(edited_code, str):
                logger.error(f"Expected string, got {type(edited_code)}: {edited_code}")
                raise ValueError("Invalid code format received from editor")

            # CRITICAL FIX: Execute code with lazy dataclass constructor patching to preserve None vs concrete distinction
            namespace = {}
            with self._patch_lazy_constructors():
                exec(edited_code, namespace)

            # Get the pattern from the namespace
            if 'pattern' in namespace:
                new_pattern = namespace['pattern']
                self._apply_edited_pattern(new_pattern)
            else:
                raise ValueError("No 'pattern = ...' assignment found in edited code")

        except (SyntaxError, Exception) as e:
            logger.error(f"Failed to parse edited pattern: {e}")
            # Re-raise so the code editor can handle it (keep dialog open, move cursor to error line)
            raise

    def _apply_edited_pattern(self, new_pattern):
        """Apply the edited pattern back to the UI."""
        try:
            if self.is_dict_mode:
                if isinstance(new_pattern, dict):
                    self.pattern_data = new_pattern
                    # Update current channel if it exists in new pattern
                    if self.selected_channel and self.selected_channel in new_pattern:
                        self.functions = self._normalize_function_list(new_pattern[self.selected_channel])
                    else:
                        # Select first channel
                        if new_pattern:
                            self.selected_channel = next(iter(new_pattern))
                            self.functions = self._normalize_function_list(new_pattern[self.selected_channel])
                        else:
                            self.functions = []
                else:
                    raise ValueError("Expected dict pattern for dict mode")
            else:
                if isinstance(new_pattern, list):
                    self.pattern_data = new_pattern
                    self.functions = self._normalize_function_list(new_pattern)
                elif callable(new_pattern):
                    # Single callable: treat as [(callable, {})]
                    self.pattern_data = [(new_pattern, {})]
                    self.functions = [(new_pattern, {})]
                elif isinstance(new_pattern, tuple) and len(new_pattern) == 2 and callable(new_pattern[0]) and isinstance(new_pattern[1], dict):
                    # Single tuple (callable, kwargs): treat as [(callable, kwargs)]
                    self.pattern_data = [new_pattern]
                    self.functions = [new_pattern]
                else:
                    raise ValueError(f"Expected list, callable, or (callable, dict) tuple pattern for list mode, got {type(new_pattern)}")

            # Refresh the UI and notify of changes
            self._populate_function_list()
            self.function_pattern_changed.emit()

            # CRITICAL: Trigger global cross-window refresh for ALL open windows
            # This ensures any window with placeholders (configs, steps, etc.) refreshes
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
            ParameterFormManager.trigger_global_cross_window_refresh()

        except Exception as e:
            if self.service_adapter:
                self.service_adapter.show_error_dialog(f"Failed to apply edited pattern: {str(e)}")

    def _patch_lazy_constructors(self):
        """Context manager that patches lazy dataclass constructors to preserve None vs concrete distinction."""
        from openhcs.introspection import patch_lazy_constructors
        return patch_lazy_constructors()

    def _move_function(self, index, direction):
        """Move function up or down."""
        if 0 <= index < len(self.functions):
            new_index = index + direction
            if 0 <= new_index < len(self.functions):
                # Swap functions
                self.functions[index], self.functions[new_index] = self.functions[new_index], self.functions[index]
                self._update_pattern_data()
                self._populate_function_list()
                self.function_pattern_changed.emit()
    
    def _add_function_at_index(self, index):
        """Add function at specific index (mirrors Textual TUI)."""
        from openhcs.pyqt_gui.dialogs.function_selector_dialog import FunctionSelectorDialog

        # Show function selector dialog (reuses Textual TUI logic)
        selected_function = FunctionSelectorDialog.select_function(parent=self)

        if selected_function:
            # Insert function at specific index (same logic as Textual TUI)
            new_func_item = (selected_function, {})
            self.functions.insert(index, new_func_item)
            self._update_pattern_data()
            self._populate_function_list()
            self.function_pattern_changed.emit()
            logger.debug(f"Added function at index {index}: {selected_function.__name__}")
    
    def _remove_function(self, index):
        """Remove function at index."""
        if 0 <= index < len(self.functions):
            self.functions.pop(index)
            self._update_pattern_data()
            self._populate_function_list()
            self.function_pattern_changed.emit()
    
    def _on_parameter_changed(self, index, param_name, value):
        """Handle parameter change from function pane."""
        if 0 <= index < len(self.functions):
            func, kwargs = self.functions[index]
            kwargs[param_name] = value
            self.functions[index] = (func, kwargs)
            self._update_pattern_data()
            self.function_pattern_changed.emit()
    

    

    
    def get_current_functions(self):
        """Get current function list."""
        return self.functions.copy()

    @property
    def current_pattern(self):
        """Get the current pattern data (for parent widgets to access)."""
        self._update_pattern_data()  # Ensure it's up to date

        # Migration fix: Convert any integer keys to string keys for compatibility
        # with pattern detection system which always uses string component values
        if isinstance(self.pattern_data, dict):
            migrated_pattern = {}
            for key, value in self.pattern_data.items():
                str_key = str(key)
                migrated_pattern[str_key] = value
            return migrated_pattern

        return self.pattern_data
    
    def set_functions(self, functions):
        """Set function list and refresh display."""
        self.functions = functions.copy() if functions else []
        self._update_pattern_data()
        self._populate_function_list()

    def refresh_from_step_context(self) -> None:
        """Refresh group_by and variable_components from step_instance using lazy resolution.

        CRITICAL: This uses the SAME live context collection mechanism as form managers
        to ensure we see live values from other open windows (PipelineConfig editor, etc.).
        """
        if not hasattr(self, 'step_instance') or self.step_instance is None:
            logger.warning("No step_instance available for context refresh")
            return

        from openhcs.config_framework.context_manager import config_context
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

        try:
            # CRITICAL: Collect live context from other open windows using the same mechanism as form managers
            # This ensures we see live PipelineConfig values, not just the saved ones
            live_context = {}

            # Iterate through all active form managers to collect live context
            for manager in ParameterFormManager._active_form_managers:
                # Only collect from managers in the same scope hierarchy
                if hasattr(self, 'scope_id') and hasattr(manager, 'scope_id'):
                    # Check scope visibility (same logic as form managers)
                    if manager.scope_id is None or (self.scope_id and self.scope_id.startswith(manager.scope_id)):
                        # Get user-modified values (concrete, non-None values only)
                        live_values = manager.get_user_modified_values()
                        obj_type = type(manager.object_instance)
                        live_context[obj_type] = live_values

            # Build context stack with live values
            from contextlib import ExitStack
            from openhcs.core.config import PipelineConfig, GlobalPipelineConfig
            import dataclasses

            with ExitStack() as stack:
                # Add GlobalPipelineConfig from live context if available
                if GlobalPipelineConfig in live_context:
                    global_live = live_context[GlobalPipelineConfig]
                    # Reconstruct nested dataclasses from live values
                    from openhcs.config_framework.context_manager import get_base_global_config
                    thread_local_global = get_base_global_config()
                    if thread_local_global and global_live:
                        global_instance = dataclasses.replace(thread_local_global, **global_live)
                        stack.enter_context(config_context(global_instance))

                # Add PipelineConfig from live context if available
                if PipelineConfig in live_context:
                    pipeline_live = live_context[PipelineConfig]
                    if pipeline_live:
                        pipeline_instance = PipelineConfig(**pipeline_live)
                        stack.enter_context(config_context(pipeline_instance))

                # Add step instance
                stack.enter_context(config_context(self.step_instance))

                # Resolve group_by and variable_components with full context stack
                effective_group_by = self.step_instance.processing_config.group_by
                variable_components = self.step_instance.processing_config.variable_components or []

            # Update state
            self.current_group_by = effective_group_by
            self.current_variable_components = variable_components

            # Refresh UI
            self._refresh_component_button()

        except Exception as e:
            logger.error(f"❌ Failed to refresh from step context: {e}", exc_info=True)

    def set_effective_group_by(self, group_by: Optional[GroupBy]) -> None:
        """Accept authoritative GroupBy from parent (step.processing_config) and refresh UI.

        The parent (window) is responsible for providing the correct GroupBy instance
        from the step.processing_config. This method trusts the type and simply
        updates the widget state and refreshes dependent controls.
        """
        self.current_group_by = group_by
        # Update the button text/state immediately
        self._refresh_component_button()

    def _get_component_button_text(self) -> str:
        """Get text for the component selection button (mirrors Textual TUI)."""
        if self.current_group_by is None or self.current_group_by == GroupBy.NONE:
            return "Component: None"

        # Use the existing _get_enum_display_text function for consistent enum display handling
        component_type = _get_enum_display_text(self.current_group_by).title()

        if self.is_dict_mode and self.selected_channel is not None:
            # Try to get metadata name for the selected component
            display_name = self._get_component_display_name(self.selected_channel)
            return f"{component_type}: {display_name}"
        return f"{component_type}: None"

    def _get_component_display_name(self, component_key: str) -> str:
        """Get display name for component key, using metadata if available (mirrors Textual TUI)."""
        orchestrator = self._get_current_orchestrator()
        if orchestrator and self.current_group_by:
            metadata_name = orchestrator.metadata_cache.get_component_metadata(self.current_group_by, component_key)
            if metadata_name:
                return metadata_name
        return component_key

    def _is_component_button_disabled(self) -> bool:
        """Check if component selection button should be disabled (mirrors Textual TUI)."""
        return (
            self.current_group_by is None or
            self.current_group_by == GroupBy.NONE or
            (self.current_variable_components and
             self.current_group_by.value in [vc.value for vc in self.current_variable_components])
        )

    def show_component_selection_dialog(self):
        """Show the component selection dialog (mirrors Textual TUI)."""
        from openhcs.pyqt_gui.dialogs.group_by_selector_dialog import GroupBySelectorDialog

        # Check if component selection is disabled
        if self._is_component_button_disabled():
            logger.debug("Component selection is disabled")
            return

        # Get available components from orchestrator using current group_by - MUST exist, no fallbacks
        orchestrator = self._get_current_orchestrator()

        available_components = orchestrator.get_component_keys(self.current_group_by)
        assert available_components, f"No {self.current_group_by.value} values found in current plate"

        # Get current selection from pattern data (mirrors Textual TUI logic)
        selected_components = self._get_current_component_selection()



        # Show group by selector dialog (reuses Textual TUI logic)
        result = GroupBySelectorDialog.select_components(
            available_components=available_components,
            selected_components=selected_components,
            group_by=self.current_group_by,
            orchestrator=orchestrator,
            parent=self
        )

        if result is not None:
            self._handle_component_selection(result)

    def _get_current_orchestrator(self):
        """Get current orchestrator instance - MUST exist, no fallbacks allowed."""
        # Use stored main window reference to get plate manager
        main_window = self.main_window
        plate_manager_window = main_window.floating_windows['plate_manager']

        # Find the actual plate manager widget
        plate_manager_widget = None
        for child in plate_manager_window.findChildren(QWidget):
            if hasattr(child, 'orchestrators') and hasattr(child, 'selected_plate_path'):
                plate_manager_widget = child
                break

        # Get current plate from plate manager's selection
        current_plate = plate_manager_widget.selected_plate_path
        orchestrator = plate_manager_widget.orchestrators[current_plate]

        # Orchestrator must be initialized
        assert orchestrator.is_initialized(), f"Orchestrator for plate {current_plate} is not initialized"

        return orchestrator

    def _get_current_component_selection(self):
        """Get current component selection from pattern data (mirrors Textual TUI logic)."""
        # If in dict mode, return the keys of the dict as the current selection (sorted)
        if self.is_dict_mode and isinstance(self.pattern_data, dict):
            return sorted(list(self.pattern_data.keys()))

        # If not in dict mode, check the cache (sorted)
        cached_selection = self.component_selections.get(self.current_group_by, [])
        return sorted(cached_selection)

    def _handle_component_selection(self, new_components):
        """Handle component selection result (mirrors Textual TUI)."""
        # Save selection to cache for current group_by
        if self.current_group_by is not None and self.current_group_by != GroupBy.NONE:
            self.component_selections[self.current_group_by] = new_components
            logger.debug(f"Step '{self.step_identifier}': Cached selection for {self.current_group_by.value}: {new_components}")

        # Update pattern structure based on component selection (mirrors Textual TUI)
        self._update_components(new_components)

        # Update component button text and navigation
        self._refresh_component_button()
        logger.debug(f"Updated components: {new_components}")
        
        self.function_pattern_changed.emit()

    def _update_components(self, new_components):
        """Update function pattern structure based on component selection (mirrors Textual TUI)."""
        # Sort new components for consistent ordering
        if new_components:
            new_components = sorted(new_components)

        if not new_components:
            # No components selected - revert to list mode
            if self.is_dict_mode:
                # Save current functions to list mode
                self.pattern_data = self.functions
                self.is_dict_mode = False
                self.selected_channel = None
                logger.debug("Reverted to list mode (no components selected)")
        else:
            # Use component strings directly - no conversion needed
            component_keys = new_components

            # Components selected - ensure dict mode
            if not self.is_dict_mode:
                # Convert to dict mode
                current_functions = self.functions
                self.pattern_data = {component_keys[0]: current_functions}
                self.is_dict_mode = True
                self.selected_channel = component_keys[0]

                # Add other components with empty functions
                for component_key in component_keys[1:]:
                    self.pattern_data[component_key] = []
            else:
                # Already in dict mode - update components
                old_pattern = self.pattern_data.copy() if isinstance(self.pattern_data, dict) else {}

                # Create a persistent storage for deselected components (mirrors Textual TUI)
                if not hasattr(self, '_deselected_components_storage'):
                    self._deselected_components_storage = {}

                # Save currently deselected components to storage
                for old_key, old_functions in old_pattern.items():
                    if old_key not in component_keys:
                        self._deselected_components_storage[old_key] = old_functions
                        logger.debug(f"Saved {len(old_functions)} functions for deselected component {old_key}")

                new_pattern = {}

                # Restore functions for components (from current pattern or storage)
                for component_key in component_keys:
                    if component_key in old_pattern:
                        # Component was already selected - keep its functions
                        new_pattern[component_key] = old_pattern[component_key]
                    elif component_key in self._deselected_components_storage:
                        # Component was previously deselected - restore its functions
                        new_pattern[component_key] = self._deselected_components_storage[component_key]
                        logger.debug(f"Restored {len(new_pattern[component_key])} functions for reselected component {component_key}")
                    else:
                        # New component - start with empty functions
                        new_pattern[component_key] = []

                self.pattern_data = new_pattern

                # Update selected channel if current one is no longer available
                if self.selected_channel not in component_keys:
                    self.selected_channel = component_keys[0]
                    self.functions = new_pattern[self.selected_channel]

        # Update UI to reflect changes
        self._populate_function_list()
        self._update_navigation_buttons()

    def _refresh_component_button(self):
        """Refresh the component button text and state (mirrors Textual TUI)."""
        if hasattr(self, 'component_btn'):
            self.component_btn.setText(self._get_component_button_text())
            self.component_btn.setEnabled(not self._is_component_button_disabled())

        # Also update navigation buttons when component button is refreshed
        self._update_navigation_buttons()



    def _update_navigation_buttons(self):
        """Update visibility of channel navigation buttons (mirrors Textual TUI)."""
        if hasattr(self, 'prev_channel_btn') and hasattr(self, 'next_channel_btn'):
            # Show navigation buttons only in dict mode with multiple channels
            show_nav = (self.is_dict_mode and
                       isinstance(self.pattern_data, dict) and
                       len(self.pattern_data) > 1)

            self.prev_channel_btn.setVisible(show_nav)
            self.next_channel_btn.setVisible(show_nav)

    def _navigate_channel(self, direction: int):
        """Navigate to next/previous channel (with looping, mirrors Textual TUI)."""
        if not self.is_dict_mode or not isinstance(self.pattern_data, dict):
            return

        channels = sorted(self.pattern_data.keys())
        if len(channels) <= 1:
            return

        try:
            current_index = channels.index(self.selected_channel)
            new_index = (current_index + direction) % len(channels)
            new_channel = channels[new_index]

            self._switch_to_channel(new_channel)
            logger.debug(f"Navigated to channel {new_channel}")
        except (ValueError, IndexError):
            logger.warning(f"Failed to navigate channels: current={self.selected_channel}, channels={channels}")

    def _switch_to_channel(self, channel: str):
        """Switch to editing functions for a specific channel (mirrors Textual TUI)."""
        if not self.is_dict_mode:
            return

        # Save current functions first
        old_channel = self.selected_channel
        logger.debug(f"Switching from channel {old_channel} to {channel}")

        self._update_pattern_data()

        # Switch to new channel
        self.selected_channel = channel
        if isinstance(self.pattern_data, dict):
            self.functions = self.pattern_data.get(channel, [])
            logger.debug(f"Loaded {len(self.functions)} functions for channel {channel}")
        else:
            self.functions = []

        # Update UI
        self._refresh_component_button()
        self._populate_function_list()

    def _update_pattern_data(self):
        """Update pattern_data based on current functions and mode (mirrors Textual TUI)."""
        if self.is_dict_mode and self.selected_channel is not None:
            # Save current functions to the selected channel
            if not isinstance(self.pattern_data, dict):
                self.pattern_data = {}
            logger.debug(f"Saving {len(self.functions)} functions to channel {self.selected_channel}")
            self.pattern_data[self.selected_channel] = self.functions.copy()
        else:
            # List mode - pattern_data is just the functions list
            self.pattern_data = self.functions
