"""
Function List Editor Widget for PyQt6 GUI.

Mirrors the Textual TUI FunctionListEditorWidget with sophisticated parameter forms.
Displays a scrollable list of function panes with Add/Load/Save/Code controls.
"""

import logging
import os
from typing import List, Union, Dict, Optional, Any

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel, 
    QScrollArea
)
from PyQt6.QtCore import Qt, pyqtSignal

from pyqt_formgen.protocols import (
    get_function_registry,
    get_component_selection_provider,
    get_function_selection_provider,
)
from pyqt_formgen.services.pattern_data_manager import PatternDataManager
from pyqt_formgen.widgets.function_pane import FunctionPaneWidget
from objectstate import ObjectStateRegistry
from pyqt_formgen.theming import ColorScheme
from pyqt_formgen.forms.widget_strategies import _get_enum_display_text

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
                 step_identifier: str = None, service_adapter=None, color_scheme: Optional[ColorScheme] = None,
                 step_instance=None, scope_id: Optional[str] = None, parent=None):
        super().__init__(parent)

        # Initialize color scheme
        self.color_scheme = color_scheme or ColorScheme()

        # Initialize services (reuse existing business logic)
        self.function_registry = get_function_registry()
        self.component_selection_provider = get_component_selection_provider()
        self.function_selection_provider = get_function_selection_provider()
        if self.component_selection_provider is None:
            raise RuntimeError("No component selection provider registered. Call register_component_selection_provider(...).")
        if self.function_selection_provider is None:
            raise RuntimeError("No function selection provider registered. Call register_function_selection_provider(...).")
        self._groupby_enum = self.component_selection_provider.get_groupby_enum()
        self.data_manager = PatternDataManager()
        self.service_adapter = service_adapter

        # Step identifier for cache isolation
        self.step_identifier = step_identifier or f"widget_{id(self)}"

        # CRITICAL: Store step instance for context hierarchy (Function → Step → Pipeline → Global)
        self.step_instance = step_instance

        # CRITICAL: Store scope_id for cross-window live context updates
        self.scope_id = scope_id

        # Scope color scheme for styling newly created panes
        self._scope_color_scheme = None

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

        # CRITICAL: Subscribe to step's ObjectState resolved changes for cross-window updates
        # When PipelineConfig changes group_by, the step's resolved value changes via inheritance,
        # and we need to refresh the component button to reflect the new value
        self._subscribe_to_step_state_changes()

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

        # Store as instance attribute for scope accent styling
        self.header_label = QLabel("Functions")
        self.header_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)}; font-weight: bold; font-size: 14px;")
        header_layout.addWidget(self.header_label)
        
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
        # NOTE: We do NOT destroy function ObjectStates or clear scope tokens here.
        # - For code mode: _update_function_object_states() updates existing ObjectStates
        #   with new kwargs BEFORE this method is called, preserving dirty detection.
        # - FunctionPaneWidget.create_parameter_form() reuses existing ObjectStates
        #   (line 297-302 in function_pane.py) if they exist.
        # - ObjectStates for removed functions are cleaned up when their widgets are destroyed.
        # - Scope tokens must persist so build_scope_id returns the same scope_id for
        #   the same function object, allowing ObjectState lookup to succeed.

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

                # Apply scope color scheme to new pane (for accent colors)
                if self._scope_color_scheme:
                    logger.info(f"🎨 Applying scope_color_scheme to pane {i}")
                    pane.set_scope_color_scheme(self._scope_color_scheme)
                else:
                    logger.info(f"🎨 No scope_color_scheme set on FunctionListEditorWidget, pane {i} gets no styling")

                # CRITICAL FIX: Apply initial enabled styling for function panes
                # This ensures that when the function pattern editor opens, disabled functions
                # show the correct dimmed styling immediately, not just after toggling
                if hasattr(pane, 'form_manager') and pane.form_manager is not None:
                    # Use QTimer to ensure this runs after the widget is fully constructed
                    from PyQt6.QtCore import QTimer
                    QTimer.singleShot(0, lambda p=pane: self._apply_initial_enabled_styling_to_pane(p))

        # Apply scope styling to all child widgets (GroupBoxWithHelp, HelpButton, etc.)
        # This must be done AFTER all panes are created so findChildren() finds them all
        if self._scope_color_scheme:
            # Apply immediately for sync-created widgets
            self._apply_scope_styling_to_children(self._scope_color_scheme)

            # CRITICAL: Register callback on each pane's form_manager for async-created widgets
            # This hooks into FormBuildOrchestrator's async completion system properly
            for pane in self.function_panes:
                if hasattr(pane, 'form_manager') and pane.form_manager is not None:
                    # Capture scheme in closure
                    scheme = self._scope_color_scheme
                    pane.form_manager._on_build_complete_callbacks.append(
                        lambda s=scheme: self._apply_scope_styling_to_children(s)
                    )

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
        # Show function selector dialog via provider
        selected_function = self.function_selection_provider.select_function(parent=self)

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
            from pyqt_formgen.widgets.editors.simple_code_editor import SimpleCodeEditorService
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
        # Use complete function pattern code generation from registered provider
        from pyqt_formgen.protocols import get_codegen_provider
        provider = get_codegen_provider()
        if provider is None:
            raise RuntimeError("No codegen provider registered. Call register_codegen_provider(...).")

        # Disable clean_mode to preserve all parameters when same function appears multiple times
        # This prevents parsing issues when the same function has different parameter sets
        return provider.generate_complete_function_pattern_code(self.pattern_data, clean_mode=False)

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
        from objectstate import ObjectStateRegistry

        # ATOMIC: Coalesce all register + edit snapshots into single "code edit" snapshot
        # Without this, code mode creates multiple snapshots (one per function register + edit func)
        with ObjectStateRegistry.atomic("code edit"):
            self._apply_edited_pattern_internal(new_pattern)

    def _apply_edited_pattern_internal(self, new_pattern):
        """Internal implementation of apply_edited_pattern (wrapped in atomic block)."""
        try:
            # Get the new function list BEFORE updating self.functions
            if self.is_dict_mode:
                if isinstance(new_pattern, dict):
                    if self.selected_channel and self.selected_channel in new_pattern:
                        new_functions = self._normalize_function_list(new_pattern[self.selected_channel])
                    elif new_pattern:
                        new_channel = next(iter(new_pattern))
                        new_functions = self._normalize_function_list(new_pattern[new_channel])
                    else:
                        new_functions = []
                else:
                    raise ValueError("Expected dict pattern for dict mode")
            else:
                if isinstance(new_pattern, list):
                    new_functions = self._normalize_function_list(new_pattern)
                elif callable(new_pattern):
                    new_functions = [(new_pattern, {})]
                elif isinstance(new_pattern, tuple) and len(new_pattern) == 2 and callable(new_pattern[0]) and isinstance(new_pattern[1], dict):
                    new_functions = [new_pattern]
                else:
                    raise ValueError(f"Expected list, callable, or (callable, dict) tuple pattern for list mode, got {type(new_pattern)}")

            # CRITICAL FIX: Update existing function ObjectStates with new kwargs BEFORE
            # creating new widgets. This preserves dirty detection - the ObjectState's
            # saved baseline stays the same, only the current values change.
            self._update_function_object_states(self.functions, new_functions)

            # Now update pattern_data and functions
            if self.is_dict_mode:
                self.pattern_data = new_pattern
                if self.selected_channel and self.selected_channel in new_pattern:
                    self.functions = new_functions
                elif new_pattern:
                    self.selected_channel = next(iter(new_pattern))
                    self.functions = new_functions
                else:
                    self.functions = []
            else:
                self.pattern_data = new_pattern if isinstance(new_pattern, list) else new_functions
                self.functions = new_functions

            # Refresh the UI and notify of changes
            # NOTE: _populate_function_list will REUSE ObjectStates that we just updated
            self._populate_function_list()
            self.function_pattern_changed.emit()

            # CRITICAL: Trigger global cross-window refresh for ALL open windows
            # This ensures any window with placeholders (configs, steps, etc.) refreshes
            ObjectStateRegistry.increment_token()

        except Exception as e:
            if self.service_adapter:
                self.service_adapter.show_error_dialog(f"Failed to apply edited pattern: {str(e)}")

    def _update_function_object_states(self, old_functions: List, new_functions: List) -> None:
        """Update existing function ObjectStates with new kwargs from code mode edit.

        This is CRITICAL for dirty detection: instead of destroying and recreating
        ObjectStates (which resets the baseline), we UPDATE existing ones so the
        saved baseline is preserved and changes are detected as dirty.

        Args:
            old_functions: Previous function list [(func, kwargs), ...]
            new_functions: New function list from code mode edit
        """
        if not self.scope_id:
            return

        from objectstate import ObjectStateRegistry
        from pyqt_formgen.services.scope_token_service import ScopeTokenService

        parent_scope = str(self.scope_id)

        # Build mapping of old function scope_ids to their ObjectStates
        # We match by function identity at the same index position
        for i, (old_func, old_kwargs) in enumerate(old_functions):
            if i >= len(new_functions):
                # This function was removed - let _populate_function_list handle cleanup
                continue

            new_func, new_kwargs = new_functions[i]

            # Only update if same function at same index (function identity match)
            if old_func is not new_func:
                # Different function - ObjectState will be recreated, can't update
                continue

            # Find the ObjectState for this function
            # The scope_id is built from step_scope::func_N
            # We need to find the existing ObjectState
            func_scope_id = ScopeTokenService.build_scope_id(parent_scope, old_func)
            state = ObjectStateRegistry.get_by_scope(func_scope_id)

            if state is None:
                # No ObjectState exists yet - will be created by FunctionPaneWidget
                continue

            # Update each kwarg that changed
            for param_name, new_value in new_kwargs.items():
                old_value = old_kwargs.get(param_name)
                if old_value != new_value:
                    # Update the parameter - this triggers dirty detection
                    if param_name in state.parameters:
                        state.update_parameter(param_name, new_value)
                        logger.debug(f"🔧 Code mode: Updated {func_scope_id}.{param_name}: {old_value} → {new_value}")

            # Also handle kwargs that were removed (set to None/default)
            for param_name in old_kwargs:
                if param_name not in new_kwargs and param_name in state.parameters:
                    # Kwarg was removed - reset to None (inherit from context)
                    state.update_parameter(param_name, None)
                    logger.debug(f"🔧 Code mode: Reset {func_scope_id}.{param_name} to None (removed from kwargs)")

    def _patch_lazy_constructors(self):
        """Context manager that patches lazy dataclass constructors to preserve None vs concrete distinction."""
        from objectstate import patch_lazy_constructors
        return patch_lazy_constructors()

    def _move_function(self, index, direction):
        """Move function up or down.

        CRITICAL: Does NOT recreate widgets - just reorders existing panes in layout.
        This preserves flash registrations and avoids RuntimeError from deleted widgets.
        """
        if 0 <= index < len(self.functions):
            new_index = index + direction
            if 0 <= new_index < len(self.functions):
                # Swap functions in data
                self.functions[index], self.functions[new_index] = self.functions[new_index], self.functions[index]
                self._update_pattern_data()
                # Reorder existing panes (NOT recreate) - preserves flash registrations
                self._reorder_function_panes(index, new_index)
                self.function_pattern_changed.emit()

    def _reorder_function_panes(self, old_index: int, new_index: int) -> None:
        """Reorder existing panes in layout without recreating them.

        This preserves widget instances and their flash registrations.
        Only the layout order and pane indices are updated.
        """
        if not self.function_panes:
            return

        # Swap panes in our tracking list
        self.function_panes[old_index], self.function_panes[new_index] = \
            self.function_panes[new_index], self.function_panes[old_index]

        # Update indices on the panes
        for i, pane in enumerate(self.function_panes):
            pane.index = i

        # Reorder widgets in layout by removing and re-adding in correct order
        # First remove all from layout (but don't delete them)
        for pane in self.function_panes:
            self.function_layout.removeWidget(pane)

        # Re-add in correct order
        for pane in self.function_panes:
            self.function_layout.addWidget(pane)
    
    def _add_function_at_index(self, index):
        """Add function at specific index (mirrors Textual TUI)."""
        # Show function selector dialog via provider
        selected_function = self.function_selection_provider.select_function(parent=self)

        if selected_function:
            # Insert function at specific index (same logic as Textual TUI)
            new_func_item = (selected_function, {})
            self.functions.insert(index, new_func_item)
            self._update_pattern_data()
            self._populate_function_list()
            self.function_pattern_changed.emit()
            logger.debug(f"Added function at index {index}: {selected_function.__name__}")
    
    def _remove_function(self, index: int) -> None:
        """Remove function at index."""
        if 0 <= index < len(self.functions):
            func, _kwargs = self.functions[index]

            # Unregister ObjectState before removal
            if self.scope_id:
                from objectstate import ObjectStateRegistry
                from pyqt_formgen.services.scope_token_service import ScopeTokenService
                scope_id = ScopeTokenService.build_scope_id(self.scope_id, func)
                existing = ObjectStateRegistry.get_by_scope(scope_id)
                if existing:
                    ObjectStateRegistry.unregister(existing)

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

    def set_scope_color_scheme(self, scheme) -> None:
        """Set scope color scheme for styling function panes.

        Called by parent window after scope styling is initialized.
        Stores scheme for newly created panes and applies to existing ones.
        Also applies styling to all child GroupBoxWithHelp and HelpButton widgets.
        """
        logger.info(f"🎨 FunctionListEditorWidget.set_scope_color_scheme called with scheme={scheme}, panes={len(self.function_panes)}")
        self._scope_color_scheme = scheme

        # Apply to all existing panes (title color)
        for pane in self.function_panes:
            pane.set_scope_color_scheme(scheme)

        # Apply scope styling to all child widgets (GroupBoxWithHelp, HelpButton, etc.)
        self._apply_scope_styling_to_children(scheme)

    def _apply_scope_styling_to_children(self, scheme) -> None:
        """Apply scope styling to all child widgets that need it.

        This mirrors the logic in base_form_dialog._apply_accent_to_help_buttons().
        """
        if not scheme:
            return

        from pyqt_formgen.widgets.shared.clickable_help_components import HelpButton, HelpIndicator, GroupBoxWithHelp
        from pyqt_formgen.widgets.shared.scope_color_utils import tint_color_perceptual

        # Compute accent color from scheme (same logic as ScopedBorderMixin.get_scope_accent_color)
        layers = getattr(scheme, 'step_border_layers', None)
        if layers:
            _, tint_idx, _ = (layers[0] + ("solid",))[:3]
            accent_color = tint_color_perceptual(scheme.base_color_rgb, tint_idx).darker(120)
        else:
            accent_color = tint_color_perceptual(scheme.base_color_rgb, 0).darker(120)

        # Apply to all HelpButtons
        help_btns = self.findChildren(HelpButton)
        logger.info(f"🎨 _apply_scope_styling_to_children: found {len(help_btns)} HelpButtons")
        for help_btn in help_btns:
            help_btn.set_scope_accent_color(accent_color)

        # Apply to all HelpIndicators
        help_indicators = self.findChildren(HelpIndicator)
        logger.info(f"🎨 _apply_scope_styling_to_children: found {len(help_indicators)} HelpIndicators")
        for help_indicator in help_indicators:
            help_indicator.set_scope_accent_color(accent_color)

        # Apply to all GroupBoxWithHelp (scope border pattern)
        groupboxes = self.findChildren(GroupBoxWithHelp)
        logger.info(f"🎨 _apply_scope_styling_to_children: found {len(groupboxes)} GroupBoxWithHelp")
        for groupbox in groupboxes:
            groupbox.set_scope_color_scheme(scheme)

    def refresh_from_step_context(self) -> None:
        """Refresh group_by and variable_components from ObjectState's LIVE values.

        CRITICAL: Uses ObjectState's get_resolved_value() to get LIVE form values,
        not saved step_instance values. This ensures the function pattern editor sees
        the same group_by value that the step editor form shows.
        """
        from objectstate import ObjectStateRegistry

        try:
            # Get ObjectState for this step from registry
            my_scope = getattr(self, 'scope_id', '') or ''
            state = ObjectStateRegistry.get_by_scope(my_scope)

            logger.info(f"🔍 FUNC_EDITOR refresh_from_step_context: my_scope={my_scope!r}, state={state is not None}")

            if state:
                # Use LIVE resolved values from ObjectState (includes unsaved form changes)
                effective_group_by = state.get_resolved_value('processing_config.group_by')
                variable_components = state.get_resolved_value('processing_config.variable_components') or []
                logger.info(f"🔍 FUNC_EDITOR: Got LIVE values from ObjectState: group_by={effective_group_by}, current={self.current_group_by}")
            else:
                # Fallback to step_instance if no ObjectState (shouldn't happen in normal use)
                logger.warning(f"No ObjectState for scope {my_scope}, falling back to step_instance")
                if not hasattr(self, 'step_instance') or self.step_instance is None:
                    logger.warning("No step_instance available for context refresh")
                    return

                from objectstate import build_context_stack
                ancestor_objects = ObjectStateRegistry.get_ancestor_objects(my_scope)
                stack = build_context_stack(
                    object_instance=self.step_instance,
                    ancestor_objects=ancestor_objects,
                )
                with stack:
                    effective_group_by = self.step_instance.processing_config.group_by
                    variable_components = self.step_instance.processing_config.variable_components or []

            # Update state
            self.current_group_by = effective_group_by
            self.current_variable_components = variable_components

            # Refresh UI
            self._refresh_component_button()

        except Exception as e:
            logger.error(f"❌ Failed to refresh from step context: {e}", exc_info=True)

    def _subscribe_to_step_state_changes(self) -> None:
        """Subscribe to step's ObjectState for resolved value changes.

        CRITICAL: When PipelineConfig's group_by changes, the step's resolved group_by
        changes via inheritance. We need to refresh the component button to reflect this.
        This is the proper cross-window update mechanism - subscribe to ObjectState,
        not to form_manager signals (which only fire for direct edits in the same form).
        """
        if not self.scope_id:
            logger.debug("No scope_id, skipping ObjectState subscription")
            return

        state = ObjectStateRegistry.get_by_scope(self.scope_id)
        if not state:
            logger.warning(f"No ObjectState for scope {self.scope_id}, skipping subscription")
            return

        def on_resolved_changed(changed_paths: set) -> None:
            """Called when step's resolved values change."""
            # Check if group_by or variable_components changed
            relevant_paths = {'processing_config.group_by', 'processing_config.variable_components'}
            if changed_paths & relevant_paths:
                logger.info(f"🔔 FUNC_EDITOR: ObjectState resolved change detected: {changed_paths & relevant_paths}")
                self.refresh_from_step_context()

        state.on_resolved_changed(on_resolved_changed)
        # Store callback reference for cleanup
        self._resolved_change_callback = on_resolved_changed
        self._subscribed_state = state
        logger.info(f"🔔 FUNC_EDITOR: Subscribed to ObjectState resolved changes for scope {self.scope_id}")

        # Cleanup on widget destruction
        def cleanup_subscription():
            if hasattr(self, '_resolved_change_callback') and hasattr(self, '_subscribed_state'):
                self._subscribed_state.off_resolved_changed(self._resolved_change_callback)
                logger.debug(f"🔔 FUNC_EDITOR: Unsubscribed from ObjectState on destruction")
        self.destroyed.connect(cleanup_subscription)

    def set_effective_group_by(self, group_by: Optional[Any]) -> None:
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
        if self.current_group_by is None or self.current_group_by == self._groupby_enum.NONE:
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
        if self.current_group_by:
            metadata_name = self.component_selection_provider.get_component_display_name(
                self.current_group_by, component_key
            )
            if metadata_name:
                return metadata_name
        return component_key

    def _is_component_button_disabled(self) -> bool:
        """Check if component selection button should be disabled (mirrors Textual TUI)."""
        return (
            self.current_group_by is None or
            self.current_group_by == self._groupby_enum.NONE or
            (self.current_variable_components and
             self.current_group_by.value in [vc.value for vc in self.current_variable_components])
        )

    def show_component_selection_dialog(self):
        """Show the component selection dialog (mirrors Textual TUI)."""
        # Check if component selection is disabled
        if self._is_component_button_disabled():
            logger.debug("Component selection is disabled")
            return

        # Get available components from provider
        available_components = self.component_selection_provider.get_component_keys(self.current_group_by)
        assert available_components, f"No {self.current_group_by} values found in current context"

        # Get current selection from pattern data (mirrors Textual TUI logic)
        selected_components = self._get_current_component_selection()

        # Show provider selection UI
        result = self.component_selection_provider.select_components(
            available_components=available_components,
            selected_components=selected_components,
            group_by=self.current_group_by,
            parent=self,
        )

        if result is not None:
            self._handle_component_selection(result)

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
        if self.current_group_by is not None and self.current_group_by != self._groupby_enum.NONE:
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
            new_text = self._get_component_button_text()
            old_text = self.component_btn.text()
            logger.info(f"🔄 _refresh_component_button: old={old_text!r}, new={new_text!r}, group_by={self.current_group_by}")
            self.component_btn.setText(new_text)
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
            # CRITICAL: Create a NEW dict so ObjectState equality check detects changes
            # If we modify the same dict object, current_value == value is always True
            old_pattern = self.pattern_data if isinstance(self.pattern_data, dict) else {}
            new_pattern = dict(old_pattern)  # Shallow copy of dict
            new_pattern[self.selected_channel] = self.functions.copy()
            self.pattern_data = new_pattern
            logger.debug(f"Saving {len(self.functions)} functions to channel {self.selected_channel}")
        else:
            # List mode - pattern_data is a COPY of functions list
            # CRITICAL: Must be a copy so ObjectState equality check detects changes
            self.pattern_data = self.functions.copy()
