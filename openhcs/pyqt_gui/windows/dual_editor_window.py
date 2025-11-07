"""
Dual Editor Window for PyQt6

Step and function editing dialog with tabbed interface.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
from typing import Optional, Callable, Dict, List

from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QTabWidget, QWidget, QStackedWidget
)
from PyQt6.QtCore import pyqtSignal, Qt
from PyQt6.QtGui import QFont

from openhcs.core.steps.function_step import FunctionStep
from openhcs.constants.constants import GroupBy
from openhcs.ui.shared.pattern_data_manager import PatternDataManager

from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.windows.base_form_dialog import BaseFormDialog
from typing import List
logger = logging.getLogger(__name__)


class DualEditorWindow(BaseFormDialog):
    """
    PyQt6 Multi-Tab Parameter Editor Window.

    Generic parameter editing dialog with inheritance hierarchy-based tabbed interface.
    Creates one tab per class in the inheritance hierarchy, showing parameters specific
    to each class level. Preserves all business logic from Textual version with clean PyQt6 UI.

    Inherits from BaseFormDialog to automatically handle unregistration from
    cross-window placeholder updates when the dialog closes.
    """

    # Signals
    step_saved = pyqtSignal(object)  # FunctionStep
    step_cancelled = pyqtSignal()
    changes_detected = pyqtSignal(bool)  # has_changes
    
    def __init__(self, step_data: Optional[FunctionStep] = None, is_new: bool = False,
                 on_save_callback: Optional[Callable] = None, color_scheme: Optional[PyQt6ColorScheme] = None,
                 orchestrator=None, gui_config=None, parent=None):
        """
        Initialize the dual editor window.

        Args:
        if self.tab_bar is not None:
            step_data: FunctionStep to edit (None for new step)
            is_new: Whether this is a new step
            on_save_callback: Function to call when step is saved
            color_scheme: Color scheme for UI components
            orchestrator: Orchestrator instance for context management
            gui_config: Optional GUI configuration passed from PipelineEditor
            parent: Parent widget
        """
        super().__init__(parent)

        # Make window non-modal (like plate manager and pipeline editor)
        self.setModal(False)

        # Initialize color scheme and style generator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)
        self.gui_config = gui_config

        # Business logic state (extracted from Textual version)
        self.is_new = is_new
        self.on_save_callback = on_save_callback
        self.orchestrator = orchestrator  # Store orchestrator for context management
        
        # Pattern management (extracted from Textual version)
        self.pattern_manager = PatternDataManager()

        # Store original step reference (never modified)
        # CRITICAL: For new steps, this must be None until first save
        self.original_step_reference = None if is_new else step_data

        if step_data:
            # CRITICAL FIX: Work on a copy to prevent immediate modification of original
            self.editing_step = self._clone_step(step_data)
            self.original_step = self._clone_step(step_data)
        else:
            self.editing_step = self._create_new_step()
            self.original_step = None
        
        # Change tracking
        self.has_changes = False
        self.current_tab = "step"
        
        # UI components
        self.tab_widget: Optional[QTabWidget] = None
        self.parameter_editors: Dict[str, QWidget] = {}  # Map tab titles to editor widgets
        self.class_hierarchy: List = []  # Store inheritance hierarchy info
        
        # Setup UI
        self.setup_ui()
        self.setup_connections()
        
        logger.debug(f"Dual editor window initialized (new={is_new})")

    def set_original_step_for_change_detection(self):
        """Set the original step for change detection. Must be called within proper context."""
        # Original step is already set in __init__ when working on a copy
        # This method is kept for compatibility but no longer needed
        pass

    def setup_ui(self):
        """Setup the user interface."""
        self._update_window_title()
        self.resize(1000, 700)

        layout = QVBoxLayout(self)
        layout.setSpacing(5)
        layout.setContentsMargins(5, 5, 5, 5)

        # Single row: tabs + title + status + buttons
        tab_row = QHBoxLayout()
        tab_row.setContentsMargins(5, 5, 5, 5)
        tab_row.setSpacing(10)

        # Tab widget (tabs on the left)
        self.tab_widget = QTabWidget()
        self.tab_bar = self.tab_widget.tabBar()
        self.tab_bar.setExpanding(False)
        self.tab_bar.setUsesScrollButtons(False)
        tab_row.addWidget(self.tab_bar, 0)

        # Title label
        self.header_label = QLabel()
        self.header_label.setFont(QFont("Arial", 14, QFont.Weight.Bold))
        self.header_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
        from PyQt6.QtWidgets import QSizePolicy
        self.header_label.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Preferred)
        tab_row.addWidget(self.header_label, 1)

        tab_row.addStretch()

        # Status indicator
        self.changes_label = QLabel("")
        self.changes_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.status_warning)}; font-style: italic;")
        tab_row.addWidget(self.changes_label)

        # Get centralized button styles
        button_styles = self.style_generator.generate_config_button_styles()

        # Cancel button
        cancel_button = QPushButton("Cancel")
        cancel_button.setFixedHeight(28)
        cancel_button.setMinimumWidth(70)
        cancel_button.clicked.connect(self.cancel_edit)
        cancel_button.setStyleSheet(button_styles["cancel"])
        tab_row.addWidget(cancel_button)

        # Save/Create button
        self.save_button = QPushButton()
        self._update_save_button_text()
        self.save_button.setFixedHeight(28)
        self.save_button.setMinimumWidth(70)
        self.save_button.setEnabled(False)
        self._setup_save_button(self.save_button, self.save_edit)
        self.save_button.setStyleSheet(button_styles["save"] + f"""
            QPushButton:disabled {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                color: {self.color_scheme.to_hex(self.color_scheme.border_light)};
                border: none;
            }}
        """)
        tab_row.addWidget(self.save_button)

        layout.addLayout(tab_row)

        # Style the tab bar
        self.tab_bar.setStyleSheet(f"""
            QTabBar::tab {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.input_bg)};
                color: white;
                padding: 8px 16px;
                margin-right: 2px;
                border-top-left-radius: 4px;
                border-top-right-radius: 4px;
                border: none;
            }}
            QTabBar::tab:selected {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
            }}
            QTabBar::tab:hover {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.button_hover_bg)};
            }}
        """)

        # Create tabs (this adds content to the tab widget)
        self.create_step_tab()
        self.create_function_tab()

        # Add the tab widget's content area (stacked widget) below the tab row
        # The tab bar is already in tab_row, so we only add the content pane here
        content_container = QWidget()
        content_layout = QVBoxLayout(content_container)
        content_layout.setContentsMargins(0, 0, 0, 0)
        content_layout.setSpacing(0)

        # Get the stacked widget from the tab widget and add it
        stacked_widget = self.tab_widget.findChild(QStackedWidget)
        if stacked_widget:
            content_layout.addWidget(stacked_widget)

        layout.addWidget(content_container)

        # Apply centralized styling
        self.setStyleSheet(self.style_generator.generate_config_window_style())

    def _update_window_title(self):
        title = "New Step" if getattr(self, 'is_new', False) else f"Edit Step: {getattr(self.editing_step, 'name', 'Unknown')}"
        self.setWindowTitle(title)
        if hasattr(self, 'header_label'):
            self.header_label.setText(title)

    def _update_save_button_text(self):
        if hasattr(self, 'save_button'):
            new_text = "Create" if getattr(self, 'is_new', False) else "Save"
            logger.info(f"🔘 Updating save button text: is_new={self.is_new} → '{new_text}'")
            self.save_button.setText(new_text)
    
    def create_step_tab(self):
        """Create the step settings tab (using dedicated widget)."""
        from openhcs.pyqt_gui.widgets.step_parameter_editor import StepParameterEditorWidget
        from openhcs.config_framework.context_manager import config_context

        # Create step parameter editor widget with proper nested context
        # Step must be nested: GlobalPipelineConfig -> PipelineConfig -> Step
        # CRITICAL: Pass orchestrator's plate_path as scope_id to limit cross-window updates to same orchestrator
        scope_id = str(self.orchestrator.plate_path) if self.orchestrator else None
        with config_context(self.orchestrator.pipeline_config):  # Pipeline level
            with config_context(self.editing_step):              # Step level
                self.step_editor = StepParameterEditorWidget(
                    self.editing_step,
                    service_adapter=None,
                    color_scheme=self.color_scheme,
                    pipeline_config=self.orchestrator.pipeline_config,
                    scope_id=scope_id
                )

        # Connect parameter changes - use form manager signal for immediate response
        self.step_editor.form_manager.parameter_changed.connect(self.on_form_parameter_changed)

        self.tab_widget.addTab(self.step_editor, "Step Settings")

    def create_function_tab(self):
        """Create the function pattern tab (using dedicated widget)."""
        from openhcs.pyqt_gui.widgets.function_list_editor import FunctionListEditorWidget

        # Convert step func to function list format
        initial_functions = self._convert_step_func_to_list()

        # Create function list editor widget (mirrors Textual TUI)
        step_id = getattr(self.editing_step, 'name', 'unknown_step')
        self.func_editor = FunctionListEditorWidget(
            initial_functions=initial_functions,
            step_identifier=step_id,
            service_adapter=None
        )

        # Store main window reference for orchestrator access (find it through parent chain)
        main_window = self._find_main_window()
        if main_window:
            self.func_editor.main_window = main_window

        # SINGLE SOURCE OF TRUTH: Initialize function editor state from step
        self._sync_function_editor_from_step()

        # Connect function pattern changes
        self.func_editor.function_pattern_changed.connect(self._on_function_pattern_changed)

        self.tab_widget.addTab(self.func_editor, "Function Pattern")

    def _on_function_pattern_changed(self):
        """Handle function pattern changes from function editor."""
        # Update step func from function editor - use current_pattern to get full pattern data
        current_pattern = self.func_editor.current_pattern

        # CRITICAL FIX: Use fresh imports to avoid unpicklable registry wrappers
        if callable(current_pattern) and hasattr(current_pattern, '__module__'):
            try:
                import importlib
                module = importlib.import_module(current_pattern.__module__)
                current_pattern = getattr(module, current_pattern.__name__)
            except Exception:
                pass  # Use original if refresh fails

        self.editing_step.func = current_pattern
        self.detect_changes()
        logger.debug(f"Function pattern changed: {current_pattern}")





    def setup_connections(self):
        """Setup signal/slot connections."""
        # Tab change tracking
        self.tab_widget.currentChanged.connect(self.on_tab_changed)

        # Change detection
        self.changes_detected.connect(self.on_changes_detected)

    def _convert_step_func_to_list(self):
        """Convert step func to initial pattern format for function list editor."""
        if not hasattr(self.editing_step, 'func') or not self.editing_step.func:
            return []

        # Return the step func directly - the function list editor will handle the conversion
        result = self.editing_step.func
        print(f"🔍 DUAL EDITOR _convert_step_func_to_list: returning {result}")
        return result

    def _sync_function_editor_from_step(self):
        """
        SINGLE SOURCE OF TRUTH: Sync function editor state from step editor's CURRENT form values.

        CRITICAL: This reads from the form manager's current values (live context), NOT from self.editing_step.
        The form manager's values are the live working copy that updates as the user types.
        self.editing_step only gets updated when the user saves.

        This method extracts all step configuration that affects the function editor
        and updates it. Call this whenever ANY step parameter changes to ensure
        the function editor stays in sync.

        If the step structure changes in the future, only this method needs updating.
        """
        logger.info("🔄 _sync_function_editor_from_step called")

        # Guard: Only sync if function editor exists
        if not hasattr(self, 'func_editor') or self.func_editor is None:
            logger.info("⏭️  Function editor doesn't exist yet, skipping sync")
            return

        # CRITICAL: Read from form manager's current values (live context), not from self.editing_step
        # The form manager updates its self.parameters dict as the user types, but doesn't update
        # the dataclass instance until save. So we need to read from the form's current state.
        #
        # CRITICAL: Also apply lazy resolution to handle None values (inherit from pipeline config)
        from openhcs.config_framework.context_manager import config_context

        try:
            # Get current values from step editor form (includes nested dataclasses)
            current_values = self.step_editor.form_manager.get_current_values()
            processing_config = current_values.get('processing_config')

            if processing_config:
                # CRITICAL: Apply config_context to enable lazy resolution for None values
                # When group_by is None, it should inherit from pipeline config
                # We need to create a temporary step-like object with the live processing_config
                # so that lazy resolution can work properly

                # Create a simple object that mimics the step's structure for lazy resolution
                class TempStep:
                    def __init__(self, processing_config):
                        self.processing_config = processing_config

                temp_step = TempStep(processing_config)

                with config_context(self.orchestrator.pipeline_config):
                    with config_context(temp_step):
                        # Read from the live processing_config with lazy resolution
                        # If group_by is None, this will resolve to pipeline config's value
                        effective_group_by = processing_config.group_by
                        variable_components = processing_config.variable_components or []
                        logger.info(f"🔍 Live form values (lazy-resolved): group_by={effective_group_by}, variable_components={variable_components}")
            else:
                # Fallback: processing_config not in current values (shouldn't happen)
                logger.warning("⚠️  processing_config not found in current form values, using defaults")
                effective_group_by = None
                variable_components = []
        except Exception as e:
            logger.error(f"❌ Failed to read live form values: {e}", exc_info=True)
            effective_group_by = None
            variable_components = []

        # Update function editor with extracted values
        logger.info(f"📤 Updating function editor: group_by={effective_group_by}, variable_components={variable_components}")
        self.func_editor.set_effective_group_by(effective_group_by)
        self.func_editor.current_variable_components = variable_components
        self.func_editor._refresh_component_button()

        logger.info(f"✅ Synced function editor: group_by={effective_group_by}, variable_components={variable_components}")



    def _find_main_window(self):
        """Find the main window through the parent chain."""
        try:
            # Navigate up the parent chain to find OpenHCSMainWindow
            current = self.parent()
            while current:
                # Check if this is the main window (has floating_windows attribute)
                if hasattr(current, 'floating_windows') and hasattr(current, 'service_adapter'):
                    logger.debug(f"Found main window: {type(current).__name__}")
                    return current
                current = current.parent()

            logger.warning("Could not find main window in parent chain")
            return None

        except Exception as e:
            logger.error(f"Error finding main window: {e}")
            return None

    def _get_current_plate_from_pipeline_editor(self):
        """Get current plate from pipeline editor (mirrors Textual TUI pattern)."""
        try:
            # Navigate up to find pipeline editor widget
            current = self.parent()
            while current:
                # Check if this is a pipeline editor widget
                if hasattr(current, 'current_plate') and hasattr(current, 'pipeline_steps'):
                    current_plate = getattr(current, 'current_plate', None)
                    if current_plate:
                        logger.debug(f"Found current plate from pipeline editor: {current_plate}")
                        return current_plate

                # Check children for pipeline editor widget
                for child in current.findChildren(QWidget):
                    if hasattr(child, 'current_plate') and hasattr(child, 'pipeline_steps'):
                        current_plate = getattr(child, 'current_plate', None)
                        if current_plate:
                            logger.debug(f"Found current plate from pipeline editor child: {current_plate}")
                            return current_plate

                current = current.parent()

            logger.warning("Could not find current plate from pipeline editor")
            return None

        except Exception as e:
            logger.error(f"Error getting current plate from pipeline editor: {e}")
            return None

    # Old function pane methods removed - now using dedicated FunctionListEditorWidget
    
    def get_function_info(self) -> str:
        """
        Get function information for display.
        
        Returns:
            Function information string
        """
        if not self.editing_step or not hasattr(self.editing_step, 'func'):
            return "No function assigned"
        
        func = self.editing_step.func
        func_name = getattr(func, '__name__', 'Unknown Function')
        func_module = getattr(func, '__module__', 'Unknown Module')
        
        info = f"Function: {func_name}\n"
        info += f"Module: {func_module}\n"
        
        # Add parameter info if available
        if hasattr(self.editing_step, 'parameters'):
            params = self.editing_step.parameters
            if params:
                info += f"\nParameters ({len(params)}):\n"
                for param_name, param_value in params.items():
                    info += f"  {param_name}: {param_value}\n"
        
        return info
    
    def on_orchestrator_config_changed(self, plate_path: str, effective_config):
        """Handle orchestrator configuration changes for placeholder refresh.

        This is called when the pipeline config is saved and the orchestrator's
        effective config changes. We need to update our stored pipeline_config
        reference and refresh the step editor's placeholders.

        Args:
            plate_path: Path of the plate whose orchestrator config changed
            effective_config: The orchestrator's new effective configuration
        """
        # Only refresh if this is for our orchestrator
        if self.orchestrator and str(self.orchestrator.plate_path) == plate_path:
            logger.debug(f"Step editor received orchestrator config change for {plate_path}")

            # Update our stored pipeline_config reference to the orchestrator's current config
            self.pipeline_config = self.orchestrator.pipeline_config

            # Update the step editor's pipeline_config reference
            if hasattr(self, 'step_editor') and self.step_editor:
                self.step_editor.pipeline_config = self.orchestrator.pipeline_config

                # Update the form manager's context_obj to use the new pipeline config
                if hasattr(self.step_editor, 'form_manager') and self.step_editor.form_manager:
                    # CRITICAL: Update context_obj for root form manager AND all nested managers
                    # Nested managers (e.g., processing_config) also have context_obj references that need updating
                    self._update_context_obj_recursively(self.step_editor.form_manager, self.orchestrator.pipeline_config)

                    # Refresh placeholders to show new inherited values
                    self.step_editor.form_manager._refresh_all_placeholders()
                    logger.debug("Refreshed step editor placeholders after pipeline config change")

    def _update_context_obj_recursively(self, form_manager, new_context_obj):
        """Recursively update context_obj for a form manager and all its nested managers.

        This is critical for proper placeholder resolution after pipeline config changes.
        When the pipeline config is saved, we get a new PipelineConfig object from the
        orchestrator. We need to update not just the root form manager's context_obj,
        but also all nested managers (processing_config, zarr_config, etc.) so they
        resolve placeholders against the new config.

        Args:
            form_manager: The ParameterFormManager to update
            new_context_obj: The new context object (pipeline_config)
        """
        # Update this manager's context_obj
        form_manager.context_obj = new_context_obj

        # Recursively update all nested managers
        if hasattr(form_manager, 'nested_managers'):
            for nested_name, nested_manager in form_manager.nested_managers.items():
                self._update_context_obj_recursively(nested_manager, new_context_obj)

    def on_form_parameter_changed(self, param_name: str, value):
        """Handle form parameter changes directly from form manager.

        SINGLE SOURCE OF TRUTH: Always sync function editor on any parameter change.
        This ensures the function editor stays in sync regardless of which parameter
        changed or how the step structure evolves in the future.

        Handles both top-level parameters (e.g., 'name', 'processing_config') and
        nested parameters from nested forms (e.g., 'group_by' from processing_config form).
        """
        logger.info(f"🔔 on_form_parameter_changed: param_name={param_name}, value type={type(value).__name__}")

        # Handle reset_all completion signal
        if param_name == "__reset_all_complete__":
            logger.info("🔄 Received reset_all_complete signal, syncing function editor")
            # Sync function editor after reset_all completes
            self._sync_function_editor_from_step()
            self.detect_changes()
            return

        # CRITICAL: Check if this is a nested parameter (from a nested form manager)
        # Nested parameters are fields within nested dataclasses (e.g., processing_config.group_by)
        # They don't exist as direct attributes on FunctionStep
        # Known nested parameters from processing_config: group_by, variable_components, input_source
        NESTED_PARAMS = {'group_by', 'variable_components', 'input_source'}

        if param_name in NESTED_PARAMS:
            logger.info(f"🔍 {param_name} is a nested parameter from processing_config")
            # This is a nested parameter change - the nested form manager already updated
            # the processing_config dataclass, so we just need to sync the function editor
            # The step_editor.form_manager has a nested manager for processing_config that
            # already updated self.editing_step.processing_config.{param_name}
            logger.info(f"🔄 Calling _sync_function_editor_from_step after nested {param_name} change")
            self._sync_function_editor_from_step()
            self.detect_changes()
            return

        # CRITICAL FIX: For function parameters, use fresh imports to avoid unpicklable registry wrappers
        if param_name == 'func' and callable(value) and hasattr(value, '__module__'):
            try:
                import importlib
                module = importlib.import_module(value.__module__)
                value = getattr(module, value.__name__)
            except Exception:
                pass  # Use original if refresh fails

        # CRITICAL FIX: For nested dataclass parameters (like processing_config),
        # don't replace the entire lazy dataclass - instead update individual fields
        # This preserves lazy resolution for fields that weren't changed
        from dataclasses import is_dataclass, fields
        if is_dataclass(value) and not isinstance(value, type):
            logger.info(f"📦 {param_name} is a nested dataclass, updating fields individually")
            # This is a nested dataclass - update fields individually
            existing_config = getattr(self.editing_step, param_name, None)
            if existing_config is not None and hasattr(existing_config, '_resolve_field_value'):
                logger.info(f"✅ {param_name} is lazy, preserving lazy resolution")
                # Existing config is lazy - update fields individually to preserve lazy resolution
                for field in fields(value):
                    # Use object.__getattribute__ to get raw value (not lazy-resolved)
                    raw_value = object.__getattribute__(value, field.name)
                    logger.info(f"  📝 Field {field.name}: raw_value={raw_value} (type={type(raw_value).__name__})")
                    # CRITICAL: Always update the field, even if None
                    # When user resets a field, we MUST update it to None so lazy resolution can inherit from context
                    # When user sets a concrete value, we update it to that value
                    object.__setattr__(existing_config, field.name, raw_value)
                    logger.info(f"    ✏️  Updated {field.name} to {raw_value}")
                logger.info(f"✅ Updated lazy {param_name} fields individually to preserve lazy resolution")
            else:
                logger.info(f"⚠️  {param_name} is not lazy or doesn't exist, replacing entire config")
                # Not lazy or doesn't exist - just replace it
                setattr(self.editing_step, param_name, value)
        else:
            logger.info(f"📄 {param_name} is not a nested dataclass, setting normally")
            # Not a nested dataclass - just set it normally
            setattr(self.editing_step, param_name, value)

        # SINGLE SOURCE OF TRUTH: Always sync function editor from step
        # This handles any parameter that might affect component selection
        # (group_by, variable_components, processing_config, etc.)
        logger.info(f"🔄 Calling _sync_function_editor_from_step after {param_name} change")
        self._sync_function_editor_from_step()

        self.detect_changes()
    
    def on_tab_changed(self, index: int):
        """Handle tab changes."""
        tab_names = ["step", "function"]
        if 0 <= index < len(tab_names):
            self.current_tab = tab_names[index]
            logger.debug(f"Tab changed to: {self.current_tab}")
    
    def detect_changes(self):
        """Detect if changes have been made."""
        has_changes = self.original_step != self.editing_step

        # Check function pattern
        if not has_changes:
            original_func = getattr(self.original_step, 'func', None)
            current_func = getattr(self.editing_step, 'func', None)
            # Simple comparison - could be enhanced for deep comparison
            has_changes = str(original_func) != str(current_func)

        if has_changes != self.has_changes:
            self.has_changes = has_changes
            self.changes_detected.emit(has_changes)
    
    def on_changes_detected(self, has_changes: bool):
        """Handle changes detection."""
        if has_changes:
            self.changes_label.setText("● Unsaved changes")
            self.save_button.setEnabled(True)
        else:
            self.changes_label.setText("")
            self.save_button.setEnabled(False)
    
    def save_edit(self, *, close_window=True):
        """Save the edited step. If close_window is True, close after saving; else, keep open."""
        try:
            # CRITICAL FIX: Sync function pattern from function editor BEFORE collecting form values
            # The function editor doesn't use a form manager, so we need to explicitly sync it
            if self.func_editor:
                current_pattern = self.func_editor.current_pattern

                # CRITICAL FIX: Use fresh imports to avoid unpicklable registry wrappers
                if callable(current_pattern) and hasattr(current_pattern, '__module__'):
                    try:
                        import importlib
                        module = importlib.import_module(current_pattern.__module__)
                        current_pattern = getattr(module, current_pattern.__name__)
                    except Exception:
                        pass  # Use original if refresh fails

                self.editing_step.func = current_pattern
                logger.debug(f"Synced function pattern before save: {current_pattern}")

            # CRITICAL FIX: Collect current values from all form managers before saving
            # This ensures nested dataclass field values are properly saved to the step object
            for tab_index in range(self.tab_widget.count()):
                tab_widget = self.tab_widget.widget(tab_index)
                if hasattr(tab_widget, 'form_manager'):
                    # Get current values from this tab's form manager
                    current_values = tab_widget.form_manager.get_current_values()

                    # Apply values to the editing step
                    for param_name, value in current_values.items():
                        if hasattr(self.editing_step, param_name):
                            setattr(self.editing_step, param_name, value)
                            logger.debug(f"Applied {param_name}={value} to editing step")

            # Validate step
            step_name = getattr(self.editing_step, 'name', None)
            if not step_name or not step_name.strip():
                from PyQt6.QtWidgets import QMessageBox
                QMessageBox.warning(self, "Validation Error", "Step name cannot be empty.")
                return

            # CRITICAL FIX: For existing steps, apply changes to original step object
            # This ensures the pipeline gets the updated step with the same object identity
            logger.info(f"💾 Save: is_new={self.is_new}, original_step_reference={self.original_step_reference is not None}")

            if self.original_step_reference is not None:
                # Editing existing step
                logger.info(f"💾 Editing existing step: {getattr(self.original_step_reference, 'name', 'Unknown')}")
                self._apply_changes_to_original()
                step_to_save = self.original_step_reference
            else:
                # For new steps, after first save, switch to edit mode
                logger.info(f"💾 Creating new step, switching to edit mode")
                step_to_save = self.editing_step
                self.original_step_reference = self.editing_step
                self.is_new = False
                logger.info(f"💾 Set is_new=False, original_step_reference set")
                self._update_window_title()
                self._update_save_button_text()

            # Emit signals and call callback
            logger.info(f"💾 Emitting step_saved signal for: {getattr(step_to_save, 'name', 'Unknown')}")
            self.step_saved.emit(step_to_save)

            if self.on_save_callback:
                logger.info(f"💾 Calling on_save_callback")
                self.on_save_callback(step_to_save)

            if close_window:
                self.accept()  # BaseFormDialog handles unregistration
            logger.debug(f"Step saved: {getattr(step_to_save, 'name', 'Unknown')}")

        except Exception as e:
            logger.error(f"Failed to save step: {e}")
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.critical(self, "Save Error", f"Failed to save step:\n{e}")

    def _apply_changes_to_original(self):
        """Apply all changes from editing_step to original_step_reference."""
        if self.original_step_reference is None:
            return

        # Copy all attributes from editing_step to original_step_reference
        from dataclasses import fields, is_dataclass

        if is_dataclass(self.editing_step):
            # For dataclass steps, copy all field values
            for field in fields(self.editing_step):
                value = getattr(self.editing_step, field.name)
                setattr(self.original_step_reference, field.name, value)
        else:
            # CRITICAL FIX: Use reflection to copy ALL attributes, not just hardcoded list
            # This ensures optional dataclass attributes like step_materialization_config are copied
            for attr_name in dir(self.editing_step):
                # Skip private/magic attributes and methods
                if not attr_name.startswith('_') and not callable(getattr(self.editing_step, attr_name, None)):
                    if hasattr(self.editing_step, attr_name) and hasattr(self.original_step_reference, attr_name):
                        value = getattr(self.editing_step, attr_name)
                        setattr(self.original_step_reference, attr_name, value)
                        logger.debug(f"Copied attribute {attr_name}: {value}")

        logger.debug("Applied changes to original step object")

    def _clone_step(self, step):
        """Clone a step object using deep copy."""
        import copy
        return copy.deepcopy(step)

    def _create_new_step(self):
        """Create a new empty step."""
        from openhcs.core.steps.function_step import FunctionStep
        return FunctionStep(
            func=[],  # Start with empty function list
            name="New_Step"
        )

    def cancel_edit(self):
        """Cancel editing and close dialog."""
        if self.has_changes:
            from PyQt6.QtWidgets import QMessageBox
            reply = QMessageBox.question(
                self,
                "Unsaved Changes",
                "You have unsaved changes. Are you sure you want to cancel?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No
            )

            if reply != QMessageBox.StandardButton.Yes:
                return

        self.step_cancelled.emit()
        self.reject()  # BaseFormDialog handles unregistration
        logger.debug("Step editing cancelled")

    def closeEvent(self, event):
        """Handle dialog close event."""
        if self.has_changes:
            from PyQt6.QtWidgets import QMessageBox
            reply = QMessageBox.question(
                self,
                "Unsaved Changes",
                "You have unsaved changes. Are you sure you want to close?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                QMessageBox.StandardButton.No
            )

            if reply != QMessageBox.StandardButton.Yes:
                event.ignore()
                return

        super().closeEvent(event)  # BaseFormDialog handles unregistration

    # No need to override _get_form_managers() - BaseFormDialog automatically
    # discovers all ParameterFormManager instances recursively in the widget tree
