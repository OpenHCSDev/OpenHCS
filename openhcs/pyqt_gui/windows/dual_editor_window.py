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
from PyQt6.QtCore import pyqtSignal, Qt, QTimer
from PyQt6.QtGui import QFont

from openhcs.core.steps.function_step import FunctionStep
from openhcs.constants.constants import GroupBy
from openhcs.ui.shared.pattern_data_manager import PatternDataManager

from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.windows.base_form_dialog import BaseFormDialog
from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer
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

        # Snapshot of last-saved state for change detection
        self._baseline_snapshot = self._serialize_for_change_detection(self.editing_step)
        
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

        # Debounce timer for function editor synchronization (batches rapid updates)
        self._function_sync_timer = QTimer(self)
        self._function_sync_timer.setSingleShot(True)
        self._function_sync_timer.timeout.connect(self._flush_function_editor_sync)
        self._pending_function_editor_sync = False

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

    def _build_step_scope_id(self, fallback_name: str) -> str:
        plate_scope = getattr(self.orchestrator, 'plate_path', 'no_orchestrator')
        token = getattr(self.editing_step, '_pipeline_scope_token', None)
        if token:
            return f"{plate_scope}::{token}"
        return f"{plate_scope}::{fallback_name}"
    
    def create_step_tab(self):
        """Create the step settings tab (using dedicated widget)."""
        from openhcs.pyqt_gui.widgets.step_parameter_editor import StepParameterEditorWidget
        from openhcs.config_framework.context_manager import config_context

        # Create step parameter editor widget with proper nested context
        # Step must be nested: GlobalPipelineConfig -> PipelineConfig -> Step
        # CRITICAL: Use hierarchical scope_id to isolate this step editor + its function panes
        # Format: "plate_path::step_name" to prevent cross-contamination between different step editors
        step_name = getattr(self.editing_step, 'name', 'unknown_step')
        scope_id = self._build_step_scope_id(step_name)

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

        # CRITICAL: Connect context_refreshed signal for cross-window updates from code editor
        self.step_editor.form_manager.context_refreshed.connect(self._on_step_context_refreshed)

        self.tab_widget.addTab(self.step_editor, "Step Settings")

    def create_function_tab(self):
        """Create the function pattern tab (using dedicated widget)."""
        from openhcs.pyqt_gui.widgets.function_list_editor import FunctionListEditorWidget

        # Convert step func to function list format
        initial_functions = self._convert_step_func_to_list()

        # Create function list editor widget (mirrors Textual TUI)
        # CRITICAL: Pass editing_step for context hierarchy (Function → Step → Pipeline → Global)
        # CRITICAL: Use same hierarchical scope_id as step editor to isolate this step editor + its function panes
        step_name = getattr(self.editing_step, 'name', 'unknown_step')
        scope_id = self._build_step_scope_id(step_name)

        self.func_editor = FunctionListEditorWidget(
            initial_functions=initial_functions,
            step_identifier=step_name,
            service_adapter=None,
            step_instance=self.editing_step,  # Pass step for lazy resolution context
            scope_id=scope_id  # Same hierarchical scope_id as step editor
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

    def _on_step_context_refreshed(self, object_instance, context_obj):
        """Handle context refresh from step editor.

        CRITICAL: This is called when:
        1. Code editor saves (updates step instance)
        2. Cross-window refresh (placeholders update due to PipelineConfig/GlobalPipelineConfig changes)
        3. Reset button clicked (placeholders update to show inherited values)

        We need to refresh the function editor's component button to show the new resolved group_by value.
        """
        # Refresh function editor from step context (updates component button with resolved group_by)
        if hasattr(self, 'func_editor') and self.func_editor is not None:
            self.func_editor.refresh_from_step_context()

        # Detect changes
        self.detect_changes()
        logger.debug("Step context refreshed - updated function editor component button")

    def _get_event_bus(self):
        """Get the global event bus from the service adapter.

        Returns:
            GlobalEventBus instance or None if not found
        """
        try:
            # Navigate up to find main window with service adapter
            current = self.parent()
            while current:
                if hasattr(current, 'service_adapter'):
                    return current.service_adapter.get_event_bus()
                current = current.parent()

            logger.warning("Could not find service adapter for event bus")
            return None
        except Exception as e:
            logger.error(f"Error getting event bus: {e}")
            return None

    def _on_pipeline_changed(self, new_pipeline_steps: list):
        """Handle pipeline_changed signal from global event bus.

        CRITICAL: This is connected to the global event bus in setup_connections().
        It receives updates from ANY window that modifies the pipeline:
        - Pipeline editor code button
        - Plate manager code button
        - Pipeline editor UI
        - Any future pipeline editing source

        This is the OpenHCS "set and forget" pattern - one handler receives ALL updates.

        Args:
            new_pipeline_steps: Updated list of FunctionStep objects from the pipeline
        """
        # Find our step in the new pipeline by matching the original step reference
        # (The step we're editing might have been modified in the code editor)
        original_step = getattr(self, 'original_step', None)
        if not original_step:
            return

        # Try to find the updated version of our step in the new pipeline
        # Match by object identity first (if editing existing step)
        updated_step = None
        for step in new_pipeline_steps:
            if step is original_step:
                updated_step = step
                break

        # If we found an updated version, refresh our editor with the new values
        if updated_step and updated_step is not self.editing_step:
            logger.debug(f"Pipeline changed - updating step editor with new step: {updated_step.name}")

            # Update our editing step reference
            self.editing_step = updated_step
            self.step = updated_step

            # Update step editor's step reference
            if hasattr(self, 'step_editor') and self.step_editor:
                self.step_editor.step = updated_step

                # Refresh the form manager with new values
                if hasattr(self.step_editor, 'form_manager') and self.step_editor.form_manager:
                    self.step_editor.form_manager.object_instance = updated_step
                    self.step_editor.form_manager._refresh_with_live_context()

            # Update function list editor with new func
            if hasattr(self, 'func_editor') and self.func_editor and hasattr(updated_step, 'func'):
                self.func_editor._initialize_pattern_data(updated_step.func)
                self.func_editor._populate_function_list()

            # Detect changes (might have unsaved changes now)
            self.detect_changes()

    def _on_config_changed(self, config):
        """Handle config_changed signal from global event bus.

        CRITICAL: This is connected to the global event bus in setup_connections().
        It receives updates from ANY window that modifies configs:
        - PlateManager code button (GlobalPipelineConfig, PipelineConfig)
        - ConfigWindow code button (GlobalPipelineConfig, PipelineConfig, StepConfig)
        - Any future config editing source

        This is the OpenHCS "set and forget" pattern - one handler receives ALL updates.

        Args:
            config: Updated config object (GlobalPipelineConfig, PipelineConfig, or StepConfig)
        """
        from openhcs.core.config import PipelineConfig
        from openhcs.config_framework import is_global_config_instance
        from openhcs.config_framework.global_config import get_current_global_config

        # Only care about global configs and PipelineConfig changes
        # (StepConfig changes are handled by the step editor's own form manager)
        is_global = is_global_config_instance(config)
        is_pipeline = isinstance(config, PipelineConfig)
        if not (is_global or is_pipeline):
            return

        # Only refresh if this is for our orchestrator
        if not self.orchestrator:
            return

        # Check if this config belongs to our orchestrator
        if is_pipeline:
            # Check if this is our orchestrator's pipeline config
            if config is not self.orchestrator.pipeline_config:
                return
        elif is_global:
            # Check if this is the current global config
            current_global = get_current_global_config(type(config))
            if config is not current_global:
                return

        logger.debug(f"Step editor received config change: {type(config).__name__}")

        # Trigger cross-window refresh for all form managers
        # This will update placeholders in the step editor to show new inherited values
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        ParameterFormManager.trigger_global_cross_window_refresh()
        logger.debug("Triggered global cross-window refresh after config change")

    def setup_connections(self):
        """Setup signal/slot connections."""
        # Tab change tracking
        self.tab_widget.currentChanged.connect(self.on_tab_changed)

        # Change detection
        self.changes_detected.connect(self.on_changes_detected)

        # CRITICAL: Connect to global event bus for cross-window updates
        # This is the OpenHCS "set and forget" pattern - one connection handles ALL sources
        event_bus = self._get_event_bus()
        if event_bus:
            event_bus.pipeline_changed.connect(self._on_pipeline_changed)
            event_bus.config_changed.connect(self._on_config_changed)
            event_bus.register_window(self)
            logger.debug("Connected to global event bus for cross-window updates")

    def _convert_step_func_to_list(self):
        """Convert step func to initial pattern format for function list editor."""
        if not hasattr(self.editing_step, 'func') or not self.editing_step.func:
            return []

        # Return the step func directly - the function list editor will handle the conversion
        result = self.editing_step.func
        logger.debug(f"🔍 DUAL EDITOR _convert_step_func_to_list: returning {result}")
        return result

    def _schedule_function_editor_sync(self):
        """Schedule a batched sync of the function editor."""
        self._pending_function_editor_sync = True
        if not self._function_sync_timer.isActive():
            self._function_sync_timer.start(0)

    def _flush_function_editor_sync(self):
        """Run any pending function editor sync."""
        if not getattr(self, '_pending_function_editor_sync', False):
            return
        self._pending_function_editor_sync = False
        self._sync_function_editor_from_step()
        self.detect_changes()

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
        logger.debug("🔄 _sync_function_editor_from_step called")

        # Guard: Only sync if function editor exists
        if not hasattr(self, 'func_editor') or self.func_editor is None:
            logger.debug("⏭️  Function editor doesn't exist yet, skipping sync")
            return

        # CRITICAL: The function editor already has access to step_instance and can resolve
        # group_by using the same lazy resolution pattern as the function panes.
        # Just trigger a refresh - the function editor will read from step_instance.processing_config.group_by
        # with proper context resolution (including live context from other open windows).
        self.func_editor.refresh_from_step_context()

        logger.debug(f"✅ Triggered function editor refresh from step context")



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
                    # Use the same pattern as on_config_changed (line 466)
                    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
                    ParameterFormManager.trigger_global_cross_window_refresh()
                    logger.debug("Triggered global cross-window refresh after pipeline config change")

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
        logger.info(f"🔔 DUAL_EDITOR: on_form_parameter_changed called")
        logger.info(f"  param_name={param_name}")
        logger.info(f"  value type={type(value).__name__}")
        logger.info(f"  value={repr(value)[:100]}")

        # Handle reset_all completion signal
        if param_name == "__reset_all_complete__":
            logger.debug("🔄 Received reset_all_complete signal, syncing function editor")
            self._schedule_function_editor_sync()
            return

        # param_name is now a full path like "processing_config.group_by" or just "name"
        # Parse the path to determine if it's a nested field
        path_parts = param_name.split('.')
        logger.info(f"  path_parts={path_parts}")

        # Skip the first part if it's the form manager's field_id (type name like "FunctionStep")
        # The path format is: "TypeName.field" or "TypeName.nested.field"
        if len(path_parts) > 1:
            # Remove the type name prefix (e.g., "FunctionStep")
            path_parts = path_parts[1:]
            logger.info(f"  path_parts after removing type prefix={path_parts}")

        if len(path_parts) == 1:
            # Top-level field (e.g., "name", "func", "processing_config")
            field_name = path_parts[0]

            # CRITICAL FIX: For function parameters, use fresh imports to avoid unpicklable registry wrappers
            if field_name == 'func' and callable(value) and hasattr(value, '__module__'):
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
                logger.debug(f"📦 {field_name} is a nested dataclass, updating fields individually")
                existing_config = getattr(self.editing_step, field_name, None)
                if existing_config is not None and hasattr(existing_config, '_resolve_field_value'):
                    logger.debug(f"✅ {field_name} is lazy, preserving lazy resolution")
                    for field in fields(value):
                        raw_value = object.__getattribute__(value, field.name)
                        object.__setattr__(existing_config, field.name, raw_value)
                        logger.debug(f"    ✏️  Updated {field.name} to {raw_value}")
                else:
                    setattr(self.editing_step, field_name, value)
            else:
                setattr(self.editing_step, field_name, value)
        else:
            # Nested field (e.g., ["processing_config", "group_by"])
            # The nested form manager already updated self.editing_step via _mark_parents_modified
            # We just need to sync the function editor
            logger.info(f"  🔄 Nested field change: {'.'.join(path_parts)}")
            logger.info(f"  Nested field already updated by _mark_parents_modified")

        # SINGLE SOURCE OF TRUTH: Always sync function editor from step (batched)
        logger.info(f"  🔄 Scheduling function editor sync after {param_name} change")
        self._schedule_function_editor_sync()
    
    def on_tab_changed(self, index: int):
        """Handle tab changes."""
        tab_names = ["step", "function"]
        if 0 <= index < len(tab_names):
            self.current_tab = tab_names[index]
            logger.debug(f"Tab changed to: {self.current_tab}")
    
    def detect_changes(self):
        """Detect if changes have been made."""
        current_snapshot = self._serialize_current_form_state()
        baseline_snapshot = getattr(self, '_baseline_snapshot', None)
        has_changes = current_snapshot != baseline_snapshot

        logger.info(f"🔍 DETECT_CHANGES:")
        logger.info(f"  current_snapshot={current_snapshot}")
        logger.info(f"  baseline_snapshot={baseline_snapshot}")
        logger.info(f"  has_changes={has_changes}")

        if has_changes != self.has_changes:
            self.has_changes = has_changes
            logger.info(f"  ✅ Emitting changes_detected({has_changes})")
            self.changes_detected.emit(has_changes)
        else:
            logger.info(f"  ⏭️  No change in has_changes state")
    
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

            # After a successful save, refresh the baseline snapshot used for change detection.
            # This ensures Shift+Save (which keeps the window open) clears the "Unsaved changes" label.
            self.original_step = self._clone_step(self.editing_step)
            self._baseline_snapshot = self._serialize_for_change_detection(self.editing_step)
            self.detect_changes()

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

    _CHANGE_DETECTION_EXCLUDE_PARAMS = {'kwargs'}

    def _serialize_for_change_detection(self, step):
        """Create a normalized snapshot of the step for change detection."""
        params = UnifiedParameterAnalyzer.analyze(step)
        snapshot = {}
        for name, param_info in params.items():
            if name in self._CHANGE_DETECTION_EXCLUDE_PARAMS:
                continue
            current_value = getattr(step, name, param_info.default_value)
            snapshot[name] = self._normalize_value_for_change_detection(current_value)
        return snapshot

    def _serialize_current_form_state(self):
        """Serialize a snapshot of the step using live form values (including nested dataclasses)."""
        import copy

        temp_step = copy.deepcopy(self.editing_step)

        # NOTE: We DON'T override func from func_editor.current_pattern here because:
        # 1. current_pattern returns the pattern data structure (list of tuples), not the func value
        # 2. editing_step.func should already be kept in sync by the function editor's signals
        # 3. Using current_pattern would cause serialization mismatch with baseline

        for tab_index in range(self.tab_widget.count()):
            tab_widget = self.tab_widget.widget(tab_index)
            form_manager = getattr(tab_widget, 'form_manager', None)
            if not form_manager:
                continue

            current_values = form_manager.get_current_values()
            for param_name, value in current_values.items():
                if hasattr(temp_step, param_name):
                    setattr(temp_step, param_name, value)

        return self._serialize_for_change_detection(temp_step)

    def _normalize_value_for_change_detection(self, value):
        """Normalize complex values into comparison-friendly primitives."""
        from dataclasses import is_dataclass, fields
        from pathlib import Path

        if value is None:
            return None

        if isinstance(value, (str, int, float, bool)):
            return value

        if isinstance(value, Path):
            return str(value)

        if isinstance(value, list):
            return [self._normalize_value_for_change_detection(v) for v in value]

        if isinstance(value, tuple):
            return tuple(self._normalize_value_for_change_detection(v) for v in value)

        if isinstance(value, dict):
            return {k: self._normalize_value_for_change_detection(v) for k, v in value.items()}

        if hasattr(value, 'value') and hasattr(value, 'name'):
            return value.value

        if callable(value):
            module = getattr(value, '__module__', '')
            qualname = getattr(value, '__qualname__', getattr(value, '__name__', repr(value)))
            return f"{module}.{qualname}"

        if is_dataclass(value):
            from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
            is_lazy_dataclass = get_base_type_for_lazy(type(value)) is not None
            normalized = {}
            for field in fields(value):
                if is_lazy_dataclass:
                    raw_field_value = object.__getattribute__(value, field.name)
                else:
                    raw_field_value = getattr(value, field.name)
                normalized[field.name] = self._normalize_value_for_change_detection(raw_field_value)
            return normalized

        return repr(value)

    def _create_new_step(self):
        """Create a new empty step."""
        from openhcs.core.steps.function_step import FunctionStep
        return FunctionStep(
            func=[],  # Start with empty function list
            name="New_Step"
        )

    def cancel_edit(self):
        """Cancel editing and close dialog."""
        # Just call reject() - it handles everything including the confirmation dialog
        self.reject()

    def reject(self):
        """Handle dialog rejection (Cancel button or Escape key)."""
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
        logger.info("🔍 DualEditorWindow: About to call super().reject()")
        super().reject()  # BaseFormDialog handles unregistration

        # CRITICAL: Trigger global refresh AFTER unregistration so other windows
        # re-collect live context without this cancelled window's values
        logger.info("🔍 DualEditorWindow: About to trigger global refresh")
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        ParameterFormManager.trigger_global_cross_window_refresh()
        logger.info("🔍 DualEditorWindow: Triggered global refresh after cancel")

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
