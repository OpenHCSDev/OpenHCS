"""
Configuration Window for PyQt6

Configuration editing dialog with full feature parity to Textual TUI version.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
import dataclasses
import copy
from typing import Type, Any, Callable, Optional

from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QScrollArea, QWidget, QSplitter, QTreeWidget, QTreeWidgetItem,
    QLineEdit, QSpinBox, QDoubleSpinBox, QCheckBox, QComboBox
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

# Infrastructure classes removed - functionality migrated to ParameterFormManager service layer
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.widgets.shared.config_hierarchy_tree import ConfigHierarchyTreeHelper
from openhcs.pyqt_gui.widgets.shared.collapsible_splitter_helper import CollapsibleSplitterHelper
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.windows.base_form_dialog import BaseFormDialog
from openhcs.core.config import GlobalPipelineConfig
from openhcs.config_framework import is_global_config_type
from openhcs.ui.shared.code_editor_form_updater import CodeEditorFormUpdater
# ❌ REMOVED: require_config_context decorator - enhanced decorator events system handles context automatically
from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService



logger = logging.getLogger(__name__)


# Infrastructure classes removed - functionality migrated to ParameterFormManager service layer


class ConfigWindow(BaseFormDialog):
    """
    PyQt6 Configuration Window.

    Configuration editing dialog with parameter forms and validation.
    Preserves all business logic from Textual version with clean PyQt6 UI.

    Inherits from BaseFormDialog to automatically handle unregistration from
    cross-window placeholder updates when the dialog closes.
    """

    # Signals
    config_saved = pyqtSignal(object)  # saved config
    config_cancelled = pyqtSignal()

    def __init__(self, config_class: Type, current_config: Any,
                 on_save_callback: Optional[Callable] = None,
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None,
                 scope_id: Optional[str] = None):
        """
        Initialize the configuration window.

        Args:
            config_class: Configuration class type
            current_config: Current configuration instance
            on_save_callback: Function to call when config is saved
            color_scheme: Color scheme for styling (optional, uses default if None)
            parent: Parent widget
            scope_id: Optional scope identifier (e.g., plate_path) to limit cross-window updates to same orchestrator
        """
        super().__init__(parent)

        # Business logic state (extracted from Textual version)
        self.config_class = config_class
        self.current_config = current_config
        self.on_save_callback = on_save_callback
        self.scope_id = scope_id  # Store scope_id for passing to form_manager
        self._global_context_dirty = False
        self._original_global_config_snapshot = None

        # Flag to prevent refresh during save operation
        self._saving = False
        self._suppress_global_context_sync = False
        self._needs_global_context_resync = False

        # Initialize color scheme and style generator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)
        self.tree_helper = ConfigHierarchyTreeHelper()

        # SIMPLIFIED: Use dual-axis resolution
        from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService

        # Determine placeholder prefix based on actual instance type (not class type)
        is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(type(current_config))
        placeholder_prefix = "Pipeline default" if is_lazy_dataclass else "Default"

        # SIMPLIFIED: Use ParameterFormManager with dual-axis resolution
        root_field_id = type(current_config).__name__  # e.g., "GlobalPipelineConfig" or "PipelineConfig"
        global_config_type = GlobalPipelineConfig  # Always use GlobalPipelineConfig for dual-axis resolution

        # CRITICAL FIX: Pipeline Config Editor should NOT use itself as parent context
        # context_obj=None means inherit from thread-local GlobalPipelineConfig only
        # The overlay (current form state) will be built by ParameterFormManager
        # This fixes the circular context bug where reset showed old values instead of global defaults

        # CRITICAL: Config window manages its own scroll area, so tell form_manager NOT to create one
        # This prevents double scroll areas which cause navigation bugs
        self.form_manager = ParameterFormManager.from_dataclass_instance(
            dataclass_instance=current_config,
            field_id=root_field_id,
            placeholder_prefix=placeholder_prefix,
            color_scheme=self.color_scheme,
            use_scroll_area=False,  # Config window handles scrolling
            global_config_type=global_config_type,
            context_obj=None,  # Inherit from thread-local GlobalPipelineConfig only
            scope_id=self.scope_id  # Pass scope_id to limit cross-window updates to same orchestrator
        )

        if is_global_config_type(self.config_class):
            self._original_global_config_snapshot = copy.deepcopy(current_config)
            self.form_manager.parameter_changed.connect(self._on_global_config_field_changed)

        # No config_editor needed - everything goes through form_manager
        self.config_editor = None

        # Setup UI
        self.setup_ui()

        logger.debug(f"Config window initialized for {config_class.__name__}")

    def setup_ui(self):
        """Setup the user interface."""
        self.setWindowTitle(f"Configuration - {self.config_class.__name__}")
        self.setModal(False)  # Non-modal like plate manager and pipeline editor
        self.setMinimumSize(600, 400)
        self.resize(800, 600)
        
        layout = QVBoxLayout(self)
        layout.setSpacing(10)

        # Header with title, help button, and action buttons
        header_widget = QWidget()
        header_layout = QHBoxLayout(header_widget)
        header_layout.setContentsMargins(10, 10, 10, 10)

        header_label = QLabel(f"Configure {self.config_class.__name__}")
        header_label.setFont(QFont("Arial", 14, QFont.Weight.Bold))
        header_label.setStyleSheet(f"color: {self.color_scheme.to_hex(self.color_scheme.text_accent)};")
        header_layout.addWidget(header_label)

        # Add help button for the dataclass itself
        if dataclasses.is_dataclass(self.config_class):
            from openhcs.pyqt_gui.widgets.shared.clickable_help_components import HelpButton
            help_btn = HelpButton(help_target=self.config_class, text="Help", color_scheme=self.color_scheme)
            help_btn.setMaximumWidth(80)
            header_layout.addWidget(help_btn)

        header_layout.addStretch()

        # Add action buttons to header (top right)
        button_styles = self.style_generator.generate_config_button_styles()

        # View Code button
        view_code_button = QPushButton("View Code")
        view_code_button.setFixedHeight(28)
        view_code_button.setMinimumWidth(80)
        view_code_button.clicked.connect(self._view_code)
        view_code_button.setStyleSheet(button_styles["reset"])
        header_layout.addWidget(view_code_button)

        # Reset button
        reset_button = QPushButton("Reset to Defaults")
        reset_button.setFixedHeight(28)
        reset_button.setMinimumWidth(100)
        reset_button.clicked.connect(self.reset_to_defaults)
        reset_button.setStyleSheet(button_styles["reset"])
        header_layout.addWidget(reset_button)

        # Cancel button
        cancel_button = QPushButton("Cancel")
        cancel_button.setFixedHeight(28)
        cancel_button.setMinimumWidth(70)
        cancel_button.clicked.connect(self.reject)
        cancel_button.setStyleSheet(button_styles["cancel"])
        header_layout.addWidget(cancel_button)

        # Save button
        save_button = QPushButton("Save")
        save_button.setFixedHeight(28)
        save_button.setMinimumWidth(70)
        self._setup_save_button(save_button, self.save_config)
        save_button.setStyleSheet(button_styles["save"])
        header_layout.addWidget(save_button)

        layout.addWidget(header_widget)

        # Create splitter with tree view on left and form on right
        self.splitter = QSplitter(Qt.Orientation.Horizontal)
        self.splitter.setChildrenCollapsible(True)  # Allow collapsing to 0
        self.splitter.setHandleWidth(5)  # Make handle more visible

        # Left panel - Inheritance hierarchy tree
        self.tree_widget = self._create_inheritance_tree()
        self.splitter.addWidget(self.tree_widget)

        # Right panel - Parameter form with scroll area
        # Always use scroll area for consistent navigation behavior
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.scroll_area.setWidget(self.form_manager)
        self.splitter.addWidget(self.scroll_area)

        # Set splitter proportions (30% tree, 70% form)
        self.splitter.setSizes([300, 700])

        # Install collapsible splitter helper for double-click toggle
        self.splitter_helper = CollapsibleSplitterHelper(self.splitter, left_panel_index=0)
        self.splitter_helper.set_initial_size(300)

        # Add splitter with stretch factor so it expands to fill available space
        layout.addWidget(self.splitter, 1)  # stretch factor = 1

        # Apply centralized styling (config window style includes tree styling now)
        self.setStyleSheet(
            self.style_generator.generate_config_window_style() + "\n" +
            self.style_generator.generate_tree_widget_style()
        )

    def _create_inheritance_tree(self) -> QTreeWidget:
        """Create tree widget showing inheritance hierarchy for navigation."""
        tree = self.tree_helper.create_tree_widget()
        self.tree_helper.populate_from_root_dataclass(tree, self.config_class)

        # Connect click/double-click to navigation
        tree.itemClicked.connect(self._on_tree_item_double_clicked)
        tree.itemDoubleClicked.connect(self._on_tree_item_double_clicked)

        return tree

    def _on_tree_item_double_clicked(self, item: QTreeWidgetItem, column: int):
        """Handle tree item double-clicks for navigation."""
        data = item.data(0, Qt.ItemDataRole.UserRole)
        if not data:
            return

        # Check if this item is ui_hidden - if so, ignore the double-click
        if data.get('ui_hidden', False):
            logger.debug("Ignoring double-click on ui_hidden item")
            return

        item_type = data.get('type')

        if item_type == 'dataclass':
            # Navigate to the dataclass section in the form
            field_name = data.get('field_name')
            if field_name:
                self._scroll_to_section(field_name)
                logger.debug(f"Navigating to section: {field_name}")
            else:
                class_obj = data.get('class')
                class_name = getattr(class_obj, '__name__', 'Unknown') if class_obj else 'Unknown'
                logger.debug(f"Double-clicked on root dataclass: {class_name}")

        elif item_type == 'inheritance_link':
            # Navigate to the parent class section in the form
            target_class = data.get('target_class')
            if target_class:
                # Find the field that has this type (or its lazy version)
                field_name = self._find_field_for_class(target_class)
                if field_name:
                    self._scroll_to_section(field_name)
                    logger.debug(f"Navigating to inherited section: {field_name} (class: {target_class.__name__})")
                else:
                    logger.warning(f"Could not find field for class {target_class.__name__}")

    def _find_field_for_class(self, target_class) -> str:
        """Find the field name that has the given class type (or its lazy version)."""
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
        import dataclasses

        # Get the root dataclass type
        root_config = self.form_manager.object_instance
        if not dataclasses.is_dataclass(root_config):
            return None

        root_type = type(root_config)

        # Search through all fields to find one with matching type
        for field in dataclasses.fields(root_type):
            field_type = field.type

            # Check if field type matches target class directly
            if field_type == target_class:
                return field.name

            # Check if field type is a lazy version of target class
            if LazyDefaultPlaceholderService.has_lazy_resolution(field_type):
                # Get the base class of the lazy type
                for base in field_type.__bases__:
                    if base == target_class:
                        return field.name

        return None

    def _scroll_to_section(self, field_name: str):
        """Scroll to a specific section in the form - type-driven, seamless."""
        logger.info(f"🔍 Scrolling to section: {field_name}")
        logger.info(f"Available nested managers: {list(self.form_manager.nested_managers.keys())}")

        # Type-driven: nested_managers dict has exact field name as key
        if field_name in self.form_manager.nested_managers:
            nested_manager = self.form_manager.nested_managers[field_name]

            # Strategy: Find the first parameter widget in this nested manager (like the test does)
            # This is more reliable than trying to find the GroupBox
            first_widget = None

            if hasattr(nested_manager, 'widgets') and nested_manager.widgets:
                # Get the first widget from the nested manager's widgets dict
                first_param_name = next(iter(nested_manager.widgets.keys()))
                first_widget = nested_manager.widgets[first_param_name]
                logger.info(f"Found first widget: {first_param_name}")

            if first_widget:
                # Scroll to the first widget (this will show the section header too)
                self.scroll_area.ensureWidgetVisible(first_widget, 100, 100)
                logger.info(f"✅ Scrolled to {field_name} via first widget")
            else:
                # Fallback: try to find the GroupBox
                from PyQt6.QtWidgets import QGroupBox
                current = nested_manager.parentWidget()
                while current:
                    if isinstance(current, QGroupBox):
                        self.scroll_area.ensureWidgetVisible(current, 50, 50)
                        logger.info(f"✅ Scrolled to {field_name} via GroupBox")
                        return
                    current = current.parentWidget()

                logger.warning(f"⚠️ Could not find widget or GroupBox for {field_name}")
        else:
            logger.warning(f"❌ Field '{field_name}' not in nested_managers")


    



    
    def update_widget_value(self, widget: QWidget, value: Any):
        """
        Update widget value without triggering signals.
        
        Args:
            widget: Widget to update
            value: New value
        """
        # Temporarily block signals to avoid recursion
        widget.blockSignals(True)
        
        try:
            if isinstance(widget, QCheckBox):
                widget.setChecked(bool(value))
            elif isinstance(widget, QSpinBox):
                widget.setValue(int(value) if value is not None else 0)
            elif isinstance(widget, QDoubleSpinBox):
                widget.setValue(float(value) if value is not None else 0.0)
            elif isinstance(widget, QComboBox):
                for i in range(widget.count()):
                    if widget.itemData(i) == value:
                        widget.setCurrentIndex(i)
                        break
            elif isinstance(widget, QLineEdit):
                widget.setText(str(value) if value is not None else "")
        finally:
            widget.blockSignals(False)
    
    def reset_to_defaults(self):
        """Reset all parameters using centralized service with full sophistication."""
        # Service layer now contains ALL the sophisticated logic previously in infrastructure classes
        # This includes nested dataclass reset, lazy awareness, and recursive traversal
        self.form_manager.reset_all_parameters()

        # Refresh placeholder text to ensure UI shows correct defaults
        self.form_manager._refresh_all_placeholders()

        logger.debug("Reset all parameters using enhanced ParameterFormManager service")

    def save_config(self, *, close_window=True):
        """Save the configuration preserving lazy behavior for unset fields. If close_window is True, close after saving; else, keep open."""
        try:
            if LazyDefaultPlaceholderService.has_lazy_resolution(self.config_class):
                # BETTER APPROACH: For lazy dataclasses, only save user-modified values
                # Get only values that were explicitly set by the user (non-None raw values)
                user_modified_values = self.form_manager.get_user_modified_values()

                # Create fresh lazy instance with only user-modified values
                # This preserves lazy resolution for unmodified fields
                new_config = self.config_class(**user_modified_values)
            else:
                # For non-lazy dataclasses, use all current values
                current_values = self.form_manager.get_current_values()
                new_config = self.config_class(**current_values)

            # CRITICAL: Set flag to prevent refresh_config from recreating the form
            # The window already has the correct data - it just saved it!
            self._saving = True
            logger.info(f"🔍 SAVE_CONFIG: Set _saving=True before callback (id={id(self)})")
            try:
                # Emit signal and call callback
                self.config_saved.emit(new_config)

                if self.on_save_callback:
                    logger.info(f"🔍 SAVE_CONFIG: Calling on_save_callback (id={id(self)})")
                    self.on_save_callback(new_config)
                    logger.info(f"🔍 SAVE_CONFIG: Returned from on_save_callback (id={id(self)})")
            finally:
                self._saving = False
                logger.info(f"🔍 SAVE_CONFIG: Reset _saving=False (id={id(self)})")

            if is_global_config_type(self.config_class):
                self._original_global_config_snapshot = copy.deepcopy(new_config)
                self._global_context_dirty = False

            if close_window:
                self.accept()
            else:
                # CRITICAL: If keeping window open after save, update the form manager's object_instance
                # and refresh placeholders to reflect the new saved values
                self.form_manager.object_instance = new_config

                # Increment token to invalidate caches
                from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
                LiveContextService.increment_token()

                # Refresh this window's placeholders with new saved values as base
                from openhcs.pyqt_gui.widgets.shared.services.parameter_ops_service import ParameterOpsService
                ParameterOpsService().refresh_with_live_context(self.form_manager)

                # Emit context_refreshed to notify other windows
                self.form_manager.context_refreshed.emit(new_config, self.form_manager.context_obj, self.form_manager.scope_id or "")

        except Exception as e:
            logger.error(f"Failed to save configuration: {e}")
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.critical(self, "Save Error", f"Failed to save configuration:\n{e}")
    

    def _view_code(self):
        """Open code editor to view/edit the configuration as Python code."""
        try:
            from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService
            from openhcs.debug.pickle_to_python import generate_config_code
            from openhcs.pyqt_gui.widgets.shared.services.parameter_ops_service import ParameterOpsService
            import os

            # CRITICAL: Refresh with live context BEFORE getting current values
            # This ensures code editor shows unsaved changes from other open windows
            # Example: GlobalPipelineConfig editor open with unsaved zarr_config changes
            #          → PipelineConfig code editor should show those live zarr_config values
            ParameterOpsService().refresh_with_live_context(self.form_manager)

            # Get current config from form (now includes live context values)
            current_values = self.form_manager.get_current_values()
            current_config = self.config_class(**current_values)

            # Generate code using existing function
            python_code = generate_config_code(current_config, self.config_class, clean_mode=True)

            # Launch editor
            editor_service = SimpleCodeEditorService(self)
            use_external = os.environ.get('OPENHCS_USE_EXTERNAL_EDITOR', '').lower() in ('1', 'true', 'yes')

            editor_service.edit_code(
                initial_content=python_code,
                title=f"View/Edit {self.config_class.__name__}",
                callback=self._handle_edited_config_code,
                use_external=use_external,
                code_type='config',
                code_data={'config_class': self.config_class, 'clean_mode': True}
            )

        except Exception as e:
            logger.error(f"Failed to view config code: {e}")
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.critical(self, "View Code Error", f"Failed to view code:\n{e}")

    def _handle_edited_config_code(self, edited_code: str):
        """Handle edited configuration code from the code editor."""
        try:
            # SIMPLIFIED: Just exec with patched constructors
            # The patched constructors preserve None vs concrete distinction in raw field values
            # No need to parse code - just inspect raw values after exec
            namespace = {}

            with CodeEditorFormUpdater.patch_lazy_constructors():
                exec(edited_code, namespace)

            new_config = namespace.get('config')
            if not new_config:
                raise ValueError("No 'config' variable found in edited code")

            if not isinstance(new_config, self.config_class):
                raise ValueError(f"Expected {self.config_class.__name__}, got {type(new_config).__name__}")

            # Update current config
            self.current_config = new_config

            # FIXED: Proper context propagation based on config type
            # ConfigWindow is used for BOTH GlobalPipelineConfig AND PipelineConfig editing
            from openhcs.config_framework.global_config import set_global_config_for_editing

            # Temporarily suppress per-field sync during code-mode bulk update
            suppress_context = is_global_config_type(self.config_class)
            if suppress_context:
                self._suppress_global_context_sync = True
                self._needs_global_context_resync = False

            try:
                if is_global_config_type(self.config_class):
                    # For global configs: Update thread-local context immediately
                    set_global_config_for_editing(self.config_class, new_config)
                    logger.debug(f"Updated thread-local {self.config_class.__name__} context")
                    self._global_context_dirty = True
                # For PipelineConfig: No context update needed here
                # The orchestrator.apply_pipeline_config() happens in the save callback
                # Code edits just update the form, actual application happens on Save

                # Update form values from the new config without rebuilding
                self._update_form_from_config(new_config)

                if suppress_context:
                    self._sync_global_context_with_current_values()
            finally:
                if suppress_context:
                    self._suppress_global_context_sync = False
                    self._needs_global_context_resync = False

            logger.info("Updated config from edited code")

        except Exception as e:
            logger.error(f"Failed to apply edited config code: {e}")
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.critical(self, "Code Edit Error", f"Failed to apply edited code:\n{e}")

    def _on_global_config_field_changed(self, param_name: str, value: Any):
        """Keep thread-local global config context in sync with live edits."""
        if self._saving:
            return
        if self._suppress_global_context_sync:
            self._needs_global_context_resync = True
            return
        self._sync_global_context_with_current_values(param_name)

    def _sync_global_context_with_current_values(self, source_param: str = None):
        """Rebuild global context from current form values once."""
        if not is_global_config_type(self.config_class):
            return
        try:
            current_values = self.form_manager.get_current_values()
            updated_config = self.config_class(**current_values)
            self.current_config = updated_config
            from openhcs.config_framework.global_config import set_global_config_for_editing
            set_global_config_for_editing(self.config_class, updated_config)
            self._global_context_dirty = True
            ParameterFormManager.trigger_global_cross_window_refresh()
            if source_param:
                logger.debug(f"Synchronized {self.config_class.__name__} context after change ({source_param})")
        except Exception as exc:
            logger.warning("Failed to sync global context%s: %s",
                           f' ({source_param})' if source_param else '', exc)

    def _update_form_from_config(self, new_config):
        """Update form values from new config using the shared updater."""
        self.form_manager._block_cross_window_updates = True
        try:
            CodeEditorFormUpdater.update_form_from_instance(
                self.form_manager,
                new_config,
                broadcast_callback=self._broadcast_config_changed
            )
        finally:
            self.form_manager._block_cross_window_updates = False

        ParameterFormManager.trigger_global_cross_window_refresh()

    def reject(self):
        """Handle dialog rejection (Cancel button)."""
        if (is_global_config_type(self.config_class) and
                getattr(self, '_global_context_dirty', False) and
                self._original_global_config_snapshot is not None):
            from openhcs.config_framework.global_config import set_global_config_for_editing
            set_global_config_for_editing(self.config_class,
                                          copy.deepcopy(self._original_global_config_snapshot))
            self._global_context_dirty = False
            logger.debug(f"Restored {self.config_class.__name__} context after cancel")

        self.config_cancelled.emit()
        super().reject()  # BaseFormDialog handles unregistration

        # CRITICAL: Trigger global refresh AFTER unregistration so other windows
        # re-collect live context without this cancelled window's values
        # This ensures group_by selector and other placeholders sync correctly
        ParameterFormManager.trigger_global_cross_window_refresh()
        logger.debug(f"Triggered global refresh after cancelling {self.config_class.__name__} editor")

    def _get_form_managers(self):
        """Return list of form managers to unregister (required by BaseFormDialog)."""
        if hasattr(self, 'form_manager'):
            return [self.form_manager]
        return []
