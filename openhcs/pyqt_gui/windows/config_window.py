"""
Configuration Window for PyQt6

Configuration editing dialog with full feature parity to Textual TUI version.
Uses hybrid approach: extracted business logic + clean PyQt6 UI.
"""

import logging
import dataclasses
from typing import Type, Any, Callable, Optional

from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QScrollArea, QWidget, QSplitter, QTreeWidget, QTreeWidgetItem,
    QLineEdit, QSpinBox, QDoubleSpinBox, QCheckBox, QComboBox
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont, QColor

# Infrastructure classes removed - functionality migrated to ParameterFormManager service layer
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.pyqt_gui.windows.base_form_dialog import BaseFormDialog
from openhcs.core.config import GlobalPipelineConfig
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

        # Flag to prevent refresh during save operation
        self._saving = False

        # Initialize color scheme and style generator
        self.color_scheme = color_scheme or PyQt6ColorScheme()
        self.style_generator = StyleSheetGenerator(self.color_scheme)

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
        save_button.clicked.connect(self.save_config)
        save_button.setStyleSheet(button_styles["save"])
        header_layout.addWidget(save_button)

        layout.addWidget(header_widget)

        # Create splitter with tree view on left and form on right
        splitter = QSplitter(Qt.Orientation.Horizontal)

        # Left panel - Inheritance hierarchy tree
        self.tree_widget = self._create_inheritance_tree()
        splitter.addWidget(self.tree_widget)

        # Right panel - Parameter form with scroll area
        # Always use scroll area for consistent navigation behavior
        self.scroll_area = QScrollArea()
        self.scroll_area.setWidgetResizable(True)
        self.scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.scroll_area.setWidget(self.form_manager)
        splitter.addWidget(self.scroll_area)

        # Set splitter proportions (30% tree, 70% form)
        splitter.setSizes([300, 700])

        # Add splitter with stretch factor so it expands to fill available space
        layout.addWidget(splitter, 1)  # stretch factor = 1

        # Apply centralized styling (config window style includes tree styling now)
        self.setStyleSheet(
            self.style_generator.generate_config_window_style() + "\n" +
            self.style_generator.generate_tree_widget_style()
        )

    def _create_inheritance_tree(self) -> QTreeWidget:
        """Create tree widget showing inheritance hierarchy for navigation."""
        tree = QTreeWidget()
        tree.setHeaderLabel("Configuration Hierarchy")
        # Remove width restrictions to allow horizontal dragging
        tree.setMinimumWidth(200)

        # Disable expand on double-click (use arrow only)
        tree.setExpandsOnDoubleClick(False)

        # Build inheritance hierarchy
        self._populate_inheritance_tree(tree)

        # Connect double-click to navigation
        tree.itemDoubleClicked.connect(self._on_tree_item_double_clicked)

        return tree

    def _populate_inheritance_tree(self, tree: QTreeWidget):
        """Populate the inheritance tree with only dataclasses visible in the UI.

        Excludes the root node (PipelineConfig/GlobalPipelineConfig) and shows
        its attributes directly as top-level items.
        """
        import dataclasses

        # Skip creating root item - add children directly to tree as top-level items
        if dataclasses.is_dataclass(self.config_class):
            self._add_ui_visible_dataclasses_to_tree(tree, self.config_class, is_root=True)

        # Leave tree collapsed by default (user can expand as needed)

    def _get_base_type(self, dataclass_type):
        """Get base (non-lazy) type for a dataclass - type-based detection."""
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

        # Type-based lazy detection
        if LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type):
            # Get first non-Lazy base class
            for base in dataclass_type.__bases__:
                if base.__name__ != 'object' and not LazyDefaultPlaceholderService.has_lazy_resolution(base):
                    return base

        return dataclass_type

    def _add_ui_visible_dataclasses_to_tree(self, parent_item, dataclass_type, is_root=False):
        """Add only dataclasses that are visible in the UI form.

        Args:
            parent_item: Either a QTreeWidgetItem or QTreeWidget (for root level)
            dataclass_type: The dataclass type to process
            is_root: True if adding direct children of the root config class
        """
        import dataclasses

        # Get all fields from this dataclass
        fields = dataclasses.fields(dataclass_type)

        for field in fields:
            field_name = field.name
            field_type = field.type

            # Only show dataclass fields (these appear as sections in the UI)
            if dataclasses.is_dataclass(field_type):
                # Get the base (non-lazy) type for display and inheritance
                base_type = self._get_base_type(field_type)
                display_name = base_type.__name__

                # Check if this field is hidden from UI
                is_ui_hidden = self._is_field_ui_hidden(dataclass_type, field_name, field_type)

                # Skip root-level ui_hidden items entirely (don't show them in tree at all)
                # For nested items, show them but styled differently (for inheritance visibility)
                if is_root and is_ui_hidden:
                    continue

                # For root-level items, show only the class name (matching child style)
                # For nested items, show "field_name (ClassName)"
                if is_root:
                    label = display_name
                else:
                    label = f"{field_name} ({display_name})"

                # Create a child item for this nested dataclass
                field_item = QTreeWidgetItem([label])
                field_item.setData(0, Qt.ItemDataRole.UserRole, {
                    'type': 'dataclass',
                    'class': field_type,  # Store original type for field lookup
                    'field_name': field_name,
                    'ui_hidden': is_ui_hidden  # Store ui_hidden flag
                })

                # Style ui_hidden items differently (grayed out, italicized)
                if is_ui_hidden:
                    font = field_item.font(0)
                    font.setItalic(True)
                    field_item.setFont(0, font)
                    field_item.setForeground(0, QColor(128, 128, 128))
                    field_item.setToolTip(0, "This configuration is not editable in the UI (inherited by other configs)")

                # Add to parent (either QTreeWidget for root or QTreeWidgetItem for nested)
                if is_root:
                    parent_item.addTopLevelItem(field_item)
                else:
                    parent_item.addChild(field_item)

                # Show inheritance hierarchy using the BASE type (not lazy type)
                # This automatically skips the lazy→base transition
                self._add_inheritance_info(field_item, base_type)

                # Recursively add nested dataclasses using BASE type (not root anymore)
                self._add_ui_visible_dataclasses_to_tree(field_item, base_type, is_root=False)

    def _is_field_ui_hidden(self, dataclass_type, field_name: str, field_type) -> bool:
        """Check if a field should be hidden from the UI.

        Args:
            dataclass_type: The parent dataclass containing the field
            field_name: Name of the field
            field_type: Type of the field

        Returns:
            True if the field should be hidden from UI
        """
        import dataclasses

        # Check field metadata for ui_hidden flag
        try:
            field_obj = next(f for f in dataclasses.fields(dataclass_type) if f.name == field_name)
            if field_obj.metadata.get('ui_hidden', False):
                return True
        except (StopIteration, TypeError):
            pass

        # Check if the field's type itself has _ui_hidden attribute
        # IMPORTANT: Check __dict__ directly to avoid inheriting _ui_hidden from parent classes
        # We only want to hide fields whose type DIRECTLY has _ui_hidden=True
        base_type = self._get_base_type(field_type)
        if hasattr(base_type, '__dict__') and '_ui_hidden' in base_type.__dict__ and base_type._ui_hidden:
            return True

        return False

    def _add_inheritance_info(self, parent_item: QTreeWidgetItem, dataclass_type):
        """Add inheritance information for a dataclass with proper hierarchy."""
        # Get direct base classes (dataclass_type is already the base/non-lazy type)
        direct_bases = []
        for cls in dataclass_type.__bases__:
            if cls.__name__ == 'object':
                continue
            if not hasattr(cls, '__dataclass_fields__'):
                continue

            # Always use base type (no lazy wrappers at this point)
            base_type = self._get_base_type(cls)
            direct_bases.append(base_type)

        # Add base classes directly as children (no "Inherits from:" label)
        for base_class in direct_bases:
            # Check if this base class is ui_hidden
            is_ui_hidden = hasattr(base_class, '__dict__') and '_ui_hidden' in base_class.__dict__ and base_class._ui_hidden

            base_item = QTreeWidgetItem([base_class.__name__])
            base_item.setData(0, Qt.ItemDataRole.UserRole, {
                'type': 'inheritance_link',
                'target_class': base_class,
                'ui_hidden': is_ui_hidden
            })

            # Style ui_hidden items differently (grayed out, italicized)
            if is_ui_hidden:
                font = base_item.font(0)
                font.setItalic(True)
                base_item.setFont(0, font)
                base_item.setForeground(0, QColor(128, 128, 128))
                base_item.setToolTip(0, "This configuration is not editable in the UI (inherited by other configs)")

            parent_item.addChild(base_item)

            # Recursively add inheritance for this base class
            self._add_inheritance_info(base_item, base_class)

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

            # The nested_manager itself is a QWidget (ParameterFormManager inherits from QWidget)
            # Scroll directly to it - this will show the entire section
            self.scroll_area.ensureWidgetVisible(nested_manager, 100, 100)
            logger.info(f"✅ Scrolled to {field_name} via nested manager widget")
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

    def save_config(self):
        """Save the configuration preserving lazy behavior for unset fields."""
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

            self.accept()

        except Exception as e:
            logger.error(f"Failed to save configuration: {e}")
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.critical(self, "Save Error", f"Failed to save configuration:\n{e}")
    

    def _patch_lazy_constructors(self):
        """Context manager that patches lazy dataclass constructors to preserve None vs concrete distinction."""
        from contextlib import contextmanager
        from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService
        from openhcs.config_framework.lazy_factory import _lazy_type_registry
        import dataclasses

        @contextmanager
        def patch_context():
            original_constructors = {}

            # FIXED: Dynamically discover all lazy types from registry instead of hardcoding
            # This ensures we patch ALL lazy types, including future additions
            for lazy_type in _lazy_type_registry.keys():
                if LazyDefaultPlaceholderService.has_lazy_resolution(lazy_type):
                    # Store original constructor
                    original_constructors[lazy_type] = lazy_type.__init__

                    # Create patched constructor that uses raw values
                    def create_patched_init(original_init, dataclass_type):
                        def patched_init(self, **kwargs):
                            # Use raw value approach instead of calling original constructor
                            # This prevents lazy resolution during code execution
                            for field in dataclasses.fields(dataclass_type):
                                value = kwargs.get(field.name, None)
                                object.__setattr__(self, field.name, value)

                            # Initialize any required lazy dataclass attributes
                            if hasattr(dataclass_type, '_is_lazy_dataclass'):
                                object.__setattr__(self, '_is_lazy_dataclass', True)

                        return patched_init

                    # Apply the patch
                    lazy_type.__init__ = create_patched_init(original_constructors[lazy_type], lazy_type)

            try:
                yield
            finally:
                # Restore original constructors
                for lazy_type, original_init in original_constructors.items():
                    lazy_type.__init__ = original_init

        return patch_context()

    def _view_code(self):
        """Open code editor to view/edit the configuration as Python code."""
        try:
            from openhcs.pyqt_gui.services.simple_code_editor import SimpleCodeEditorService
            from openhcs.debug.pickle_to_python import generate_config_code
            import os

            # Get current config from form
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
            # CRITICAL: Parse the code to extract explicitly specified fields
            # This prevents overwriting None values for unspecified fields
            explicitly_set_fields = self._extract_explicitly_set_fields(edited_code)

            namespace = {}

            # CRITICAL FIX: Use lazy constructor patching
            with self._patch_lazy_constructors():
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
            from openhcs.core.config import GlobalPipelineConfig

            if self.config_class == GlobalPipelineConfig:
                # For GlobalPipelineConfig: Update thread-local context
                # This ensures all lazy resolution uses the new config
                set_global_config_for_editing(GlobalPipelineConfig, new_config)
                logger.debug("Updated thread-local GlobalPipelineConfig context")
            # For PipelineConfig: No context update needed here
            # The orchestrator.apply_pipeline_config() happens in the save callback
            # Code edits just update the form, actual application happens on Save

            # Update form values from the new config without rebuilding
            self._update_form_from_config(new_config, explicitly_set_fields)

            logger.info("Updated config from edited code")

        except Exception as e:
            logger.error(f"Failed to apply edited config code: {e}")
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.critical(self, "Code Edit Error", f"Failed to apply edited code:\n{e}")

    def _extract_explicitly_set_fields(self, code: str) -> set:
        """
        Parse code to extract which fields were explicitly set.

        Returns a set of field names that appear in the config constructor call.
        For nested fields, uses dot notation like 'zarr_config.chunk_size'.
        """
        import re

        # Find the config = ClassName(...) pattern
        # Match the class name and capture everything inside parentheses
        pattern = rf'config\s*=\s*{self.config_class.__name__}\s*\((.*?)\)\s*$'
        match = re.search(pattern, code, re.DOTALL | re.MULTILINE)

        if not match:
            return set()

        constructor_args = match.group(1)

        # Extract field names (simple pattern: field_name=...)
        # This handles both simple fields and nested dataclass fields
        field_pattern = r'(\w+)\s*='
        fields_found = set(re.findall(field_pattern, constructor_args))

        logger.debug(f"Explicitly set fields from code: {fields_found}")
        return fields_found

    def _update_form_from_config(self, new_config, explicitly_set_fields: set):
        """Update form values from new config without rebuilding the entire form."""
        from dataclasses import fields, is_dataclass

        # CRITICAL: Only update fields that were explicitly set in the code
        # This preserves None values for fields not mentioned in the code
        for field in fields(new_config):
            if field.name in explicitly_set_fields:
                new_value = getattr(new_config, field.name)
                if field.name in self.form_manager.parameters:
                    # For nested dataclasses, we need to recursively update nested fields
                    if is_dataclass(new_value) and not isinstance(new_value, type):
                        self._update_nested_dataclass(field.name, new_value)
                    else:
                        self.form_manager.update_parameter(field.name, new_value)

        # Refresh placeholders to reflect the new values
        self.form_manager._placeholder_refresh_service.refresh_all_placeholders(self.form_manager, None)
        self.form_manager._apply_to_nested_managers(lambda name, manager: manager._placeholder_refresh_service.refresh_all_placeholders(manager, None))

    def _update_nested_dataclass(self, field_name: str, new_value):
        """Recursively update a nested dataclass field and all its children."""
        from dataclasses import fields, is_dataclass

        # Update the parent field first
        self.form_manager.update_parameter(field_name, new_value)

        # Get the nested manager for this field
        nested_manager = self.form_manager.nested_managers.get(field_name)
        if nested_manager:
            # Update each field in the nested manager
            for field in fields(new_value):
                nested_field_value = getattr(new_value, field.name)
                if field.name in nested_manager.parameters:
                    # Recursively handle nested dataclasses
                    if is_dataclass(nested_field_value) and not isinstance(nested_field_value, type):
                        self._update_nested_dataclass_in_manager(nested_manager, field.name, nested_field_value)
                    else:
                        nested_manager.update_parameter(field.name, nested_field_value)

    def _update_nested_dataclass_in_manager(self, manager, field_name: str, new_value):
        """Helper to update nested dataclass within a specific manager."""
        from dataclasses import fields, is_dataclass

        manager.update_parameter(field_name, new_value)

        nested_manager = manager.nested_managers.get(field_name)
        if nested_manager:
            for field in fields(new_value):
                nested_field_value = getattr(new_value, field.name)
                if field.name in nested_manager.parameters:
                    if is_dataclass(nested_field_value) and not isinstance(nested_field_value, type):
                        self._update_nested_dataclass_in_manager(nested_manager, field.name, nested_field_value)
                    else:
                        nested_manager.update_parameter(field.name, nested_field_value)

    def reject(self):
        """Handle dialog rejection (Cancel button)."""
        self.config_cancelled.emit()
        super().reject()  # BaseFormDialog handles unregistration

    def _get_form_managers(self):
        """Return list of form managers to unregister (required by BaseFormDialog)."""
        if hasattr(self, 'form_manager'):
            return [self.form_manager]
        return []
