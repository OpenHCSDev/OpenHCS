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
    QScrollArea, QWidget, QFrame, QSplitter, QTreeWidget, QTreeWidgetItem,
    QLineEdit, QSpinBox, QDoubleSpinBox, QCheckBox, QComboBox
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

# Infrastructure classes removed - functionality migrated to ParameterFormManager service layer
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.core.config import GlobalPipelineConfig
# ❌ REMOVED: require_config_context decorator - enhanced decorator events system handles context automatically
from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
from openhcs.core.context.contextvars_context import config_context



logger = logging.getLogger(__name__)


# Infrastructure classes removed - functionality migrated to ParameterFormManager service layer


class ConfigWindow(QDialog):
    """
    PyQt6 Configuration Window.
    
    Configuration editing dialog with parameter forms and validation.
    Preserves all business logic from Textual version with clean PyQt6 UI.
    """
    
    # Signals
    config_saved = pyqtSignal(object)  # saved config
    config_cancelled = pyqtSignal()

    def __init__(self, config_class: Type, current_config: Any,
                 on_save_callback: Optional[Callable] = None,
                 color_scheme: Optional[PyQt6ColorScheme] = None, parent=None,
                 orchestrator=None):
        """
        Initialize the configuration window.

        Args:
            config_class: Configuration class type
            current_config: Current configuration instance
            on_save_callback: Function to call when config is saved
            color_scheme: Color scheme for styling (optional, uses default if None)
            parent: Parent widget
            orchestrator: Optional orchestrator reference for context persistence
        """
        super().__init__(parent)

        # Business logic state (extracted from Textual version)
        self.config_class = config_class
        self.current_config = current_config
        self.on_save_callback = on_save_callback
        self.orchestrator = orchestrator  # Store orchestrator reference for context persistence

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

        # Use new context system instead of ContextEventCoordinator

        # Create form manager within pipeline config context if available
        if orchestrator and hasattr(orchestrator, 'pipeline_config'):
            with config_context(orchestrator.pipeline_config):
                self.form_manager = ParameterFormManager.from_dataclass_instance(
                    dataclass_instance=current_config,
                    field_id=root_field_id,
                    placeholder_prefix=placeholder_prefix,
                    color_scheme=self.color_scheme,
                    use_scroll_area=True,
                    global_config_type=global_config_type,
                    context_event_coordinator=None,  # No longer needed with new context system
                    context_obj=orchestrator.pipeline_config  # Pass pipeline_config as context object
                )
        else:
            self.form_manager = ParameterFormManager.from_dataclass_instance(
                dataclass_instance=current_config,
                field_id=root_field_id,
                placeholder_prefix=placeholder_prefix,
                color_scheme=self.color_scheme,
                use_scroll_area=True,
                global_config_type=global_config_type,
                context_event_coordinator=None  # No longer needed with new context system
            )

        # No config_editor needed - everything goes through form_manager
        self.config_editor = None

        # Setup UI
        self.setup_ui()

        logger.debug(f"Config window initialized for {config_class.__name__}")

    def _should_use_scroll_area(self) -> bool:
        """Determine if scroll area should be used based on config complexity."""
        # For simple dataclasses with few fields, don't use scroll area
        # This ensures dataclass fields show in full as requested
        if dataclasses.is_dataclass(self.config_class):
            field_count = len(dataclasses.fields(self.config_class))
            # Use scroll area for configs with more than 8 fields (PipelineConfig has ~12 fields)
            return field_count > 8

        # For non-dataclass configs, use scroll area
        return True

    def setup_ui(self):
        """Setup the user interface."""
        self.setWindowTitle(f"Configuration - {self.config_class.__name__}")
        self.setModal(False)  # Non-modal like plate manager and pipeline editor
        self.setMinimumSize(600, 400)
        self.resize(800, 600)
        
        layout = QVBoxLayout(self)
        layout.setSpacing(10)
        
        # Header with help functionality for dataclass
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
        layout.addWidget(header_widget)

        # Create splitter with tree view on left and form on right
        splitter = QSplitter(Qt.Orientation.Horizontal)

        # Left panel - Inheritance hierarchy tree
        self.tree_widget = self._create_inheritance_tree()
        splitter.addWidget(self.tree_widget)

        # Right panel - Parameter form
        if self._should_use_scroll_area():
            self.scroll_area = QScrollArea()
            self.scroll_area.setWidgetResizable(True)
            self.scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
            self.scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            self.scroll_area.setWidget(self.form_manager)
            splitter.addWidget(self.scroll_area)
        else:
            # For simple dataclasses, show form directly without scrolling
            splitter.addWidget(self.form_manager)

        # Set splitter proportions (30% tree, 70% form)
        splitter.setSizes([300, 700])

        # Add splitter with stretch factor so it expands to fill available space
        layout.addWidget(splitter, 1)  # stretch factor = 1
        
        # Button panel
        button_panel = self.create_button_panel()
        layout.addWidget(button_panel)
        
        # Apply centralized styling
        self.setStyleSheet(self.style_generator.generate_config_window_style())

    def _create_inheritance_tree(self) -> QTreeWidget:
        """Create tree widget showing inheritance hierarchy for navigation."""
        tree = QTreeWidget()
        tree.setHeaderLabel("Configuration Hierarchy")
        # Remove width restrictions to allow horizontal dragging
        tree.setMinimumWidth(200)

        # Style the tree with original appearance
        tree.setStyleSheet(f"""
            QTreeWidget {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 3px;
                color: {self.color_scheme.to_hex(self.color_scheme.text_primary)};
                font-size: 12px;
            }}
            QTreeWidget::item {{
                padding: 4px;
                border-bottom: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
            }}
            QTreeWidget::item:selected {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.selection_bg)};
                color: white;
            }}
            QTreeWidget::item:hover {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.hover_bg)};
            }}
        """)

        # Build inheritance hierarchy
        self._populate_inheritance_tree(tree)

        # Connect double-click to navigation
        tree.itemDoubleClicked.connect(self._on_tree_item_double_clicked)

        return tree

    def _populate_inheritance_tree(self, tree: QTreeWidget):
        """Populate the inheritance tree with only dataclasses visible in the UI."""
        import dataclasses

        # Create root item for the main config class
        config_name = self.config_class.__name__ if self.config_class else "Configuration"
        root_item = QTreeWidgetItem([config_name])
        root_item.setData(0, Qt.ItemDataRole.UserRole, {'type': 'dataclass', 'class': self.config_class})
        tree.addTopLevelItem(root_item)

        # Only show dataclasses that are visible in the UI (have form sections)
        if dataclasses.is_dataclass(self.config_class):
            self._add_ui_visible_dataclasses_to_tree(root_item, self.config_class)

        # Expand the tree
        tree.expandAll()

    def _add_ui_visible_dataclasses_to_tree(self, parent_item: QTreeWidgetItem, dataclass_type):
        """Add only dataclasses that are visible in the UI form."""
        import dataclasses

        # Get all fields from this dataclass
        fields = dataclasses.fields(dataclass_type)

        for field in fields:
            field_name = field.name
            field_type = field.type

            # Only show dataclass fields (these appear as sections in the UI)
            if dataclasses.is_dataclass(field_type):
                # Create a child item for this nested dataclass
                field_item = QTreeWidgetItem([f"{field_name} ({field_type.__name__})"])
                field_item.setData(0, Qt.ItemDataRole.UserRole, {
                    'type': 'dataclass',
                    'class': field_type,
                    'field_name': field_name
                })
                parent_item.addChild(field_item)

                # Show inheritance hierarchy for this dataclass
                self._add_inheritance_info(field_item, field_type)

                # Recursively add nested dataclasses
                self._add_ui_visible_dataclasses_to_tree(field_item, field_type)

    def _add_inheritance_info(self, parent_item: QTreeWidgetItem, dataclass_type):
        """Add inheritance information for a dataclass with proper hierarchy, skipping lazy classes."""
        # Get direct base classes, skipping lazy versions
        direct_bases = []
        for cls in dataclass_type.__bases__:
            if (cls.__name__ != 'object' and
                hasattr(cls, '__dataclass_fields__') and
                not cls.__name__.startswith('Lazy')):  # Skip lazy dataclass wrappers
                direct_bases.append(cls)

        # Add base classes directly as children (no "Inherits from:" label)
        for base_class in direct_bases:
            base_item = QTreeWidgetItem([base_class.__name__])
            base_item.setData(0, Qt.ItemDataRole.UserRole, {
                'type': 'inheritance_link',
                'target_class': base_class
            })
            parent_item.addChild(base_item)

            # Recursively add inheritance for this base class
            self._add_inheritance_info(base_item, base_class)

    def _on_tree_item_double_clicked(self, item: QTreeWidgetItem, column: int):
        """Handle tree item double-clicks for navigation."""
        data = item.data(0, Qt.ItemDataRole.UserRole)
        if not data:
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
            # Find and navigate to the target class in the tree
            target_class = data.get('target_class')
            if target_class:
                self._navigate_to_class_in_tree(target_class)
                logger.debug(f"Navigating to inherited class: {target_class.__name__}")

    def _navigate_to_class_in_tree(self, target_class):
        """Find and highlight a class in the tree."""
        # Search through all items in the tree to find the target class
        root = self.tree_widget.invisibleRootItem()
        self._search_and_highlight_class(root, target_class)

    def _search_and_highlight_class(self, parent_item, target_class):
        """Recursively search for and highlight a class in the tree."""
        for i in range(parent_item.childCount()):
            child = parent_item.child(i)
            data = child.data(0, Qt.ItemDataRole.UserRole)

            if data and data.get('type') == 'dataclass':
                if data.get('class') == target_class:
                    # Found the target - select and scroll to it
                    self.tree_widget.setCurrentItem(child)
                    self.tree_widget.scrollToItem(child)
                    return True

            # Recursively search children
            if self._search_and_highlight_class(child, target_class):
                return True

        return False

    def _scroll_to_section(self, field_name: str):
        """Scroll to a specific section in the form."""
        try:
            # Check if we have a scroll area
            if hasattr(self, 'scroll_area') and self.scroll_area:
                # Find the group box for this field name
                form_widget = self.scroll_area.widget()
                if form_widget:
                    group_box = self._find_group_box_by_name(form_widget, field_name)
                    if group_box:
                        # Scroll to the group box with small margins for better visibility
                        self.scroll_area.ensureWidgetVisible(group_box, 20, 20)
                        logger.debug(f"Scrolled to section: {field_name}")
                        return

            # Fallback: try to scroll to form manager directly if no scroll area
            if hasattr(self.form_manager, 'nested_managers') and field_name in self.form_manager.nested_managers:
                nested_manager = self.form_manager.nested_managers[field_name]
                if hasattr(self, 'scroll_area') and self.scroll_area:
                    self.scroll_area.ensureWidgetVisible(nested_manager, 20, 20)
                    logger.debug(f"Scrolled to nested manager: {field_name}")
                    return

            logger.debug(f"Could not find section to scroll to: {field_name}")
        except Exception as e:
            logger.warning(f"Error scrolling to section {field_name}: {e}")

    def _find_group_box_by_name(self, parent_widget, field_name: str):
        """Recursively find a group box by field name."""
        from PyQt6.QtWidgets import QGroupBox

        # Look for QGroupBox widgets with matching titles
        group_boxes = parent_widget.findChildren(QGroupBox)

        for group_box in group_boxes:
            title = group_box.title()
            # Check if field name matches the title (case insensitive)
            if (field_name.lower() in title.lower() or
                title.lower().replace(' ', '_') == field_name.lower() or
                field_name.lower().replace('_', ' ') in title.lower()):
                logger.debug(f"Found matching group box: '{title}' for field '{field_name}'")
                return group_box

        # Also check object names as fallback
        for child in parent_widget.findChildren(QWidget):
            if hasattr(child, 'objectName') and child.objectName():
                if field_name.lower() in child.objectName().lower():
                    logger.debug(f"Found matching widget by object name: '{child.objectName()}' for field '{field_name}'")
                    return child

        logger.debug(f"No matching section found for field: {field_name}")
        # Debug: print all group box titles to help troubleshoot
        all_titles = [gb.title() for gb in group_boxes]
        logger.debug(f"Available group box titles: {all_titles}")

        return None




    

    
    def create_button_panel(self) -> QWidget:
        """
        Create the button panel.
        
        Returns:
            Widget containing action buttons
        """
        panel = QFrame()
        panel.setFrameStyle(QFrame.Shape.Box)
        panel.setStyleSheet(f"""
            QFrame {{
                background-color: {self.color_scheme.to_hex(self.color_scheme.panel_bg)};
                border: 1px solid {self.color_scheme.to_hex(self.color_scheme.border_color)};
                border-radius: 3px;
                padding: 10px;
            }}
        """)
        
        layout = QHBoxLayout(panel)
        layout.addStretch()
        
        # Reset button
        reset_button = QPushButton("Reset to Defaults")
        reset_button.setMinimumWidth(120)
        reset_button.clicked.connect(self.reset_to_defaults)
        button_styles = self.style_generator.generate_config_button_styles()
        reset_button.setStyleSheet(button_styles["reset"])
        layout.addWidget(reset_button)
        
        layout.addSpacing(10)
        
        # Cancel button
        cancel_button = QPushButton("Cancel")
        cancel_button.setMinimumWidth(80)
        cancel_button.clicked.connect(self.reject)
        cancel_button.setStyleSheet(button_styles["cancel"])
        layout.addWidget(cancel_button)
        
        # Save button
        save_button = QPushButton("Save")
        save_button.setMinimumWidth(80)
        save_button.clicked.connect(self.save_config)
        save_button.setStyleSheet(button_styles["save"])
        layout.addWidget(save_button)
        
        return panel
    



    
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
        self.form_manager.refresh_placeholder_text()

        logger.debug("Reset all parameters using enhanced ParameterFormManager service")

    def refresh_config(self, new_config):
        """Refresh the config window with new configuration data.

        This is called when the underlying configuration changes (e.g., from tier 3 edits)
        to keep the UI in sync with the actual data.

        Args:
            new_config: New configuration instance to display
        """
        try:
            # Import required services
            from openhcs.core.lazy_placeholder import LazyDefaultPlaceholderService

            # Update the current config
            self.current_config = new_config

            # Determine placeholder prefix based on actual instance type (same logic as __init__)
            is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(type(new_config))
            placeholder_prefix = "Pipeline default" if is_lazy_dataclass else "Default"

            # SIMPLIFIED: Create new form manager with dual-axis resolution
            root_field_id = type(new_config).__name__  # e.g., "GlobalPipelineConfig" or "PipelineConfig"

            # Use new context system instead of ContextEventCoordinator
            if self.orchestrator:
                with config_context(self.orchestrator):
                    new_form_manager = ParameterFormManager.from_dataclass_instance(
                        dataclass_instance=new_config,
                        field_id=root_field_id,
                        placeholder_prefix=placeholder_prefix,
                        color_scheme=self.color_scheme,
                        use_scroll_area=True,
                        global_config_type=GlobalPipelineConfig,  # FIXED: Always use GlobalPipelineConfig for dual-axis resolution
                        context_event_coordinator=None,  # No longer needed with new context system
                        context_obj=self.orchestrator  # Pass orchestrator as generic context object
                    )
            else:
                new_form_manager = ParameterFormManager.from_dataclass_instance(
                    dataclass_instance=new_config,
                    field_id=root_field_id,
                    placeholder_prefix=placeholder_prefix,
                    color_scheme=self.color_scheme,
                    use_scroll_area=True,
                    global_config_type=GlobalPipelineConfig,  # FIXED: Always use GlobalPipelineConfig for dual-axis resolution
                    context_event_coordinator=None  # No longer needed with new context system
                )

            # Find and replace the form widget in the layout
            # Layout structure: [0] header, [1] form/scroll_area, [2] buttons
            layout = self.layout()
            if layout.count() >= 2:
                # Get the form container (might be scroll area or direct form)
                form_container_item = layout.itemAt(1)
                if form_container_item:
                    old_container = form_container_item.widget()

                    # Remove old container from layout
                    layout.removeItem(form_container_item)

                    # Properly delete old container and its contents
                    if old_container:
                        old_container.deleteLater()

                    # Add new form container at the same position
                    if self._should_use_scroll_area():
                        # Create new scroll area with new form
                        from PyQt6.QtWidgets import QScrollArea
                        from PyQt6.QtCore import Qt
                        scroll_area = QScrollArea()
                        scroll_area.setWidgetResizable(True)
                        scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
                        scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
                        scroll_area.setWidget(new_form_manager)
                        layout.insertWidget(1, scroll_area)
                    else:
                        # Add form directly
                        layout.insertWidget(1, new_form_manager)

                    # Update the form manager reference
                    self.form_manager = new_form_manager

                    logger.debug(f"Config window refreshed with new {type(new_config).__name__}")
                else:
                    logger.error("Could not find form container in layout")
            else:
                logger.error(f"Layout has insufficient items: {layout.count()}")

        except Exception as e:
            logger.error(f"Failed to refresh config window: {e}")
            import traceback
            logger.error(f"Traceback: {traceback.format_exc()}")

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

            # Emit signal and call callback
            self.config_saved.emit(new_config)

            if self.on_save_callback:
                self.on_save_callback(new_config)

            self.accept()

        except Exception as e:
            logger.error(f"Failed to save configuration: {e}")
            from PyQt6.QtWidgets import QMessageBox
            QMessageBox.critical(self, "Save Error", f"Failed to save configuration:\n{e}")
    

    
    def reject(self):
        """Handle dialog rejection (Cancel button)."""
        self.config_cancelled.emit()
        self._cleanup_signal_connections()
        super().reject()

    def accept(self):
        """Handle dialog acceptance (Save button)."""
        self._cleanup_signal_connections()
        super().accept()

    def closeEvent(self, event):
        """Handle window close event."""
        self._cleanup_signal_connections()
        super().closeEvent(event)

    def _cleanup_signal_connections(self):
        """Clean up signal connections to prevent memory leaks."""
        # The signal connection is handled by the plate manager
        # We just need to mark that this window is closing
        logger.debug("Config window closing, signal connections will be cleaned up")
