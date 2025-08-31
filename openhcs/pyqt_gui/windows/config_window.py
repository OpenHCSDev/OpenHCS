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
    QScrollArea, QWidget, QFrame,
    QLineEdit, QSpinBox, QDoubleSpinBox, QCheckBox, QComboBox
)
from PyQt6.QtCore import Qt, pyqtSignal
from PyQt6.QtGui import QFont

# Infrastructure classes removed - functionality migrated to ParameterFormManager service layer
from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
from openhcs.pyqt_gui.shared.style_generator import StyleSheetGenerator
from openhcs.pyqt_gui.shared.color_scheme import PyQt6ColorScheme
from openhcs.core.config import GlobalPipelineConfig



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

        # Determine placeholder prefix based on actual instance type (not class type)
        from openhcs.core.config import LazyDefaultPlaceholderService
        is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(type(current_config))
        placeholder_prefix = "Pipeline default" if is_lazy_dataclass else "Default"

        # Always use ParameterFormManager with dataclass editing mode - unified approach
        self.form_manager = ParameterFormManager.from_dataclass_instance(
            dataclass_instance=current_config,
            field_id="config",
            placeholder_prefix=placeholder_prefix,
            color_scheme=self.color_scheme,
            use_scroll_area=True
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
        
        # Parameter form - always use form_manager (unified approach)
        if self._should_use_scroll_area():
            scroll_area = QScrollArea()
            scroll_area.setWidgetResizable(True)
            scroll_area.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
            scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
            scroll_area.setWidget(self.form_manager)
            layout.addWidget(scroll_area)
        else:
            # For simple dataclasses, show form directly without scrolling
            layout.addWidget(self.form_manager)
        
        # Button panel
        button_panel = self.create_button_panel()
        layout.addWidget(button_panel)
        
        # Apply centralized styling
        self.setStyleSheet(self.style_generator.generate_config_window_style())
    

    

    

    
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
            # Update the current config
            self.current_config = new_config

            # Determine placeholder prefix based on actual instance type (same logic as __init__)
            from openhcs.core.config import LazyDefaultPlaceholderService
            is_lazy_dataclass = LazyDefaultPlaceholderService.has_lazy_resolution(type(new_config))
            placeholder_prefix = "Pipeline default" if is_lazy_dataclass else "Default"

            # Create new form manager with the new config
            new_form_manager = ParameterFormManager.from_dataclass_instance(
                dataclass_instance=new_config,
                field_id="config",
                placeholder_prefix=placeholder_prefix,
                color_scheme=self.color_scheme,
                use_scroll_area=True
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
            # ConfigWindow owns dataclass reconstruction - proper separation of concerns
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
