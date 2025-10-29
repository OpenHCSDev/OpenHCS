"""
Widget Update Service - Low-level widget value update operations.

Extracts all low-level widget update logic from ParameterFormManager.
Handles signal blocking, value dispatch, and placeholder application.
"""

from typing import Any, Optional
from PyQt6.QtWidgets import QWidget, QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox, QCheckBox, QTextEdit
import logging

logger = logging.getLogger(__name__)


class WidgetUpdateService:
    """
    Service for updating widget values with signal blocking and placeholder handling.

    Stateless service that encapsulates all low-level widget update operations.
    """

    def __init__(self):
        """Initialize widget update service (stateless - no dependencies)."""
        from openhcs.ui.shared.widget_operations import WidgetOperations
        from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer

        self.widget_ops = WidgetOperations
        self.widget_enhancer = PyQt6WidgetEnhancer
    
    def update_widget_value(
        self,
        widget: QWidget,
        value: Any,
        param_name: Optional[str] = None,
        skip_context_behavior: bool = False,
        manager=None
    ) -> None:
        """
        Update widget value with signal blocking and optional placeholder application.
        
        Args:
            widget: Widget to update
            value: New value to set
            param_name: Parameter name (for placeholder resolution)
            skip_context_behavior: If True, skip placeholder application (e.g., during reset)
            manager: ParameterFormManager instance (for context resolution)
        """
        # Update widget value with signal blocking
        self._execute_with_signal_blocking(widget, lambda: self._dispatch_widget_update(widget, value))
        
        # Apply placeholder behavior if not skipped
        if not skip_context_behavior and manager:
            self._apply_context_behavior(widget, value, param_name, manager)
    
    def _execute_with_signal_blocking(self, widget: QWidget, operation: callable) -> None:
        """
        Execute operation with widget signals blocked.
        
        Prevents signal emission during programmatic value updates.
        """
        widget.blockSignals(True)
        operation()
        widget.blockSignals(False)
    
    def _dispatch_widget_update(self, widget: QWidget, value: Any) -> None:
        """
        Dispatch widget update using ABC-based operations.
        
        ANTI-DUCK-TYPING: Uses ABC-based dispatch - fails loud if widget doesn't implement ValueSettable.
        """
        self.widget_ops.set_value(widget, value)
    
    def _apply_context_behavior(
        self,
        widget: QWidget,
        value: Any,
        param_name: str,
        manager
    ) -> None:
        """
        Apply placeholder behavior based on value.
        
        If value is None, resolve and apply placeholder text.
        If value is not None, clear placeholder state.
        
        Args:
            widget: Widget to apply placeholder to
            value: Current value
            param_name: Parameter name (for placeholder resolution)
            manager: ParameterFormManager instance (for context resolution)
        """
        if not param_name or not manager.dataclass_type:
            return
        
        if value is None:
            # Build overlay from current form state
            overlay = manager.get_current_values()

            # Build context stack for placeholder resolution
            from openhcs.pyqt_gui.widgets.shared.context_layer_builders import build_context_stack
            with build_context_stack(manager, overlay):
                placeholder_text = manager.service.get_placeholder_text(param_name, manager.dataclass_type)
                if placeholder_text:
                    self.widget_enhancer.apply_placeholder_text(widget, placeholder_text)
        elif value is not None:
            self.widget_enhancer._clear_placeholder_state(widget)
    
    def clear_widget_to_default_state(self, widget: QWidget) -> None:
        """
        Clear widget to its default/empty state for reset operations.
        
        ANTI-DUCK-TYPING: All widgets should have clear() - fails loud if not.
        """
        if isinstance(widget, QLineEdit):
            widget.clear()
        elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
            widget.setValue(widget.minimum())
        elif isinstance(widget, QComboBox):
            widget.setCurrentIndex(-1)  # No selection
        elif isinstance(widget, QCheckBox):
            widget.setChecked(False)
        elif isinstance(widget, QTextEdit):
            widget.clear()
        else:
            # ANTI-DUCK-TYPING: All widgets should have clear() - fail loud if not
            widget.clear()
    
    def update_combo_box(self, widget: QComboBox, value: Any) -> None:
        """Update combo box with value matching."""
        widget.setCurrentIndex(
            -1 if value is None else
            next((i for i in range(widget.count()) if widget.itemData(i) == value), -1)
        )
    
    def update_checkbox_group(self, widget: QWidget, value: Any) -> None:
        """
        Update checkbox group using functional operations.
        
        ANTI-DUCK-TYPING: Widget must have _checkboxes attribute - fail loud if not.
        """
        if isinstance(value, list):
            # Functional: reset all, then set selected
            [cb.setChecked(False) for cb in widget._checkboxes.values()]
            [widget._checkboxes[v].setChecked(True) for v in value if v in widget._checkboxes]
    
    def get_widget_value(self, widget: QWidget) -> Any:
        """
        Get widget value using ABC-based polymorphism.

        Returns None if:
        - Widget is in placeholder state
        - Widget doesn't implement ValueGettable (container widgets like GroupBoxWithHelp)

        This allows get_current_values() to iterate over all widgets without special casing.
        """
        # Check placeholder state first
        if widget.property("is_placeholder_state"):
            return None

        # Polymorphic: if widget implements ValueGettable, get its value; otherwise None
        from openhcs.ui.shared.widget_protocols import ValueGettable
        if isinstance(widget, ValueGettable):
            return widget.get_value()

        # Container widgets (GroupBoxWithHelp, etc) don't have values - return None
        return None

