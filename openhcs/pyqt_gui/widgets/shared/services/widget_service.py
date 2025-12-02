"""
Consolidated Widget Service.

Merges:
- WidgetFinderService: Finding widgets in ParameterFormManager
- WidgetStylingService: Read-only styling, dimming, visual state management
- WidgetUpdateService: Low-level widget value update operations

Key features:
1. Centralized widget finding, styling, and update logic
2. Type-safe widget retrieval with fail-loud behavior
3. Signal blocking during value updates
4. Read-only styling that maintains normal appearance
"""

from typing import Any, Optional, List, Type, Callable
from PyQt6.QtWidgets import (
    QWidget, QCheckBox, QLineEdit, QSpinBox, QDoubleSpinBox, 
    QComboBox, QTextEdit, QAbstractSpinBox
)
from PyQt6.QtCore import Qt
import logging

logger = logging.getLogger(__name__)


class WidgetService:
    """
    Consolidated service for widget finding, styling, and value updates.

    Examples:
        service = WidgetService()
        
        # Find widgets:
        checkbox = WidgetService.find_optional_checkbox(manager, param_name)
        widget = WidgetService.get_widget_safe(manager, param_name)
        
        # Style widgets:
        WidgetService.make_readonly(widget, color_scheme)
        WidgetService.apply_dimming(widget, opacity=0.5)
        
        # Update widget values:
        service.update_widget_value(widget, value, param_name, manager=manager)
    """

    def __init__(self):
        """Initialize widget service with dependencies."""
        from openhcs.ui.shared.widget_operations import WidgetOperations
        from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer

        self.widget_ops = WidgetOperations
        self.widget_enhancer = PyQt6WidgetEnhancer

    # ========== WIDGET FINDING (from WidgetFinderService) ==========

    @staticmethod
    def find_optional_checkbox(manager, param_name: str) -> Optional[QCheckBox]:
        """Find optional checkbox for a parameter."""
        if param_name not in manager.widgets:
            logger.debug(f"No widget for param_name={param_name}")
            return None
        
        container = manager.widgets[param_name]
        ids = manager.service.generate_field_ids_direct(manager.config.field_id, param_name)
        checkbox = container.findChild(QCheckBox, ids['optional_checkbox_id'])
        
        if checkbox:
            logger.debug(f"Found optional checkbox for param_name={param_name}")
        return checkbox

    @staticmethod
    def find_nested_checkbox(manager, param_name: str) -> Optional[QCheckBox]:
        """Find checkbox in nested manager's container."""
        if param_name not in manager.widgets:
            return None
        
        container = manager.widgets[param_name]
        ids = manager.service.generate_field_ids_direct(manager.config.field_id, param_name)
        return container.findChild(QCheckBox, ids['optional_checkbox_id'])

    @staticmethod
    def find_group_box(container: QWidget, group_box_type: Type = None) -> Optional[QWidget]:
        """Find group box within container."""
        if group_box_type is None:
            try:
                from openhcs.pyqt_gui.widgets.shared.clickable_help_components import GroupBoxWithHelp
                group_box_type = GroupBoxWithHelp
            except ImportError:
                logger.warning("Could not import GroupBoxWithHelp")
                return None
        
        return container.findChild(group_box_type)

    @staticmethod
    def get_widget_safe(manager, param_name: str) -> Optional[QWidget]:
        """Safely get a widget from manager's widgets dict."""
        widget = manager.widgets.get(param_name)
        if widget:
            logger.debug(f"Found widget for param_name={param_name}, type={type(widget).__name__}")
        return widget

    @staticmethod
    def find_all_input_widgets(container: QWidget, widget_ops) -> List[QWidget]:
        """Find all input widgets within a container."""
        widgets = widget_ops.get_all_value_widgets(container)
        logger.debug(f"Found {len(widgets)} input widgets in container")
        return widgets

    # ========== WIDGET STYLING (from WidgetStylingService) ==========

    @staticmethod
    def make_readonly(widget: QWidget, color_scheme) -> None:
        """Make a widget read-only without greying it out."""
        if isinstance(widget, (QLineEdit, QTextEdit)):
            widget.setReadOnly(True)
            widget.setStyleSheet(f"color: {color_scheme.to_hex(color_scheme.text_primary)};")
        elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
            widget.setReadOnly(True)
            widget.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
            widget.setStyleSheet(f"color: {color_scheme.to_hex(color_scheme.text_primary)};")
        elif isinstance(widget, QComboBox):
            widget.setEnabled(False)
            widget.setStyleSheet(f"""
                QComboBox:disabled {{
                    color: {color_scheme.to_hex(color_scheme.text_primary)};
                    background-color: {color_scheme.to_hex(color_scheme.input_bg)};
                }}
            """)
        elif isinstance(widget, QCheckBox):
            widget.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
            widget.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        else:
            logger.warning(f"No read-only styling for {type(widget).__name__}")

    @staticmethod
    def apply_dimming(widget: QWidget, opacity: float = 0.5) -> None:
        """Apply visual dimming to a widget."""
        if not (0.0 <= opacity <= 1.0):
            raise ValueError(f"Opacity must be 0.0-1.0, got {opacity}")
        widget.setWindowOpacity(opacity)

    @staticmethod
    def remove_dimming(widget: QWidget) -> None:
        """Remove visual dimming from a widget."""
        widget.setWindowOpacity(1.0)

    @staticmethod
    def set_enabled_with_styling(widget: QWidget, enabled: bool, color_scheme=None) -> None:
        """Set widget enabled state with appropriate styling."""
        if enabled:
            widget.setEnabled(True)
            if isinstance(widget, (QLineEdit, QTextEdit)):
                widget.setReadOnly(False)
                widget.setStyleSheet("")
            elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
                widget.setReadOnly(False)
                widget.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.UpDownArrows)
                widget.setStyleSheet("")
            elif isinstance(widget, QCheckBox):
                widget.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, False)
                widget.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        else:
            if color_scheme:
                WidgetService.make_readonly(widget, color_scheme)
            else:
                widget.setEnabled(False)

    @staticmethod
    def clear_stylesheet(widget: QWidget) -> None:
        """Clear widget's stylesheet."""
        widget.setStyleSheet("")

    @staticmethod
    def apply_error_styling(widget: QWidget, color_scheme) -> None:
        """Apply error styling to a widget."""
        if hasattr(color_scheme, 'error'):
            error_color = color_scheme.to_hex(color_scheme.error)
            widget.setStyleSheet(f"border: 2px solid {error_color};")

    @staticmethod
    def remove_error_styling(widget: QWidget) -> None:
        """Remove error styling from a widget."""
        WidgetService.clear_stylesheet(widget)

    # ========== WIDGET VALUE UPDATES (from WidgetUpdateService) ==========

    def update_widget_value(
        self,
        widget: QWidget,
        value: Any,
        param_name: Optional[str] = None,
        skip_context_behavior: bool = False,
        manager=None
    ) -> None:
        """Update widget value with signal blocking and optional placeholder application."""
        self._execute_with_signal_blocking(widget, lambda: self._dispatch_widget_update(widget, value))

        if not skip_context_behavior and manager:
            self._apply_context_behavior(widget, value, param_name, manager)

    def _execute_with_signal_blocking(self, widget: QWidget, operation: Callable) -> None:
        """Execute operation with widget signals blocked."""
        widget.blockSignals(True)
        operation()
        widget.blockSignals(False)

    def _dispatch_widget_update(self, widget: QWidget, value: Any) -> None:
        """Dispatch widget update using ABC-based operations."""
        self.widget_ops.set_value(widget, value)

    def _apply_context_behavior(
        self,
        widget: QWidget,
        value: Any,
        param_name: str,
        manager
    ) -> None:
        """Apply placeholder behavior based on value."""
        logger.info(f"        🎨 _apply_context_behavior: {manager.field_id}.{param_name}, value={repr(value)[:30]}")

        if not param_name or not manager.object_instance:
            logger.warning(f"        ⏭️  No param_name or object_instance, skipping")
            return

        if value is None:
            logger.info(f"        ✅ Value is None, computing placeholder...")
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
            from openhcs.config_framework.context_manager import config_context

            # Use ROOT manager type for live context cache sharing
            root_manager = manager
            while getattr(root_manager, '_parent_manager', None) is not None:
                root_manager = root_manager._parent_manager

            live_context = ParameterFormManager.collect_live_context(
                scope_filter=manager.scope_id,
                for_type=type(root_manager.object_instance)
            )

            from contextlib import ExitStack
            with ExitStack() as stack:
                if manager.context_obj is not None:
                    stack.enter_context(config_context(manager.context_obj))

                if manager.object_instance and manager.parameters:
                    try:
                        import dataclasses
                        if dataclasses.is_dataclass(type(manager.object_instance)):
                            overlay_dict = manager.parameters.copy()
                            for excluded_param in getattr(manager, 'exclude_params', []):
                                if excluded_param not in overlay_dict and hasattr(manager.object_instance, excluded_param):
                                    overlay_dict[excluded_param] = getattr(manager.object_instance, excluded_param)
                            overlay_instance = type(manager.object_instance)(**overlay_dict)
                            stack.enter_context(config_context(overlay_instance))
                    except Exception:
                        pass

                placeholder_text = manager.service.get_placeholder_text(param_name, type(manager.object_instance))
                logger.info(f"        📝 Placeholder text: {repr(placeholder_text)[:50]}")
                if placeholder_text:
                    self.widget_enhancer.apply_placeholder_text(widget, placeholder_text)
                    logger.info(f"        ✅ Applied placeholder")
                else:
                    logger.warning(f"        ⚠️  No placeholder text returned")
        elif value is not None:
            logger.info(f"        🧹 Value not None, clearing placeholder state")
            self.widget_enhancer._clear_placeholder_state(widget)

    def clear_widget_to_default_state(self, widget: QWidget) -> None:
        """Clear widget to its default/empty state for reset operations."""
        if isinstance(widget, QLineEdit):
            widget.clear()
        elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
            widget.setValue(widget.minimum())
        elif isinstance(widget, QComboBox):
            widget.setCurrentIndex(-1)
        elif isinstance(widget, QCheckBox):
            widget.setChecked(False)
        elif isinstance(widget, QTextEdit):
            widget.clear()
        else:
            widget.clear()

    def update_combo_box(self, widget: QComboBox, value: Any) -> None:
        """Update combo box with value matching."""
        widget.setCurrentIndex(
            -1 if value is None else
            next((i for i in range(widget.count()) if widget.itemData(i) == value), -1)
        )

    def update_checkbox_group(self, widget: QWidget, value: Any) -> None:
        """Update checkbox group using functional operations."""
        if isinstance(value, list):
            [cb.setChecked(False) for cb in widget._checkboxes.values()]
            [widget._checkboxes[v].setChecked(True) for v in value if v in widget._checkboxes]

    def get_widget_value(self, widget: QWidget) -> Any:
        """Get widget value using ABC-based polymorphism."""
        if widget.property("is_placeholder_state"):
            return None

        from openhcs.ui.shared.widget_protocols import ValueGettable
        if isinstance(widget, ValueGettable):
            return widget.get_value()

        return None
