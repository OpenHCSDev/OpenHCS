"""
Consolidated Signal Service.

Merges:
- SignalBlockingService: Context managers for widget signal blocking
- SignalConnectionService: Signal wiring for ParameterFormManager
- CrossWindowRegistration: Context manager for cross-window registration

Key features:
1. Context manager guarantees signal unblocking
2. Supports single or multiple widgets
3. Consolidates all signal wiring logic
4. Cross-window registration with RAII cleanup
"""

from contextlib import contextmanager
from typing import Any, Callable, Optional, TYPE_CHECKING
from PyQt6.QtWidgets import QWidget, QCheckBox, QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox
import logging

if TYPE_CHECKING:
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

logger = logging.getLogger(__name__)


class SignalService:
    """
    Consolidated service for signal blocking, connection, and cross-window registration.

    Examples:
        # Block signals (context manager):
        with SignalService.block_signals(checkbox):
            checkbox.setChecked(True)
        
        # Multiple widgets:
        with SignalService.block_signals(widget1, widget2):
            widget1.setValue(1)
            widget2.setValue(2)
        
        # Connect all signals for a manager:
        SignalService.connect_all_signals(manager)
        
        # Cross-window registration:
        with SignalService.cross_window_registration(manager):
            dialog.exec()
    """

    # ========== SIGNAL BLOCKING (from SignalBlockingService) ==========

    @staticmethod
    @contextmanager
    def block_signals(*widgets: QWidget):
        """Context manager for blocking widget signals."""
        for widget in widgets:
            if widget is not None:
                widget.blockSignals(True)
                logger.debug(f"Blocked signals on {type(widget).__name__}")
        
        try:
            yield
        finally:
            for widget in widgets:
                if widget is not None:
                    widget.blockSignals(False)
                    logger.debug(f"Unblocked signals on {type(widget).__name__}")

    @staticmethod
    def with_signals_blocked(widget: QWidget, operation: Callable) -> None:
        """Execute operation with widget signals blocked (lambda-based)."""
        with SignalService.block_signals(widget):
            operation()

    @staticmethod
    @contextmanager
    def block_signals_if(condition: bool, *widgets: QWidget):
        """Conditionally block signals based on a condition."""
        if condition:
            with SignalService.block_signals(*widgets):
                yield
        else:
            yield

    @staticmethod
    def update_widget_value(widget: QWidget, value, setter: Optional[Callable] = None) -> None:
        """Update widget value with signals blocked."""
        with SignalService.block_signals(widget):
            if setter:
                setter(widget, value)
            else:
                if isinstance(widget, QCheckBox):
                    widget.setChecked(value)
                elif isinstance(widget, QLineEdit):
                    widget.setText(str(value) if value is not None else "")
                elif isinstance(widget, QComboBox):
                    if isinstance(value, int):
                        widget.setCurrentIndex(value)
                    else:
                        widget.setCurrentText(str(value))
                elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
                    widget.setValue(value)
                else:
                    if hasattr(widget, 'setValue'):
                        widget.setValue(value)
                    else:
                        raise ValueError(f"Cannot auto-detect setter for {type(widget).__name__}")

    # ========== SIGNAL CONNECTION (from SignalConnectionService) ==========

    @staticmethod
    def connect_all_signals(manager: Any) -> None:
        """Wire all signals for the manager."""
        def on_parameter_changed(param_name, value):
            if not getattr(manager, '_in_reset', False) and param_name != 'enabled' and manager._parent_manager is None:
                manager._parameter_ops_service.refresh_with_live_context(manager)

        manager.parameter_changed.connect(on_parameter_changed)
        
        if 'enabled' in manager.parameters:
            manager.parameter_changed.connect(manager._on_enabled_field_changed_universal)
            manager._on_placeholder_refresh_complete_callbacks.append(
                lambda: manager._enabled_field_styling_service.apply_initial_enabled_styling(manager)
            )
        
        manager.destroyed.connect(manager.unregister_from_cross_window_updates)

    @staticmethod
    def register_cross_window_signals(manager: Any) -> None:
        """Register manager for cross-window updates (only root managers)."""
        if manager._parent_manager is not None:
            return
        
        from dataclasses import is_dataclass
        if hasattr(manager.config, '_resolve_field_value'):
            manager._initial_values_on_open = manager.get_user_modified_values()
        else:
            manager._initial_values_on_open = manager.get_current_values()
        
        manager.parameter_changed.connect(manager._emit_cross_window_change)

        existing_count = len(manager._active_form_managers) - 1
        logger.info(f"🔍 REGISTER: {manager.field_id} connecting to {existing_count} existing managers")

        for existing_manager in manager._active_form_managers:
            if existing_manager is manager:
                continue
            manager.context_value_changed.connect(existing_manager._on_cross_window_context_changed)
            manager.context_refreshed.connect(existing_manager._on_cross_window_context_refreshed)
            existing_manager.context_value_changed.connect(manager._on_cross_window_context_changed)
            existing_manager.context_refreshed.connect(manager._on_cross_window_context_refreshed)

        logger.info(f"🔍 REGISTER: {manager.field_id} (id={id(manager)}) registered. Total: {len(manager._active_form_managers)}")

    # ========== CROSS-WINDOW REGISTRATION (from CrossWindowRegistration) ==========

    @staticmethod
    @contextmanager
    def cross_window_registration(manager: 'ParameterFormManager'):
        """
        Context manager for cross-window registration.

        Ensures proper registration and cleanup of form managers for cross-window updates.
        """
        if manager._parent_manager is not None:
            yield manager
            return

        try:
            SignalService.register_cross_window_signals(manager)
            yield manager
        finally:
            manager.unregister_from_cross_window_updates()

