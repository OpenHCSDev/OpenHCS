"""
Context manager service for widget signal blocking.

This module provides context managers for blocking PyQt6 widget signals during
programmatic value updates, ensuring signals are always unblocked even on exception.

Key features:
1. Context manager guarantees signal unblocking
2. Supports single or multiple widgets
3. Backward compatible with lambda-based approach
4. Follows OpenHCS context manager pattern

Pattern:
    Instead of:
        widget.blockSignals(True)
        widget.setValue(value)
        widget.blockSignals(False)
    
    Use:
        with SignalBlockingService.block_signals(widget):
            widget.setValue(value)

This guarantees signals are unblocked even if setValue() raises an exception.
"""

from contextlib import contextmanager
from typing import Callable, Optional
from PyQt6.QtWidgets import QWidget
import logging

logger = logging.getLogger(__name__)


class SignalBlockingService:
    """
    Service for blocking widget signals using context managers.
    
    This service provides both context manager and lambda-based approaches
    for blocking widget signals during programmatic updates.
    
    Examples:
        # Context manager (preferred):
        with SignalBlockingService.block_signals(checkbox):
            checkbox.setChecked(True)
        
        # Multiple widgets:
        with SignalBlockingService.block_signals(widget1, widget2, widget3):
            widget1.setValue(1)
            widget2.setValue(2)
            widget3.setValue(3)
        
        # Lambda-based (backward compat):
        SignalBlockingService.with_signals_blocked(widget, lambda: widget.setValue(value))
    """
    
    @staticmethod
    @contextmanager
    def block_signals(*widgets: QWidget):
        """
        Context manager for blocking widget signals.
        
        Blocks signals on all provided widgets on entry, and unblocks them on exit.
        Guarantees signals are unblocked even if an exception occurs.
        
        Args:
            *widgets: One or more QWidget instances to block signals on
        
        Yields:
            None
        
        Example:
            # Single widget:
            with SignalBlockingService.block_signals(checkbox):
                checkbox.setChecked(True)
            
            # Multiple widgets:
            with SignalBlockingService.block_signals(widget1, widget2):
                widget1.setValue(1)
                widget2.setValue(2)
        """
        # Block signals on all widgets
        for widget in widgets:
            if widget is not None:
                widget.blockSignals(True)
                logger.debug(f"Blocked signals on {type(widget).__name__}")
        
        try:
            yield
        finally:
            # Unblock signals on all widgets (guaranteed even on exception)
            for widget in widgets:
                if widget is not None:
                    widget.blockSignals(False)
                    logger.debug(f"Unblocked signals on {type(widget).__name__}")
    
    @staticmethod
    def with_signals_blocked(widget: QWidget, operation: Callable) -> None:
        """
        Execute operation with widget signals blocked (lambda-based approach).
        
        This is a backward-compatible wrapper around block_signals() context manager
        that accepts a lambda/callable instead of using a with statement.
        
        Args:
            widget: Widget to block signals on
            operation: Callable to execute with signals blocked
        
        Example:
            SignalBlockingService.with_signals_blocked(
                checkbox,
                lambda: checkbox.setChecked(True)
            )
        """
        with SignalBlockingService.block_signals(widget):
            operation()
    
    @staticmethod
    @contextmanager
    def block_signals_if(condition: bool, *widgets: QWidget):
        """
        Conditionally block signals based on a condition.
        
        Useful when you want to optionally block signals based on runtime state.
        
        Args:
            condition: If True, block signals. If False, do nothing.
            *widgets: Widgets to block signals on (if condition is True)
        
        Example:
            with SignalBlockingService.block_signals_if(skip_signals, widget):
                widget.setValue(value)
        """
        if condition:
            with SignalBlockingService.block_signals(*widgets):
                yield
        else:
            yield
    
    @staticmethod
    def update_widget_value(widget: QWidget, value, setter: Optional[Callable] = None) -> None:
        """
        Update widget value with signals blocked.
        
        Convenience method that combines signal blocking with value setting.
        
        Args:
            widget: Widget to update
            value: Value to set
            setter: Optional custom setter callable. If None, uses widget-specific defaults.
        
        Example:
            # Auto-detect setter:
            SignalBlockingService.update_widget_value(checkbox, True)
            
            # Custom setter:
            SignalBlockingService.update_widget_value(
                widget,
                value,
                setter=lambda w, v: w.setCustomValue(v)
            )
        """
        with SignalBlockingService.block_signals(widget):
            if setter:
                setter(widget, value)
            else:
                # Auto-detect common widget types
                from PyQt6.QtWidgets import QCheckBox, QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox
                
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
                    # Fallback: try setValue() method
                    if hasattr(widget, 'setValue'):
                        widget.setValue(value)
                    else:
                        raise ValueError(
                            f"Cannot auto-detect setter for {type(widget).__name__}. "
                            f"Provide custom setter callable."
                        )

