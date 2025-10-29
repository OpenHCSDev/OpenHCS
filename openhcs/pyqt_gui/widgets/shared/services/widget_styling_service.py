"""
Service for widget styling operations.

This module provides styling utilities for widgets, including read-only styling,
dimming, and visual state management.

Key features:
1. Type-specific read-only styling
2. Maintains normal appearance (no greying out)
3. Color scheme aware
4. Supports dimming/undimming
5. Centralized styling logic

Pattern:
    Instead of:
        if isinstance(widget, QLineEdit):
            widget.setReadOnly(True)
            widget.setStyleSheet(f"color: {color};")
        elif isinstance(widget, QSpinBox):
            widget.setReadOnly(True)
            widget.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
            # ... etc
    
    Use:
        WidgetStylingService.make_readonly(widget, color_scheme)
"""

from typing import Optional
from PyQt6.QtWidgets import (
    QWidget, QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox,
    QTextEdit, QCheckBox, QAbstractSpinBox
)
from PyQt6.QtCore import Qt
import logging

logger = logging.getLogger(__name__)


class WidgetStylingService:
    """
    Service for widget styling operations.
    
    This service consolidates all widget styling logic, including read-only styling,
    dimming, and visual state management.
    
    Examples:
        # Make widget read-only:
        WidgetStylingService.make_readonly(widget, color_scheme)
        
        # Apply dimming:
        WidgetStylingService.apply_dimming(widget, opacity=0.5)
        
        # Remove dimming:
        WidgetStylingService.remove_dimming(widget)
    """
    
    @staticmethod
    def make_readonly(widget: QWidget, color_scheme) -> None:
        """
        Make a widget read-only without greying it out.
        
        This applies type-specific read-only styling that maintains normal appearance
        while preventing user interaction.
        
        Args:
            widget: Widget to make read-only
            color_scheme: Color scheme for styling (must have text_primary and input_bg attributes)
        
        Example:
            WidgetStylingService.make_readonly(line_edit, self.config.color_scheme)
        """
        if isinstance(widget, (QLineEdit, QTextEdit)):
            widget.setReadOnly(True)
            # Keep normal text color
            widget.setStyleSheet(
                f"color: {color_scheme.to_hex(color_scheme.text_primary)};"
            )
            logger.debug(f"Made {type(widget).__name__} read-only with normal text color")
        
        elif isinstance(widget, (QSpinBox, QDoubleSpinBox)):
            widget.setReadOnly(True)
            widget.setButtonSymbols(QAbstractSpinBox.ButtonSymbols.NoButtons)
            # Keep normal text color
            widget.setStyleSheet(
                f"color: {color_scheme.to_hex(color_scheme.text_primary)};"
            )
            logger.debug(f"Made {type(widget).__name__} read-only with no buttons")
        
        elif isinstance(widget, QComboBox):
            # Disable but keep normal appearance
            widget.setEnabled(False)
            widget.setStyleSheet(f"""
                QComboBox:disabled {{
                    color: {color_scheme.to_hex(color_scheme.text_primary)};
                    background-color: {color_scheme.to_hex(color_scheme.input_bg)};
                }}
            """)
            logger.debug(f"Made QComboBox read-only with normal appearance")
        
        elif isinstance(widget, QCheckBox):
            # Make non-interactive but keep normal appearance
            widget.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
            widget.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            logger.debug(f"Made QCheckBox read-only (non-interactive)")
        
        else:
            logger.warning(
                f"No read-only styling defined for {type(widget).__name__}. "
                f"Widget will remain interactive."
            )
    
    @staticmethod
    def apply_dimming(widget: QWidget, opacity: float = 0.5) -> None:
        """
        Apply visual dimming to a widget.
        
        This reduces the widget's opacity to indicate it's disabled or inactive.
        
        Args:
            widget: Widget to dim
            opacity: Opacity level (0.0 = fully transparent, 1.0 = fully opaque)
        
        Example:
            WidgetStylingService.apply_dimming(widget, opacity=0.5)
        """
        if not (0.0 <= opacity <= 1.0):
            raise ValueError(f"Opacity must be between 0.0 and 1.0, got {opacity}")
        
        widget.setWindowOpacity(opacity)
        logger.debug(f"Applied dimming to {type(widget).__name__} with opacity={opacity}")
    
    @staticmethod
    def remove_dimming(widget: QWidget) -> None:
        """
        Remove visual dimming from a widget.
        
        This restores the widget's opacity to fully opaque.
        
        Args:
            widget: Widget to undim
        
        Example:
            WidgetStylingService.remove_dimming(widget)
        """
        widget.setWindowOpacity(1.0)
        logger.debug(f"Removed dimming from {type(widget).__name__}")
    
    @staticmethod
    def set_enabled_with_styling(widget: QWidget, enabled: bool, color_scheme=None) -> None:
        """
        Set widget enabled state with appropriate styling.
        
        When disabling, applies read-only styling to maintain normal appearance.
        When enabling, removes read-only styling.
        
        Args:
            widget: Widget to enable/disable
            enabled: True to enable, False to disable
            color_scheme: Optional color scheme for read-only styling
        
        Example:
            WidgetStylingService.set_enabled_with_styling(widget, False, color_scheme)
        """
        if enabled:
            widget.setEnabled(True)
            # Remove read-only styling
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
            
            logger.debug(f"Enabled {type(widget).__name__} with normal styling")
        else:
            if color_scheme:
                WidgetStylingService.make_readonly(widget, color_scheme)
            else:
                widget.setEnabled(False)
                logger.debug(f"Disabled {type(widget).__name__} (no color scheme provided)")
    
    @staticmethod
    def clear_stylesheet(widget: QWidget) -> None:
        """
        Clear widget's stylesheet.
        
        This removes all custom styling applied to the widget.
        
        Args:
            widget: Widget to clear stylesheet from
        
        Example:
            WidgetStylingService.clear_stylesheet(widget)
        """
        widget.setStyleSheet("")
        logger.debug(f"Cleared stylesheet from {type(widget).__name__}")
    
    @staticmethod
    def apply_error_styling(widget: QWidget, color_scheme) -> None:
        """
        Apply error styling to a widget.
        
        This highlights the widget to indicate an error or invalid state.
        
        Args:
            widget: Widget to apply error styling to
            color_scheme: Color scheme for styling (must have error color attribute)
        
        Example:
            WidgetStylingService.apply_error_styling(widget, color_scheme)
        """
        if hasattr(color_scheme, 'error'):
            error_color = color_scheme.to_hex(color_scheme.error)
            widget.setStyleSheet(f"border: 2px solid {error_color};")
            logger.debug(f"Applied error styling to {type(widget).__name__}")
        else:
            logger.warning("Color scheme has no 'error' attribute, cannot apply error styling")
    
    @staticmethod
    def remove_error_styling(widget: QWidget) -> None:
        """
        Remove error styling from a widget.
        
        This clears the error highlight.
        
        Args:
            widget: Widget to remove error styling from
        
        Example:
            WidgetStylingService.remove_error_styling(widget)
        """
        WidgetStylingService.clear_stylesheet(widget)
        logger.debug(f"Removed error styling from {type(widget).__name__}")

