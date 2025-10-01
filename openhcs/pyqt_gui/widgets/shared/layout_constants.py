"""
Layout constants for PyQt parameter forms.

This module centralizes all spacing, margin, layout configuration,
and widget styling to ensure uniform appearance across all parameter forms.
"""

from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class ParameterFormLayoutConfig:
    """Configuration for parameter form layout spacing, margins, and widget styling."""

    # Main form layout settings
    main_layout_spacing: int = 2
    main_layout_margins: tuple = (4, 4, 4, 4)  # left, top, right, bottom

    # Content layout settings (between parameter fields)
    content_layout_spacing: int = 1
    content_layout_margins: tuple = (2, 2, 2, 2)

    # Parameter row layout settings (between label, widget, button)
    parameter_row_spacing: int = 4
    parameter_row_margins: tuple = (0, 0, 0, 0)

    # Optional parameter layout settings (checkbox + nested content)
    optional_layout_spacing: int = 2
    optional_layout_margins: tuple = (0, 0, 0, 0)

    # Widget sizing
    reset_button_width: int = 60
    input_field_height: int = 28  # Standard height for all input fields

    def get_widget_stylesheet(self, color_scheme) -> str:
        """
        Generate uniform widget stylesheet for all parameter forms.

        This ensures config window, step editor, and function pattern editor
        all have identical widget rendering.
        """
        return f"""
            QLineEdit, QSpinBox, QDoubleSpinBox, QComboBox {{
                background-color: {color_scheme.to_hex(color_scheme.input_bg)};
                color: {color_scheme.to_hex(color_scheme.input_text)};
                border: none;
                border-radius: 3px;
                padding: 5px;
                min-height: {self.input_field_height}px;
                max-height: {self.input_field_height}px;
            }}
            QLineEdit:focus, QSpinBox:focus, QDoubleSpinBox:focus, QComboBox:focus {{
                background-color: {color_scheme.to_hex(color_scheme.input_bg)};
                border: 1px solid {color_scheme.to_hex(color_scheme.selection_bg)};
            }}
            QPushButton {{
                background-color: {color_scheme.to_hex(color_scheme.button_bg)};
                color: {color_scheme.to_hex(color_scheme.button_text)};
                border: none;
                border-radius: 3px;
                padding: 5px 10px;
                min-height: {self.input_field_height}px;
                max-height: {self.input_field_height}px;
            }}
            QPushButton:hover {{
                background-color: {color_scheme.to_hex(color_scheme.button_hover_bg)};
            }}
            QPushButton:pressed {{
                background-color: {color_scheme.to_hex(color_scheme.button_pressed_bg)};
            }}
        """


# Default compact configuration
COMPACT_LAYOUT = ParameterFormLayoutConfig()

# Alternative configurations for different use cases
SPACIOUS_LAYOUT = ParameterFormLayoutConfig(
    main_layout_spacing=6,
    main_layout_margins=(8, 8, 8, 8),
    content_layout_spacing=4,
    content_layout_margins=(4, 4, 4, 4),
    parameter_row_spacing=8,
    optional_layout_spacing=4,
    reset_button_width=80
)

ULTRA_COMPACT_LAYOUT = ParameterFormLayoutConfig(
    main_layout_spacing=1,
    main_layout_margins=(2, 2, 2, 2),
    content_layout_spacing=0,
    content_layout_margins=(1, 1, 1, 1),
    parameter_row_spacing=2,
    parameter_row_margins=(0, 0, 0, 0),
    optional_layout_spacing=1,
    optional_layout_margins=(0, 0, 0, 0),
    reset_button_width=50
)

# Current active configuration - change this to switch layouts globally
CURRENT_LAYOUT = COMPACT_LAYOUT
