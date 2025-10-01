"""
Layout constants for PyQt parameter forms.

This module centralizes all spacing, margin, and layout configuration
to ensure uniform appearance across all parameter forms.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class ParameterFormLayoutConfig:
    """Configuration for parameter form layout spacing and margins."""

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

    # Reset button width
    reset_button_width: int = 60


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
