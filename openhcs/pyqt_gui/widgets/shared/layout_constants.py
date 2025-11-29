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
    main_layout_spacing: int = 4
    main_layout_margins: tuple = (main_layout_spacing, main_layout_spacing, main_layout_spacing, main_layout_spacing)

    # Content layout settings (between parameter fields)
    # THIS IS THE KEY ONE - controls vertical spacing between each parameter row
    content_layout_spacing: int = 1
    content_layout_margins: tuple = (content_layout_spacing, content_layout_spacing, content_layout_spacing, content_layout_spacing)

    # Parameter row layout settings (between label, widget, button)
    parameter_row_spacing: int = 2
    parameter_row_margins: tuple = (1, 1, 1, 1)

    # Optional parameter layout settings (checkbox + nested content)
    optional_layout_spacing: int = 2
    optional_layout_margins: tuple = (2, 2, 1, 1)

    # GroupBox/Section settings (Dtype Config, Processing Config, etc.)
    groupbox_spacing: int = 2           # ⭐ Spacing inside groupbox sections
    groupbox_margins: tuple = (5, 5, 5, 5)  # ⭐ Margins inside groupbox (left, top, right, bottom)
    groupbox_margin_top: int = 5        # ⭐ QSS margin-top for QGroupBox
    groupbox_padding_top: int = 5       # ⭐ QSS padding-top for QGroupBox

    # Widget-level settings
    widget_fixed_height: int | None = None  # None = auto, or set to fixed pixel height
    widget_padding: int = 5  # ⭐ WIDGET INTERNAL PADDING - controls height of input fields!
    row_fixed_height: int | None = None  # ⭐ Fixed height for each parameter row (None = auto)

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
    # Slightly tighter than COMPACT_LAYOUT but not "zero everything".
    # This is tuned to feel close to the main-branch compact layout while
    # still being clearly more dense.
    main_layout_spacing=1,              # Small spacing around entire form
    main_layout_margins=(2, 2, 2, 2),   # Small outer margins

    # Vertical spacing between parameter rows: let row margins do most of
    # the work so we have a tiny but visible gap.
    content_layout_spacing=0,
    content_layout_margins=(1, 1, 1, 1),

    # Within a row, keep labels/fields/buttons comfortably separated, and
    # use small margins to avoid rows visually fusing together.
    parameter_row_spacing=2,
    parameter_row_margins=(1, 1, 1, 1),

    optional_layout_spacing=1,
    optional_layout_margins=(1, 1, 1, 1),

    # Group boxes should still read as distinct sections but with reduced
    # padding compared to the default compact layout.
    groupbox_spacing=1,
    groupbox_margins=(3, 3, 3, 3),
    groupbox_margin_top=3,
    groupbox_padding_top=3,

    # Make widgets shorter than COMPACT (padding=5) but not razor-thin.
    widget_fixed_height=None,
    widget_padding=3,
    reset_button_width=50
)

# Current active configuration - change this to switch layouts globally
CURRENT_LAYOUT = COMPACT_LAYOUT
