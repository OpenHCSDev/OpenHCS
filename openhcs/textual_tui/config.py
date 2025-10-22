"""
Configuration classes for OpenHCS Textual User Interface.

These classes are only used by the deprecated Textual TUI and are not part of the core config.
"""

from dataclasses import dataclass, field
from textual_window import TilingLayout


@dataclass(frozen=True)
class TilingKeybinding:
    """Declarative mapping between key combination and window manager method."""
    key: str
    action: str  # method name that already exists
    description: str


@dataclass(frozen=True)
class TilingKeybindings:
    """Declarative mapping of tiling keybindings to existing methods."""

    # Focus controls
    focus_next: TilingKeybinding = TilingKeybinding("ctrl+j", "focus_next_window", "Focus Next Window")
    focus_prev: TilingKeybinding = TilingKeybinding("ctrl+k", "focus_previous_window", "Focus Previous Window")

    # Layout controls - map to wrapper methods
    horizontal_split: TilingKeybinding = TilingKeybinding("ctrl+shift+h", "set_horizontal_split", "Horizontal Split")
    vertical_split: TilingKeybinding = TilingKeybinding("ctrl+shift+v", "set_vertical_split", "Vertical Split")
    grid_layout: TilingKeybinding = TilingKeybinding("ctrl+shift+g", "set_grid_layout", "Grid Layout")
    master_detail: TilingKeybinding = TilingKeybinding("ctrl+shift+m", "set_master_detail", "Master Detail")
    toggle_floating: TilingKeybinding = TilingKeybinding("ctrl+shift+f", "toggle_floating", "Toggle Floating")

    # Window movement - map to extracted window_manager methods
    move_window_prev: TilingKeybinding = TilingKeybinding("ctrl+shift+left", "move_focused_window_prev", "Move Window Left")
    move_window_next: TilingKeybinding = TilingKeybinding("ctrl+shift+right", "move_focused_window_next", "Move Window Right")
    rotate_left: TilingKeybinding = TilingKeybinding("ctrl+alt+left", "rotate_window_order_left", "Rotate Windows Left")
    rotate_right: TilingKeybinding = TilingKeybinding("ctrl+alt+right", "rotate_window_order_right", "Rotate Windows Right")

    # Gap controls
    gap_increase: TilingKeybinding = TilingKeybinding("ctrl+plus", "gap_increase", "Increase Gap")
    gap_decrease: TilingKeybinding = TilingKeybinding("ctrl+minus", "gap_decrease", "Decrease Gap")

    # Bulk operations
    minimize_all: TilingKeybinding = TilingKeybinding("ctrl+shift+d", "minimize_all_windows", "Minimize All")
    open_all: TilingKeybinding = TilingKeybinding("ctrl+shift+o", "open_all_windows", "Open All")


@dataclass(frozen=True)
class TUIConfig:
    """Configuration for OpenHCS Textual User Interface."""
    default_tiling_layout: TilingLayout = TilingLayout.MASTER_DETAIL
    """Default tiling layout for window manager on startup."""

    default_window_gap: int = 1
    """Default gap between windows in tiling mode (in characters)."""

    enable_startup_notification: bool = True
    """Whether to show notification about tiling mode on startup."""

    keybindings: TilingKeybindings = field(default_factory=TilingKeybindings)
    """Declarative mapping of all tiling keybindings."""

