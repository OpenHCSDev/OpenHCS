"""Configuration and data structures for scope-based coloring."""

from dataclasses import dataclass
from enum import Enum
from typing import Optional


@dataclass
class ScopeVisualConfig:
    """Static configuration values for scope-based visuals."""

    ORCHESTRATOR_ITEM_BG_SATURATION: int = 50
    ORCHESTRATOR_ITEM_BG_VALUE: int = 85
    ORCHESTRATOR_ITEM_BORDER_SATURATION: int = 60
    ORCHESTRATOR_ITEM_BORDER_VALUE: int = 80
    ORCHESTRATOR_ITEM_BG_OPACITY: float = 0.10 # 0.0-1.0

    STEP_ITEM_BG_SATURATION: int = 50
    STEP_ITEM_BG_VALUE: int = 85
    STEP_ITEM_BG_OPACITY: float = 0.100  # 0.0-1.0

    # Groupbox and tree background tint (subtle scope coloring)
    GROUPBOX_BG_OPACITY: float = 0.05  # 0.0-1.0
    TREE_BG_OPACITY: float = 0.05  # 0.0-1.0

    STEP_WINDOW_BORDER_SATURATION: int = 60
    STEP_WINDOW_BORDER_VALUE: int = 80
    STEP_WINDOW_BORDER_WIDTH_PX: int = 4
    STEP_WINDOW_BORDER_STYLE: str = "solid"

    FLASH_DURATION_MS: int = 300
    FLASH_COLOR_RGB: tuple[int, int, int] = (144, 238, 144)
    LIST_ITEM_FLASH_ENABLED: bool = True
    WIDGET_FLASH_ENABLED: bool = True


@dataclass
class ScopeColorScheme:
    """Color scheme for a specific scope."""

    scope_id: Optional[str]
    hue: int

    orchestrator_item_bg_rgb: tuple[int, int, int]
    orchestrator_item_border_rgb: tuple[int, int, int]

    step_window_border_rgb: tuple[int, int, int]
    step_item_bg_rgb: Optional[tuple[int, int, int]]
    step_border_width: int = 0
    step_border_layers: list = None
    base_color_rgb: tuple[int, int, int] = (128, 128, 128)

    def __post_init__(self) -> None:
        if self.step_border_layers is None:
            self.step_border_layers = []

    def to_qcolor_orchestrator_bg(self):
        """QColor for orchestrator item background with alpha."""
        from PyQt6.QtGui import QColor

        config = get_scope_visual_config()
        r, g, b = self.orchestrator_item_bg_rgb
        return QColor(r, g, b, int(255 * config.ORCHESTRATOR_ITEM_BG_OPACITY))

    def to_qcolor_orchestrator_border(self):
        """QColor for orchestrator item border."""
        from PyQt6.QtGui import QColor

        return QColor(*self.orchestrator_item_border_rgb)

    def to_qcolor_step_window_border(self):
        """QColor for step window border."""
        from PyQt6.QtGui import QColor

        return QColor(*self.step_window_border_rgb)

    def to_qcolor_step_item_bg(self):
        """QColor for step list background (alpha) or None."""
        if self.step_item_bg_rgb is None:
            return None
        from PyQt6.QtGui import QColor

        config = get_scope_visual_config()
        r, g, b = self.step_item_bg_rgb
        return QColor(r, g, b, int(255 * config.STEP_ITEM_BG_OPACITY))

    def to_stylesheet_step_window_border(self) -> str:
        """Reserve border space via stylesheet for step windows."""
        if not self.step_border_layers:
            r, g, b = self.step_window_border_rgb
            return f"border: 4px solid rgb({r}, {g}, {b});"
        total_width = sum(layer[0] for layer in self.step_border_layers)
        return f"border: {total_width}px solid transparent;"


class ListItemType(Enum):
    """Type of list item for scope-based coloring."""

    ORCHESTRATOR = "to_qcolor_orchestrator_bg"
    STEP = "to_qcolor_step_item_bg"

    def get_background_color(self, color_scheme: ScopeColorScheme):
        method = getattr(color_scheme, self.value)
        return method()


_config_instance: Optional[ScopeVisualConfig] = None


def get_scope_visual_config() -> ScopeVisualConfig:
    """Singleton access for ScopeVisualConfig."""
    global _config_instance
    if _config_instance is None:
        _config_instance = ScopeVisualConfig()
    return _config_instance
