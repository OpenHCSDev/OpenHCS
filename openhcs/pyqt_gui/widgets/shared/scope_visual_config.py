"""Configuration for scope-based visual feedback (colors, flash animations)."""

from dataclasses import dataclass
from enum import Enum
from typing import Optional


@dataclass
class ScopeVisualConfig:
    """Configuration for scope-based visual feedback.
    
    Controls colors, flash animations, and styling for scope-aware UI elements.
    All values are configurable for easy tuning.
    """
    
    # === Orchestrator List Item Colors (HSV) ===
    ORCHESTRATOR_ITEM_BG_SATURATION: int = 40  # Visible but not overwhelming
    ORCHESTRATOR_ITEM_BG_VALUE: int = 85       # Medium-light background
    ORCHESTRATOR_ITEM_BORDER_SATURATION: int = 30
    ORCHESTRATOR_ITEM_BORDER_VALUE: int = 80

    # === Step List Item Colors (HSV) ===
    STEP_ITEM_BG_SATURATION: int = 35          # Slightly less saturated than orchestrator
    STEP_ITEM_BG_VALUE: int = 88               # Slightly lighter than orchestrator
    
    # === Step Window Border Colors (HSV) ===
    STEP_WINDOW_BORDER_SATURATION: int = 60    # More saturated for visibility
    STEP_WINDOW_BORDER_VALUE: int = 70         # Medium brightness
    STEP_WINDOW_BORDER_WIDTH_PX: int = 4       # Thicker for visibility
    STEP_WINDOW_BORDER_STYLE: str = "solid"
    
    # === Flash Animation ===
    FLASH_DURATION_MS: int = 300               # Duration of flash effect
    FLASH_COLOR_RGB: tuple[int, int, int] = (144, 238, 144)  # Light green
    LIST_ITEM_FLASH_ENABLED: bool = True
    WIDGET_FLASH_ENABLED: bool = True


@dataclass
class ScopeColorScheme:
    """Color scheme for a specific scope."""
    scope_id: Optional[str]
    hue: int

    # Orchestrator colors
    orchestrator_item_bg_rgb: tuple[int, int, int]
    orchestrator_item_border_rgb: tuple[int, int, int]

    # Step colors
    step_window_border_rgb: tuple[int, int, int]
    step_item_bg_rgb: Optional[tuple[int, int, int]]  # None = transparent background
    step_border_width: int = 0  # Total border width (for backward compat)
    step_border_layers: list = None  # List of (width, tint_index) for layered borders
    base_color_rgb: tuple[int, int, int] = (128, 128, 128)  # Base orchestrator color for tint calculation

    def __post_init__(self):
        """Initialize mutable defaults."""
        if self.step_border_layers is None:
            self.step_border_layers = []
    
    def to_qcolor_orchestrator_bg(self) -> 'QColor':
        """Get QColor for orchestrator list item background with alpha transparency."""
        from PyQt6.QtGui import QColor
        r, g, b = self.orchestrator_item_bg_rgb
        # 40% opacity for visible background tint
        return QColor(r, g, b, int(255 * 0.40))
    
    def to_qcolor_orchestrator_border(self) -> 'QColor':
        """Get QColor for orchestrator list item border."""
        from PyQt6.QtGui import QColor
        return QColor(*self.orchestrator_item_border_rgb)
    
    def to_qcolor_step_window_border(self) -> 'QColor':
        """Get QColor for step window border."""
        from PyQt6.QtGui import QColor
        return QColor(*self.step_window_border_rgb)
    
    def to_qcolor_step_item_bg(self) -> Optional['QColor']:
        """Get QColor for step list item background with alpha transparency.

        Returns None for transparent background (no background color).
        """
        if self.step_item_bg_rgb is None:
            return None
        from PyQt6.QtGui import QColor
        r, g, b = self.step_item_bg_rgb
        # 30% opacity for visible background tint
        return QColor(r, g, b, int(255 * 0.30))
    
    def to_stylesheet_step_window_border(self) -> str:
        """Generate stylesheet for step window border with layered borders.

        Uses custom border painting via paintEvent override since Qt stylesheets
        don't properly support multiple layered borders with patterns on QDialog.

        This method returns a simple placeholder border - actual layered rendering
        happens in the window's paintEvent.
        """
        if not self.step_border_layers or len(self.step_border_layers) == 0:
            # No borders - use simple window border with step color
            r, g, b = self.step_window_border_rgb
            return f"border: 4px solid rgb({r}, {g}, {b});"

        # Calculate total border width for spacing purposes
        total_width = sum(layer[0] for layer in self.step_border_layers)

        # Return empty border - actual painting happens in paintEvent
        # We still need to reserve space for the border
        return f"border: {total_width}px solid transparent;"


class ListItemType(Enum):
    """Type of list item for scope-based coloring.
    
    Uses enum-driven polymorphic dispatch to select correct background color
    from ScopeColorScheme without if/else conditionals.
    
    Pattern follows OpenHCS ProcessingContract enum design:
    - Enum value stores method name
    - Enum method uses getattr() for polymorphic dispatch
    - Extensible: add new item types without modifying existing code
    """
    ORCHESTRATOR = "to_qcolor_orchestrator_bg"
    STEP = "to_qcolor_step_item_bg"
    
    def get_background_color(self, color_scheme: ScopeColorScheme) -> 'QColor':
        """Get background color for this item type via polymorphic dispatch.
        
        Args:
            color_scheme: ScopeColorScheme containing all color variants
            
        Returns:
            QColor for this item type's background
        """
        method = getattr(color_scheme, self.value)
        return method()


def get_scope_visual_config() -> ScopeVisualConfig:
    """Get singleton instance of ScopeVisualConfig."""
    global _config_instance
    if _config_instance is None:
        _config_instance = ScopeVisualConfig()
    return _config_instance


_config_instance: Optional[ScopeVisualConfig] = None

