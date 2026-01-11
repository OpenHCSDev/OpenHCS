"""
Animation and visual effects system.

Game-engine inspired flash animation system with O(1) per-window
performance for visual feedback on value changes.
"""

from .flash_config import FlashConfig, get_flash_config
from .flash_mixin import (
    FlashMixin,
    WindowFlashOverlay,
    OverlayGeometryCache,
    get_flash_color,
    get_flash_color_from_palette,
    FlashElement,
    get_widget_corner_radius,
    DEFAULT_CORNER_RADIUS,
)

# Optional OpenGL support
try:
    from .flash_overlay_opengl import FlashOverlayOpenGL
except ImportError:
    FlashOverlayOpenGL = None

__all__ = [
    "FlashConfig",
    "get_flash_config",
    "FlashMixin",
    "WindowFlashOverlay",
    "OverlayGeometryCache",
    "get_flash_color",
    "get_flash_color_from_palette",
    "FlashElement",
    "FlashOverlayOpenGL",
    "get_widget_corner_radius",
    "DEFAULT_CORNER_RADIUS",
]
