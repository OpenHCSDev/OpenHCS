"""Pluggable color generation strategies for scope-based styling.

Follows Strategy Pattern to allow different color generation algorithms:
- MD5HashStrategy: Deterministic color from scope_id hash (default)
- ManualColorStrategy: User-selected colors with fallback to generated
- Future: SequentialStrategy, ThemeAwareStrategy, etc.
"""

from abc import ABC, abstractmethod
from typing import Tuple, Dict, Optional
from enum import Enum, auto
import hashlib
import colorsys
import logging

logger = logging.getLogger(__name__)


class ColorStrategyType(Enum):
    """Available color generation strategies."""
    MD5_HASH = auto()      # Deterministic from scope_id hash
    MANUAL = auto()        # User-selected color with fallback


class ScopeColorStrategy(ABC):
    """Abstract base for color generation strategies."""

    # Subclasses must set this class attribute
    strategy_type: ColorStrategyType

    @abstractmethod
    def generate_color(self, scope_id: str) -> Tuple[int, int, int]:
        """Generate RGB color for scope. Returns (r, g, b) in 0-255 range."""
        ...


class MD5HashStrategy(ScopeColorStrategy):
    """Deterministic color from MD5 hash of scope_id. Default strategy.
    
    Uses distinctipy for perceptually distinct colors when available,
    falls back to HSV-based generation otherwise.
    """
    
    strategy_type = ColorStrategyType.MD5_HASH
    PALETTE_SIZE = 50
    
    def __init__(self):
        self._palette: Optional[list] = None
    
    def _get_palette(self) -> list:
        """Get or generate distinct color palette."""
        if self._palette is None:
            self._palette = self._generate_palette()
        return self._palette
    
    def _generate_palette(self) -> list:
        """Generate perceptually distinct colors."""
        try:
            from distinctipy import distinctipy
            colors = distinctipy.get_colors(
                self.PALETTE_SIZE,
                exclude_colors=[(0, 0, 0), (1, 1, 1)],
                pastel_factor=0.5
            )
            # Convert from 0-1 to 0-255 range
            return [tuple(int(c * 255) for c in color) for color in colors]
        except ImportError:
            logger.debug("distinctipy not installed, using HSV fallback")
            return self._generate_hsv_palette()
    
    def _generate_hsv_palette(self) -> list:
        """Fallback HSV-based palette generation."""
        palette = []
        for i in range(self.PALETTE_SIZE):
            hue = 360 * i / self.PALETTE_SIZE
            r, g, b = colorsys.hsv_to_rgb(hue / 360, 0.5, 0.8)
            palette.append((int(r * 255), int(g * 255), int(b * 255)))
        return palette
    
    def _hash_to_index(self, scope_id: str) -> int:
        """Generate deterministic palette index from scope_id."""
        hash_bytes = hashlib.md5(scope_id.encode('utf-8')).digest()
        hash_int = int.from_bytes(hash_bytes[:4], byteorder='big')
        return hash_int % self.PALETTE_SIZE
    
    def generate_color(self, scope_id: str) -> Tuple[int, int, int]:
        """Generate color from MD5 hash of scope_id."""
        palette = self._get_palette()
        index = self._hash_to_index(scope_id)
        return palette[index]


class ManualColorStrategy(ScopeColorStrategy):
    """User-selected colors with persistence.
    
    Falls back to MD5HashStrategy for scopes without manual colors.
    """
    
    strategy_type = ColorStrategyType.MANUAL
    
    def __init__(self):
        self._colors: Dict[str, Tuple[int, int, int]] = {}
        self._fallback = MD5HashStrategy()
    
    def set_color(self, scope_id: str, rgb: Tuple[int, int, int]) -> None:
        """Set manual color for scope."""
        self._colors[scope_id] = rgb
    
    def clear_color(self, scope_id: str) -> None:
        """Clear manual color, revert to fallback."""
        self._colors.pop(scope_id, None)
    
    def has_manual_color(self, scope_id: str) -> bool:
        """Check if scope has manual color override."""
        return scope_id in self._colors
    
    def get_all_manual_colors(self) -> Dict[str, Tuple[int, int, int]]:
        """Get all manual color assignments (for persistence)."""
        return dict(self._colors)
    
    def load_manual_colors(self, colors: Dict[str, Tuple[int, int, int]]) -> None:
        """Load manual colors from persistence."""
        self._colors.update(colors)
    
    def generate_color(self, scope_id: str) -> Tuple[int, int, int]:
        """Get manual color or fall back to generated."""
        return self._colors.get(scope_id) or self._fallback.generate_color(scope_id)

