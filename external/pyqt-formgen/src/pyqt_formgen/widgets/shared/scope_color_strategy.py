"""Pluggable color generation strategies for scope-based styling.

HIERARCHY:
- Orchestrator (plate) → gets BASE color from palette (by hash)
- Steps under that orchestrator → inherit BASE color, vary by tint + pattern
"""

from abc import ABC, abstractmethod
from enum import Enum, auto
from typing import Tuple, Dict, Optional
import colorsys
import hashlib
import logging

logger = logging.getLogger(__name__)

# Predetermined palette of maximally distinct colors (12 primary colors)
# Hand-picked for maximum perceptual distinction
_PRIMARY_PALETTE_RGB: Tuple[Tuple[int, int, int], ...] = (
    (46, 204, 113),   # 0: Emerald green
    (52, 152, 219),   # 1: Sky blue
    (231, 76, 60),    # 2: Red
    (155, 89, 182),   # 3: Purple
    (241, 196, 15),   # 4: Yellow
    (26, 188, 156),   # 5: Turquoise
    (230, 126, 34),   # 6: Orange
    (52, 73, 94),     # 7: Dark blue-grey
    (46, 204, 170),   # 8: Mint
    (192, 57, 43),    # 9: Dark red
    (142, 68, 173),   # 10: Dark purple
    (39, 174, 96),    # 11: Dark green
)


class ColorStrategyType(Enum):
    """Available color generation strategies."""

    INDEX_BASED = auto()  # Color by orchestrator hash (primary)
    MD5_HASH = auto()     # Fallback (distinctipy palette)
    MANUAL = auto()


class ScopeColorStrategy(ABC):
    """Abstract base for color generation strategies."""

    strategy_type: ColorStrategyType

    @abstractmethod
    def generate_color(self, scope_id: str, step_index: Optional[int] = None) -> Tuple[int, int, int]:
        """Generate RGB color for scope.

        Args:
            scope_id: The scope identifier (orchestrator or step scope)
            step_index: Optional step index (not used for base color, only for tint/pattern)
        """
        raise NotImplementedError


class IndexBasedStrategy(ScopeColorStrategy):
    """Color by orchestrator from predetermined palette in discovery order.

    Orchestrators (plates) get distinct BASE colors from the primary palette
    assigned in the order they are first seen. Steps inherit their orchestrator's
    base color. Tint/pattern variation is handled in _build_color_scheme_from_rgb.
    """

    strategy_type = ColorStrategyType.INDEX_BASED

    def __init__(self) -> None:
        # Map orchestrator -> palette index assigned in discovery order
        self._color_map: Dict[str, int] = {}
        self._next_index: int = 0

    def generate_color(self, scope_id: str, step_index: Optional[int] = None) -> Tuple[int, int, int]:
        orchestrator = self._extract_orchestrator(scope_id)

        if orchestrator not in self._color_map:
            palette_index = self._next_index % len(_PRIMARY_PALETTE_RGB)
            self._color_map[orchestrator] = palette_index
            self._next_index += 1
        else:
            palette_index = self._color_map[orchestrator]

        return _PRIMARY_PALETTE_RGB[palette_index]

    @staticmethod
    def _extract_orchestrator(scope_id: str) -> str:
        """Extract orchestrator part (before ::) or return the whole scope_id."""
        if "::" in scope_id:
            return scope_id.split("::", 1)[0]
        return scope_id


class MD5HashStrategy(ScopeColorStrategy):
    """Deterministic color from MD5 hash of scope_id (fallback)."""

    strategy_type = ColorStrategyType.MD5_HASH
    PALETTE_SIZE = 50

    def __init__(self) -> None:
        self._palette: Optional[list] = None

    def _get_palette(self) -> list:
        if self._palette is None:
            self._palette = self._generate_palette()
        return self._palette

    def _generate_palette(self) -> list:
        try:
            from distinctipy import distinctipy

            colors = distinctipy.get_colors(
                self.PALETTE_SIZE,
                exclude_colors=[(0, 0, 0), (1, 1, 1)],
                pastel_factor=0.5,
            )
            return [tuple(int(c * 255) for c in color) for color in colors]
        except ImportError:
            logger.debug("distinctipy not installed, using HSV fallback")
            return self._generate_hsv_palette()

    def _generate_hsv_palette(self) -> list:
        palette = []
        for i in range(self.PALETTE_SIZE):
            hue = 360 * i / self.PALETTE_SIZE
            r, g, b = colorsys.hsv_to_rgb(hue / 360, 0.5, 0.8)
            palette.append((int(r * 255), int(g * 255), int(b * 255)))
        return palette

    def _hash_to_index(self, scope_id: str) -> int:
        hash_bytes = hashlib.md5(scope_id.encode("utf-8")).digest()
        hash_int = int.from_bytes(hash_bytes[:4], byteorder="big")
        return hash_int % self.PALETTE_SIZE

    def generate_color(self, scope_id: str, step_index: Optional[int] = None) -> Tuple[int, int, int]:
        palette = self._get_palette()
        index = self._hash_to_index(scope_id)
        return palette[index]


class ManualColorStrategy(ScopeColorStrategy):
    """User-selected colors with persistence."""

    strategy_type = ColorStrategyType.MANUAL

    def __init__(self) -> None:
        self._colors: Dict[str, Tuple[int, int, int]] = {}
        self._fallback = MD5HashStrategy()

    def set_color(self, scope_id: str, rgb: Tuple[int, int, int]) -> None:
        self._colors[scope_id] = rgb

    def clear_color(self, scope_id: str) -> None:
        self._colors.pop(scope_id, None)

    def has_manual_color(self, scope_id: str) -> bool:
        return scope_id in self._colors

    def get_all_manual_colors(self) -> Dict[str, Tuple[int, int, int]]:
        return dict(self._colors)

    def load_manual_colors(self, colors: Dict[str, Tuple[int, int, int]]) -> None:
        self._colors.update(colors)

    def generate_color(self, scope_id: str, step_index: Optional[int] = None) -> Tuple[int, int, int]:
        return self._colors.get(scope_id) or self._fallback.generate_color(scope_id, step_index)
