"""Pluggable color generation strategies for scope-based styling."""

from abc import ABC, abstractmethod
from enum import Enum, auto
from typing import Tuple, Dict, Optional
import colorsys
import hashlib
import logging

logger = logging.getLogger(__name__)


class ColorStrategyType(Enum):
    """Available color generation strategies."""

    MD5_HASH = auto()
    MANUAL = auto()


class ScopeColorStrategy(ABC):
    """Abstract base for color generation strategies."""

    strategy_type: ColorStrategyType

    @abstractmethod
    def generate_color(self, scope_id: str) -> Tuple[int, int, int]:
        """Generate RGB color for scope."""
        raise NotImplementedError


class MD5HashStrategy(ScopeColorStrategy):
    """Deterministic color from MD5 hash of scope_id."""

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

    def generate_color(self, scope_id: str) -> Tuple[int, int, int]:
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

    def generate_color(self, scope_id: str) -> Tuple[int, int, int]:
        return self._colors.get(scope_id) or self._fallback.generate_color(scope_id)
