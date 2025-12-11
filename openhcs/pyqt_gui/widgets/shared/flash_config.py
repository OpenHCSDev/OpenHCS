"""Declarative configuration for flash animations."""

from dataclasses import dataclass
from typing import Optional, Tuple


@dataclass
class FlashConfig:
    """Flash animation tuning knobs."""

    base_color_rgb: Tuple[int, int, int] = (100, 100, 100)  # Medium grey for no-scope flashes
    flash_alpha: int = 255
    fade_in_s: float = 0.05
    hold_s: float = 0.025
    fade_out_s: float = 0.300
    frame_ms: int = 33  # 20fps - sufficient for highlight animations


_config: Optional[FlashConfig] = None


def get_flash_config() -> FlashConfig:
    """Return singleton flash config."""
    global _config
    if _config is None:
        _config = FlashConfig()
    return _config
