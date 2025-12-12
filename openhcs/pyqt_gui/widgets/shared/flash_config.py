"""Declarative configuration for flash animations."""

from dataclasses import dataclass
from typing import Optional, Tuple
import logging

logger = logging.getLogger(__name__)


def detect_screen_refresh_rate() -> int:
    """Detect primary screen refresh rate.

    Returns:
        Detected refresh rate (Hz), or 60 if detection fails.
    """
    try:
        from PyQt6.QtGui import QGuiApplication

        # Get primary screen (QGuiApplication has primaryScreen() method)
        app = QGuiApplication.instance()
        if app is None:
            logger.warning("[FlashConfig] No QApplication instance, defaulting to 60Hz")
            return 60

        screen = app.primaryScreen()
        if screen is None:
            logger.warning("[FlashConfig] No primary screen found, defaulting to 60Hz")
            return 60

        refresh_rate = screen.refreshRate()

        # Sanity check: typical refresh rates are 60, 75, 120, 144, 165, 240
        if refresh_rate < 30 or refresh_rate > 500:
            logger.warning(f"[FlashConfig] Unusual refresh rate detected: {refresh_rate}Hz, defaulting to 60Hz")
            return 60

        logger.info(f"[FlashConfig] Detected screen refresh rate: {refresh_rate}Hz")
        return int(refresh_rate)
    except Exception as e:
        logger.warning(f"[FlashConfig] Failed to detect refresh rate: {e}, defaulting to 60Hz")
        return 60


@dataclass
class FlashConfig:
    """Flash animation tuning knobs with automatic screen refresh rate detection."""

    base_color_rgb: Tuple[int, int, int] = (255, 255, 255)  # Medium grey for no-scope flashes
    flash_alpha: int = 255
    fade_in_s: float = 0.200
    hold_s: float = 0.050
    fade_out_s: float = 0.600

    # Frame rate configuration
    frame_ms: Optional[int] = None  # Auto-calculated from target_fps if not specified

    # OpenGL acceleration (EXPERIMENTAL - actually slower than QPainter in practice)
    # The overhead of GL context switching and buffer uploads exceeds the benefit
    # of instanced rendering for our typical workload (few rectangles, simple shapes).
    # Keep False unless explicitly testing GL performance.
    use_opengl: bool = False

    # High refresh rate support
    # Options: None (auto-detect), 30, 60, 144, 240, or any custom value
    # None = automatically matches screen refresh rate (recommended)
    target_fps: Optional[int] = None  # None = auto-detect screen refresh rate

    # Advanced: Cap refresh rate even if screen supports higher
    max_fps: Optional[int] = 60# None = no cap, or set to limit (e.g., 60 for power saving)

    def __post_init__(self):
        """Calculate frame_ms from target_fps or auto-detect screen refresh rate."""
        # If frame_ms explicitly set, use it
        if self.frame_ms is not None:
            return

        # Determine target FPS
        fps = self.target_fps
        if fps is None:
            # Auto-detect screen refresh rate
            fps = detect_screen_refresh_rate()
            logger.info(f"[FlashConfig] Auto-detected target FPS: {fps}")

        # Apply max_fps cap if specified
        if self.max_fps is not None and fps > self.max_fps:
            logger.info(f"[FlashConfig] Capping FPS from {fps} to {self.max_fps} (max_fps limit)")
            fps = self.max_fps

        # Calculate frame interval
        self.frame_ms = int(1000 / fps)
        logger.info(f"[FlashConfig] Using {fps}Hz ({self.frame_ms}ms frame interval) for flash animations")


_config: Optional[FlashConfig] = None


def get_flash_config() -> FlashConfig:
    """Return singleton flash config."""
    global _config
    if _config is None:
        _config = FlashConfig()
    return _config
