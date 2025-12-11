"""Utilities for generating scope-based colors using distinct palettes."""

import colorsys
import hashlib
import logging
from typing import Optional, Tuple

from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ScopeColorScheme

logger = logging.getLogger(__name__)


def _ensure_wcag_compliant(
    color_rgb: tuple[int, int, int],
    background: tuple[int, int, int] = (255, 255, 255),
    min_ratio: float = 4.5,
) -> tuple[int, int, int]:
    """Adjust color to meet WCAG AA contrast against background."""
    try:
        from wcag_contrast_ratio.contrast import rgb as wcag_rgb

        color_01 = tuple(c / 255.0 for c in color_rgb)
        bg_01 = tuple(c / 255.0 for c in background)
        current_ratio = wcag_rgb(color_01, bg_01)
        if current_ratio >= min_ratio:
            return color_rgb

        h, s, v = colorsys.rgb_to_hsv(*color_01)
        while v > 0.1:
            v *= 0.9
            adjusted_rgb_01 = colorsys.hsv_to_rgb(h, s, v)
            ratio = wcag_rgb(adjusted_rgb_01, bg_01)
            if ratio >= min_ratio:
                return tuple(int(c * 255) for c in adjusted_rgb_01)
        logger.warning("Could not meet WCAG contrast ratio %s for color %s", min_ratio, color_rgb)
        return tuple(int(c * 255) for c in colorsys.hsv_to_rgb(h, s, 0.1))
    except ImportError:
        logger.warning("wcag-contrast-ratio not installed, skipping WCAG compliance check")
        return color_rgb
    except Exception as exc:
        logger.warning("WCAG compliance check failed: %s", exc)
        return color_rgb


def extract_orchestrator_scope(scope_id: Optional[str]) -> Optional[str]:
    """Extract orchestrator portion from scope_id."""
    if scope_id is None:
        return None
    if "::" in scope_id:
        return scope_id.split("::", 1)[0]
    return scope_id


def extract_step_index(scope_id: str) -> int:
    """Extract per-orchestrator step index from scope_id."""
    if "::" not in scope_id:
        return 0
    step_part = scope_id.split("::")[1]
    if "@" in step_part:
        try:
            position_str = step_part.split("@")[1]
            return int(position_str)
        except (IndexError, ValueError):
            pass
    hash_bytes = hashlib.md5(step_part.encode()).digest()
    return int.from_bytes(hash_bytes[:2], byteorder="big") % 27


def hsv_to_rgb(hue: int, saturation: int, value: int) -> tuple[int, int, int]:
    """Convert HSV color to RGB tuple."""
    h = hue / 360.0
    s = saturation / 100.0
    v = value / 100.0
    r, g, b = colorsys.hsv_to_rgb(h, s, v)
    return (int(r * 255), int(g * 255), int(b * 255))


def get_scope_color_scheme(scope_id: Optional[str]) -> ScopeColorScheme:
    """Get color scheme for scope via service."""
    from openhcs.pyqt_gui.widgets.shared.services.scope_color_service import ScopeColorService

    return ScopeColorService.instance().get_color_scheme(scope_id)


def _build_color_scheme_from_rgb(base_rgb: Tuple[int, int, int], scope_id: str) -> ScopeColorScheme:
    """Build color scheme for a given base RGB and scope_id."""
    orchestrator_scope = extract_orchestrator_scope(scope_id)

    orch_bg_rgb = base_rgb
    orch_border_rgb = tuple(int(c * 200 / 255) for c in base_rgb)

    step_index = extract_step_index(scope_id) if "::" in (scope_id or "") else 0
    step_item_rgb = orch_bg_rgb

    num_border_layers = (step_index // 9) + 1
    combo_index = step_index % 9
    step_pattern_index = combo_index // 3
    step_tint = combo_index % 3

    border_patterns = ["solid", "dashed", "dotted"]
    step_border_layers = []
    for layer in range(num_border_layers):
        if layer == 0:
            border_tint = step_tint
            border_pattern = border_patterns[step_pattern_index]
        else:
            layer_combo = (combo_index + layer * 3) % 9
            border_tint = (layer_combo // 3) % 3
            border_pattern = border_patterns[layer_combo % 3]
        step_border_layers.append((3, border_tint, border_pattern))

    step_border_width = num_border_layers * 3

    tint_index = step_index % 3
    tint_factors = [0.7, 1.0, 1.4]
    tint_factor = tint_factors[tint_index]
    step_window_rgb = tuple(min(255, int(c * tint_factor)) for c in base_rgb)

    orch_border_rgb = _ensure_wcag_compliant(orch_border_rgb, background=(255, 255, 255))
    step_window_rgb = _ensure_wcag_compliant(step_window_rgb, background=(255, 255, 255))

    return ScopeColorScheme(
        scope_id=orchestrator_scope,
        hue=0,
        orchestrator_item_bg_rgb=orch_bg_rgb,
        orchestrator_item_border_rgb=orch_border_rgb,
        step_window_border_rgb=step_window_rgb,
        step_item_bg_rgb=step_item_rgb,
        step_border_width=step_border_width,
        step_border_layers=step_border_layers,
        base_color_rgb=orch_bg_rgb,
    )
