"""Utilities for generating scope-based colors using distinct palettes."""

import colorsys
import hashlib
import logging
from typing import Optional, Tuple

from PyQt6.QtGui import QColor

from pyqt_formgen.widgets.shared.scope_visual_config import ScopeColorScheme

logger = logging.getLogger(__name__)

# Perceptually distinct L* levels in CIELAB (0-100 scale)
# These are equidistant in perceptual space
BORDER_LAB_LIGHTNESS: Tuple[float, ...] = (30.0, 55.0, 80.0)


def _rgb_to_lab(r: float, g: float, b: float) -> Tuple[float, float, float]:
    """Convert sRGB (0-1) to CIELAB. D65 illuminant."""
    # sRGB to linear RGB
    def linearize(c):
        return c / 12.92 if c <= 0.04045 else ((c + 0.055) / 1.055) ** 2.4

    r_lin, g_lin, b_lin = linearize(r), linearize(g), linearize(b)

    # Linear RGB to XYZ (D65)
    x = r_lin * 0.4124564 + g_lin * 0.3575761 + b_lin * 0.1804375
    y = r_lin * 0.2126729 + g_lin * 0.7151522 + b_lin * 0.0721750
    z = r_lin * 0.0193339 + g_lin * 0.1191920 + b_lin * 0.9503041

    # XYZ to LAB (D65 reference white)
    xn, yn, zn = 0.95047, 1.0, 1.08883

    def f(t):
        return t ** (1/3) if t > 0.008856 else (7.787 * t) + (16/116)

    L = 116 * f(y / yn) - 16
    a = 500 * (f(x / xn) - f(y / yn))
    b_lab = 200 * (f(y / yn) - f(z / zn))
    return L, a, b_lab


def _lab_to_rgb(L: float, a: float, b_lab: float) -> Tuple[float, float, float]:
    """Convert CIELAB to sRGB (0-1). D65 illuminant."""
    # LAB to XYZ
    xn, yn, zn = 0.95047, 1.0, 1.08883

    def f_inv(t):
        return t ** 3 if t > 0.206893 else (t - 16/116) / 7.787

    fy = (L + 16) / 116
    fx = a / 500 + fy
    fz = fy - b_lab / 200

    x = xn * f_inv(fx)
    y = yn * f_inv(fy)
    z = zn * f_inv(fz)

    # XYZ to linear RGB
    r_lin = x * 3.2404542 - y * 1.5371385 - z * 0.4985314
    g_lin = -x * 0.9692660 + y * 1.8760108 + z * 0.0415560
    b_lin = x * 0.0556434 - y * 0.2040259 + z * 1.0572252

    # Linear RGB to sRGB
    def gamma(c):
        c = max(0, min(1, c))
        return 12.92 * c if c <= 0.0031308 else 1.055 * (c ** (1/2.4)) - 0.055

    return gamma(r_lin), gamma(g_lin), gamma(b_lin)


def tint_color_perceptual(base_rgb: Tuple[int, int, int], tint_idx: int) -> QColor:
    """Get perceptually distinct color variant using CIELAB lightness.

    Uses CIELAB color space which is designed so equal distances
    represent equal perceived color differences (perceptual uniformity).
    """
    r, g, b = base_rgb
    # Convert to LAB
    L, a, b_lab = _rgb_to_lab(r / 255.0, g / 255.0, b / 255.0)

    # Set L* to perceptually uniform level, keep a* and b* (chromatic channels)
    target_L = BORDER_LAB_LIGHTNESS[tint_idx % len(BORDER_LAB_LIGHTNESS)]

    # Convert back to RGB
    r2, g2, b2 = _lab_to_rgb(target_L, a, b_lab)
    return QColor(int(r2 * 255), int(g2 * 255), int(b2 * 255))


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
    """Extract per-orchestrator step index from scope_id.

    Handles multiple token formats:
    - plate::step@5 → 5 (legacy @ notation)
    - plate::functionstep_3 → 3 (ScopeTokenService format: prefix_N)
    - Falls back to MD5 hash for unknown formats
    """
    import re

    if "::" not in scope_id:
        return 0
    step_part = scope_id.split("::")[1]

    # Try @ notation first (legacy)
    if "@" in step_part:
        try:
            position_str = step_part.split("@")[1]
            return int(position_str)
        except (IndexError, ValueError):
            pass

    # Try ScopeTokenService format: prefix_N (e.g., "functionstep_3")
    match = re.search(r"_(\d+)$", step_part)
    if match:
        return int(match.group(1))

    # Fallback to MD5 hash for unknown formats
    hash_bytes = hashlib.md5(step_part.encode()).digest()
    return int.from_bytes(hash_bytes[:2], byteorder="big") % 27


def hsv_to_rgb(hue: int, saturation: int, value: int) -> tuple[int, int, int]:
    """Convert HSV color to RGB tuple."""
    h = hue / 360.0
    s = saturation / 100.0
    v = value / 100.0
    r, g, b = colorsys.hsv_to_rgb(h, s, v)
    return (int(r * 255), int(g * 255), int(b * 255))


def get_scope_color_scheme(scope_id: Optional[str], step_index: Optional[int] = None) -> ScopeColorScheme:
    """Get color scheme for scope via service.

    Args:
        scope_id: The scope identifier (e.g., "plate_path::functionstep_0")
        step_index: Optional explicit step index (position in pipeline).
                    If provided, overrides extraction from scope_id.
                    Use this for list items where actual position matters.
    """
    try:
        from pyqt_formgen.services.scope_color_service import ScopeColorService
        return ScopeColorService.instance().get_color_scheme(scope_id, step_index=step_index)
    except ImportError:
        # Return a default color scheme if service not available
        return ScopeColorScheme()


def _build_color_scheme_from_rgb(
    base_rgb: Tuple[int, int, int],
    scope_id: str,
    step_index: Optional[int] = None,
) -> ScopeColorScheme:
    """Build color scheme for a given base RGB and scope_id.

    Args:
        base_rgb: The base color for the scope (from palette)
        scope_id: The scope identifier
        step_index: Optional explicit step index. If provided, uses this for
                    border pattern calculation instead of extracting from scope_id.
    """
    orchestrator_scope = extract_orchestrator_scope(scope_id)

    orch_bg_rgb = base_rgb
    # Use perceptual middle tint (index 1) for orchestrator border, with darker(120)
    orch_border_qcolor = tint_color_perceptual(base_rgb, 1).darker(120)
    orch_border_rgb = (orch_border_qcolor.red(), orch_border_qcolor.green(), orch_border_qcolor.blue())

    step_item_rgb = orch_bg_rgb

    # Check if this is an orchestrator-level scope (no "::" = no step)
    is_orchestrator_level = "::" not in (scope_id or "")

    if is_orchestrator_level:
        # Orchestrator-level: use fixed middle tint, solid pattern, single layer
        # This ensures plate list items AND their config windows use the same color
        step_border_layers = [(3, 1, "solid")]  # middle tint, solid
        step_border_width = 3
        tint_index = 1
    else:
        # Step-level: use position-based variation for visual distinction
        # Use explicit step_index if provided, otherwise extract from scope_id
        if step_index is None:
            step_index = extract_step_index(scope_id)

        # Adjacent steps must have DIFFERENT tints (colors)
        # Same pattern is OK - patterns only change after exhausting tints
        # Order: cycle through all 3 tints, then change pattern
        border_patterns = ["solid", "dashed", "dotted", "dashdot"]
        num_patterns = len(border_patterns)
        num_tints = 3

        # Combos: 3 tints × 4 patterns = 12 per layer
        combos_per_layer = num_tints * num_patterns  # 12

        # Determine number of layers needed
        num_border_layers = (step_index // combos_per_layer) + 1
        # Cap at reasonable max
        num_border_layers = min(num_border_layers, 4)

        step_border_layers = []
        for layer in range(num_border_layers):
            # Offset each layer to ensure layers within same step differ
            effective_index = step_index + (layer * 5)

            # Tint cycles every step (adjacent steps always differ in color)
            border_tint = effective_index % num_tints
            # Pattern changes only after cycling through all tints
            pattern_idx = (effective_index // num_tints) % num_patterns
            border_pattern = border_patterns[pattern_idx]

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
