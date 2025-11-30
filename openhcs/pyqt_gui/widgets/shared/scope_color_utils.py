"""Utilities for generating scope-based colors using perceptually distinct palettes.

This module provides:
- Helper functions for color manipulation and extraction
- The main get_scope_color_scheme() function that delegates to ScopeColorService
- Internal _build_color_scheme_from_rgb() for constructing schemes from base colors

The actual color generation is handled by pluggable strategies via ScopeColorService.
"""

import hashlib
import colorsys
import logging
from typing import Optional, Tuple

from .scope_visual_config import ScopeColorScheme

logger = logging.getLogger(__name__)


def _ensure_wcag_compliant(
    color_rgb: tuple[int, int, int],
    background: tuple[int, int, int] = (255, 255, 255),
    min_ratio: float = 4.5
) -> tuple[int, int, int]:
    """Ensure color meets WCAG AA contrast requirements against background.

    Args:
        color_rgb: RGB color tuple (0-255 range)
        background: Background RGB color tuple (0-255 range), default white
        min_ratio: Minimum contrast ratio (4.5 for WCAG AA normal text, 3.0 for large text)

    Returns:
        Adjusted RGB color tuple that meets contrast requirements
    """
    try:
        from wcag_contrast_ratio.contrast import rgb as wcag_rgb

        # Convert to 0-1 range for wcag library
        color_01 = tuple(c / 255.0 for c in color_rgb)
        bg_01 = tuple(c / 255.0 for c in background)

        # Calculate current contrast ratio
        current_ratio = wcag_rgb(color_01, bg_01)

        if current_ratio >= min_ratio:
            return color_rgb  # Already compliant

        # Darken color until it meets contrast requirements
        # Convert to HSV for easier manipulation
        h, s, v = colorsys.rgb_to_hsv(*color_01)

        # Reduce value (brightness) to increase contrast
        while v > 0.1:  # Don't go completely black
            v *= 0.9  # Reduce by 10% each iteration
            adjusted_rgb_01 = colorsys.hsv_to_rgb(h, s, v)
            ratio = wcag_rgb(adjusted_rgb_01, bg_01)

            if ratio >= min_ratio:
                # Convert back to 0-255 range
                adjusted_rgb = tuple(int(c * 255) for c in adjusted_rgb_01)
                logger.debug(f"Adjusted color from ratio {current_ratio:.2f} to {ratio:.2f}")
                return adjusted_rgb

        # If we couldn't meet requirements by darkening, return darkest version
        logger.warning(f"Could not meet WCAG contrast ratio {min_ratio} for color {color_rgb}")
        return tuple(int(c * 255) for c in colorsys.hsv_to_rgb(h, s, 0.1))

    except ImportError:
        logger.warning("wcag-contrast-ratio not installed, skipping WCAG compliance check")
        return color_rgb
    except Exception as e:
        logger.warning(f"WCAG compliance check failed: {e}")
        return color_rgb


def extract_orchestrator_scope(scope_id: Optional[str]) -> Optional[str]:
    """Extract orchestrator scope from a scope_id.
    
    Scope IDs follow the pattern:
    - Orchestrator scope: "plate_path" (e.g., "/path/to/plate")
    - Step scope: "plate_path::step_token" (e.g., "/path/to/plate::step_0")
    
    Args:
        scope_id: Full scope identifier (can be orchestrator or step scope)
        
    Returns:
        Orchestrator scope (plate_path) or None if scope_id is None
        
    Examples:
        >>> extract_orchestrator_scope("/path/to/plate")
        '/path/to/plate'
        >>> extract_orchestrator_scope("/path/to/plate::step_0")
        '/path/to/plate'
        >>> extract_orchestrator_scope(None)
        None
    """
    if scope_id is None:
        return None
    
    # Split on :: separator
    if '::' in scope_id:
        return scope_id.split('::', 1)[0]
    else:
        return scope_id





def extract_step_index(scope_id: str) -> int:
    """Extract per-orchestrator step index from step scope_id.

    The scope_id format is "plate_path::step_token@position" where position
    is the step's index within its orchestrator's pipeline (0-based).

    This ensures each orchestrator has independent step indexing for visual styling.

    Args:
        scope_id: Step scope in format "plate_path::step_token@position"

    Returns:
        Step index (0-based) for visual styling, or 0 if not a step scope
    """
    if '::' not in scope_id:
        return 0

    # Extract the part after ::
    step_part = scope_id.split('::')[1]

    # Check if position is included (format: "step_token@position")
    if '@' in step_part:
        try:
            position_str = step_part.split('@')[1]
            return int(position_str)
        except (IndexError, ValueError):
            pass

    # Fallback for old format without @position: hash the step token
    hash_bytes = hashlib.md5(step_part.encode()).digest()
    return int.from_bytes(hash_bytes[:2], byteorder='big') % 27


def hsv_to_rgb(hue: int, saturation: int, value: int) -> tuple[int, int, int]:
    """Convert HSV color to RGB tuple.
    
    Args:
        hue: Hue in range [0, 359]
        saturation: Saturation in range [0, 100]
        value: Value (brightness) in range [0, 100]
        
    Returns:
        RGB tuple with values in range [0, 255]
    """
    # Normalize to [0, 1] range for colorsys
    h = hue / 360.0
    s = saturation / 100.0
    v = value / 100.0
    
    # Convert to RGB
    r, g, b = colorsys.hsv_to_rgb(h, s, v)
    
    # Scale to [0, 255]
    return (int(r * 255), int(g * 255), int(b * 255))


def get_scope_color_scheme(scope_id: Optional[str]) -> ScopeColorScheme:
    """Get color scheme for scope via ScopeColorService.

    This is the main entry point for getting scope colors. Delegates to
    ScopeColorService which handles caching, strategy selection, and reactive updates.

    Args:
        scope_id: Scope identifier (can be orchestrator or step scope)

    Returns:
        ScopeColorScheme with all derived colors and border info
    """
    from .services.scope_color_service import ScopeColorService
    return ScopeColorService.instance().get_color_scheme(scope_id)


def _build_color_scheme_from_rgb(
    base_rgb: Tuple[int, int, int],
    scope_id: str
) -> ScopeColorScheme:
    """Build complete color scheme from base RGB color.

    Internal function used by ScopeColorService. Takes a base color (from any strategy)
    and builds the full scheme with all derived colors and border layers.

    Args:
        base_rgb: Base RGB color tuple (0-255 range)
        scope_id: Scope identifier for step index extraction

    Returns:
        ScopeColorScheme with all derived colors and border info
    """
    # Extract orchestrator scope (removes step token if present)
    orchestrator_scope = extract_orchestrator_scope(scope_id)

    # Orchestrator background is base color (transparency handled in to_qcolor methods)
    orch_bg_rgb = base_rgb

    # Darker version for border (scale by ~0.78)
    orch_border_rgb = tuple(int(c * 200 / 255) for c in base_rgb)

    # Get step index for border logic
    step_index = extract_step_index(scope_id) if '::' in (scope_id or '') else 0

    # Steps use same color as orchestrator
    step_item_rgb = orch_bg_rgb

    # === BORDER LAYER CALCULATION ===
    # Cycle through 9 tint+pattern combinations before adding layers:
    # - 3 tints (0=dark, 1=neutral, 2=bright)
    # - 3 patterns (solid, dashed, dotted)
    num_border_layers = (step_index // 9) + 1
    combo_index = step_index % 9
    step_pattern_index = combo_index // 3
    step_tint = combo_index % 3

    border_patterns = ['solid', 'dashed', 'dotted']
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

    # === STEP WINDOW BORDER ===
    tint_index = step_index % 3
    tint_factors = [0.7, 1.0, 1.4]
    tint_factor = tint_factors[tint_index]
    step_window_rgb = tuple(min(255, int(c * tint_factor)) for c in base_rgb)

    # === WCAG COMPLIANCE ===
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

