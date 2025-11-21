"""Utilities for generating scope-based colors using perceptually distinct palettes."""

import hashlib
import colorsys
import logging
from typing import Optional
from functools import lru_cache

from .scope_visual_config import ScopeVisualConfig, ScopeColorScheme

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


def get_scope_depth(scope_id: Optional[str]) -> int:
    """Get the depth (number of levels) in a hierarchical scope.

    GENERIC SCOPE RULE: Works for any N-level hierarchy.

    Examples:
        >>> get_scope_depth(None)
        0
        >>> get_scope_depth("plate")
        1
        >>> get_scope_depth("plate::step")
        2
        >>> get_scope_depth("plate::step::nested")
        3

    Args:
        scope_id: Hierarchical scope identifier

    Returns:
        Number of levels in the scope (0 for None/global)
    """
    if scope_id is None:
        return 0
    return scope_id.count('::') + 1


def extract_orchestrator_scope(scope_id: Optional[str]) -> Optional[str]:
    """Extract orchestrator scope from a scope_id.

    GENERIC SCOPE RULE: Extracts the ROOT (first level) of the scope hierarchy.
    Works for any N-level hierarchy by extracting everything before the first '::'.

    This is equivalent to extract_scope_segment(scope_id, 0).

    Examples:
        >>> extract_orchestrator_scope("/path/to/plate")
        '/path/to/plate'
        >>> extract_orchestrator_scope("/path/to/plate::step_0")
        '/path/to/plate'
        >>> extract_orchestrator_scope("/path/to/plate::step_0::nested")
        '/path/to/plate'
        >>> extract_orchestrator_scope(None)
        None

    Args:
        scope_id: Full scope identifier (can be any level in hierarchy)

    Returns:
        Root scope (orchestrator/plate level), or None if scope_id is None
    """
    if scope_id is None:
        return None

    # GENERIC: Extract first segment using generic utility
    # Note: We inline this for performance since it's called frequently
    if '::' in scope_id:
        return scope_id.split('::', 1)[0]
    else:
        return scope_id


@lru_cache(maxsize=256)
def _get_distinct_color_palette(n_colors: int = 50) -> list:
    """Generate perceptually distinct colors using distinctipy.

    Cached to avoid regenerating the same palette repeatedly.

    Args:
        n_colors: Number of distinct colors to generate

    Returns:
        List of RGB tuples (0-1 range)
    """
    try:
        from distinctipy import distinctipy
        # Generate perceptually distinct colors
        # Exclude very dark and very light colors for better visibility
        colors = distinctipy.get_colors(
            n_colors,
            exclude_colors=[(0, 0, 0), (1, 1, 1)],  # Exclude black and white
            pastel_factor=0.5  # Pastel for softer backgrounds
        )
        return colors
    except ImportError:
        # Fallback to simple HSV if distinctipy not available
        return [_hsv_to_rgb_normalized(int(360 * i / n_colors), 50, 80) for i in range(n_colors)]


def _hsv_to_rgb_normalized(hue: int, saturation: int, value: int) -> tuple[float, float, float]:
    """Convert HSV to RGB in 0-1 range.

    Args:
        hue: Hue (0-359)
        saturation: Saturation (0-100)
        value: Value/Brightness (0-100)

    Returns:
        RGB tuple (0-1, 0-1, 0-1)
    """
    h = hue / 360.0
    s = saturation / 100.0
    v = value / 100.0
    return colorsys.hsv_to_rgb(h, s, v)


def hash_scope_to_color_index(scope_id: str, palette_size: int = 50) -> int:
    """Generate deterministic color index from scope_id using hash.

    Args:
        scope_id: Scope identifier to hash
        palette_size: Size of color palette

    Returns:
        Color index for palette lookup
    """
    hash_bytes = hashlib.md5(scope_id.encode('utf-8')).digest()
    hash_int = int.from_bytes(hash_bytes[:4], byteorder='big')
    return hash_int % palette_size


def extract_scope_segment(scope_id: str, level: int = -1) -> Optional[str]:
    """Extract a specific segment from a hierarchical scope_id.

    GENERIC SCOPE RULE: Works for any N-level hierarchy.

    Examples:
        >>> extract_scope_segment("plate::step::nested", 0)
        'plate'
        >>> extract_scope_segment("plate::step::nested", 1)
        'step'
        >>> extract_scope_segment("plate::step::nested", 2)
        'nested'
        >>> extract_scope_segment("plate::step::nested", -1)
        'nested'
        >>> extract_scope_segment("plate::step::nested", -2)
        'step'
        >>> extract_scope_segment("plate", 0)
        'plate'
        >>> extract_scope_segment("plate", 1)
        None

    Args:
        scope_id: Hierarchical scope identifier
        level: Index of segment to extract (0-based, supports negative indexing)
               -1 = last segment (default), 0 = first segment, etc.

    Returns:
        The segment at the specified level, or None if level is out of bounds
    """
    if scope_id is None:
        return None

    segments = scope_id.split('::')

    try:
        return segments[level]
    except IndexError:
        return None


def extract_step_index(scope_id: str) -> int:
    """Extract per-orchestrator step index from step scope_id.

    GENERIC SCOPE RULE: Extracts the LAST segment of the scope hierarchy.
    Works for any N-level hierarchy by extracting everything after the last '::'.

    The scope_id format is "...::step_token@position" where position
    is the step's index within its orchestrator's pipeline (0-based).

    Examples:
        >>> extract_step_index("plate::step_0@5")
        5
        >>> extract_step_index("plate::nested::step_0@5")
        5
        >>> extract_step_index("plate")
        0

    Args:
        scope_id: Step scope in format "...::step_token@position"

    Returns:
        Step index (0-based) for visual styling, or 0 if not a step scope
    """
    if '::' not in scope_id:
        return 0

    # GENERIC: Extract the LAST segment using generic utility
    step_part = extract_scope_segment(scope_id, -1)
    if step_part is None:
        return 0

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


@lru_cache(maxsize=512)
def get_scope_color_scheme(scope_id: Optional[str]) -> ScopeColorScheme:
    """Generate complete color scheme for scope using perceptually distinct colors.

    Uses distinctipy to generate visually distinct colors for orchestrators.
    For steps, applies tinting based on step index and adds borders every 3 steps.

    PERFORMANCE: Cached with LRU cache to avoid repeated color calculations for the same scope.

    Args:
        scope_id: Scope identifier (can be orchestrator or step scope)

    Returns:
        ScopeColorScheme with all derived colors and border info
    """
    config = ScopeVisualConfig()

    # Extract orchestrator scope (removes step token if present)
    orchestrator_scope = extract_orchestrator_scope(scope_id)

    if orchestrator_scope is None:
        # Global scope: neutral gray
        return ScopeColorScheme(
            scope_id=None,
            hue=0,
            orchestrator_item_bg_rgb=(240, 240, 240),
            orchestrator_item_border_rgb=(180, 180, 180),
            step_window_border_rgb=(128, 128, 128),
            step_item_bg_rgb=(245, 245, 245),
            step_border_width=0,
        )

    # Get distinct color palette
    palette = _get_distinct_color_palette(50)

    # Get color index for this orchestrator
    color_idx = hash_scope_to_color_index(orchestrator_scope, len(palette))
    base_color = palette[color_idx]  # RGB in 0-1 range

    # Convert to 0-255 range for orchestrator (full color, transparency handled separately)
    orch_bg_rgb = tuple(int(c * 255) for c in base_color)

    # Darker version for border
    orch_border_rgb = tuple(int(c * 200) for c in base_color)

    # Get step index for border logic
    step_index = extract_step_index(scope_id) if '::' in (scope_id or '') else 0

    # === STEP LIST ITEMS ===
    # Steps use same color as orchestrator (full color, transparency handled separately)
    step_item_rgb = orch_bg_rgb

    # Calculate which borders to show (layering pattern)
    # Cycle through ALL tint+pattern combinations before adding layers:
    # - 3 tints (0=dark, 1=neutral, 2=bright)
    # - 3 patterns (solid, dashed, dotted)
    # - 9 combinations total per layer
    #
    # Pattern priority: cycle through colors FIRST, then patterns
    # Step 0-2:   solid with tints 0,1,2
    # Step 3-5:   dashed with tints 0,1,2
    # Step 6-8:   dotted with tints 0,1,2
    # Step 9-17:  2 borders (all combos)
    # Step 18-26: 3 borders (all combos)
    # etc.
    num_border_layers = (step_index // 9) + 1  # Always at least 1 border

    # Within each layer group, cycle through tint+pattern combinations
    combo_index = step_index % 9  # 0-8

    # Pattern cycles every 3 steps: solid, solid, solid, dashed, dashed, dashed, dotted, dotted, dotted
    step_pattern_index = combo_index // 3  # 0, 1, or 2

    # Tint cycles within each pattern group: 0, 1, 2
    step_tint = combo_index % 3

    # Store border info: list of (width, tint_index, pattern) tuples
    # Tint factors: [0.7, 1.0, 1.4] for MORE DRASTIC visual distinction (darker, neutral, brighter)
    # Patterns: 'solid', 'dashed', 'dotted' for additional differentiation
    # Build from innermost to outermost
    border_patterns = ['solid', 'dashed', 'dotted']
    step_border_layers = []
    for layer in range(num_border_layers):
        # First layer uses step's tint+pattern combo
        if layer == 0:
            border_tint = step_tint
            border_pattern = border_patterns[step_pattern_index]
        else:
            # Subsequent layers cycle through other tint+pattern combinations
            # Offset by layer to get different combinations
            layer_combo = (combo_index + layer * 3) % 9
            border_tint = (layer_combo // 3) % 3
            border_pattern = border_patterns[layer_combo % 3]

        step_border_layers.append((3, border_tint, border_pattern))  # 3px width, tint index, pattern

    # For backward compatibility, store total border width
    step_border_width = num_border_layers * 3

    # === STEP WINDOW BORDERS ===
    # Window border uses cycling tint based on step index
    tint_index = step_index % 3  # 0, 1, or 2
    tint_factors = [0.7, 1.0, 1.4]  # Tint 0 (darker), Tint 1 (neutral), Tint 2 (brighter) - MORE DRASTIC
    tint_factor = tint_factors[tint_index]
    step_window_rgb = tuple(min(255, int(c * 255 * tint_factor)) for c in base_color)

    # === WCAG COMPLIANCE CHECK ===
    # Ensure border colors meet WCAG AA contrast requirements (4.5:1 for normal text)
    orch_border_rgb = _ensure_wcag_compliant(orch_border_rgb, background=(255, 255, 255))
    step_window_rgb = _ensure_wcag_compliant(step_window_rgb, background=(255, 255, 255))

    return ScopeColorScheme(
        scope_id=orchestrator_scope,
        hue=0,  # Not used with distinctipy
        orchestrator_item_bg_rgb=orch_bg_rgb,
        orchestrator_item_border_rgb=orch_border_rgb,
        step_window_border_rgb=step_window_rgb,
        step_item_bg_rgb=step_item_rgb,
        step_border_width=step_border_width,
        step_border_layers=step_border_layers,
        base_color_rgb=orch_bg_rgb,  # Store base color for tint calculations
    )

