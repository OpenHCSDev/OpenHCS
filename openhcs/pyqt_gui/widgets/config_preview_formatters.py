"""
Centralized config preview formatters for UI widgets.

Single source of truth for how config fields are formatted in preview labels
across PipelineEditor, PlateManager, and other widgets.
"""

from typing import Any, Optional, Dict, Callable


# Config attribute name to display abbreviation mapping
# Maps config attribute names to their preview text indicators
CONFIG_INDICATORS: Dict[str, str] = {
    'step_materialization_config': 'MAT',
    'napari_streaming_config': 'NAP',
    'fiji_streaming_config': 'FIJI',
}


def _check_enabled_field(config: Any, resolve_attr: Optional[Callable] = None) -> bool:
    """Check if a config object is enabled.

    GENERAL RULE: Any config with an 'enabled: bool' parameter should only show
    if it resolves to True.

    Args:
        config: Config object to check
        resolve_attr: Optional function to resolve lazy config attributes

    Returns:
        True if config is enabled (or has no enabled field), False if disabled
    """
    import dataclasses

    # Check if config has 'enabled' field
    has_enabled = dataclasses.is_dataclass(config) and 'enabled' in {f.name for f in dataclasses.fields(config)}

    if has_enabled:
        # Resolve enabled field if resolver provided
        if resolve_attr:
            enabled = resolve_attr(None, config, 'enabled', None)
        else:
            enabled = getattr(config, 'enabled', False)

        return bool(enabled)

    # No enabled field - assume enabled
    return True


def format_generic_config(config_attr: str, config: Any, resolve_attr: Optional[Callable] = None) -> Optional[str]:
    """Format any config with an indicator for preview display.

    GENERAL RULE: Any config with an 'enabled: bool' parameter will only show
    if it resolves to True.

    Args:
        config_attr: Config attribute name (e.g., 'napari_streaming_config')
        config: Config object
        resolve_attr: Optional function to resolve lazy config attributes
                     Signature: resolve_attr(parent_obj, config_obj, attr_name, context) -> value

    Returns:
        Formatted indicator string (e.g., 'NAP') or None if config is disabled
    """
    # Get the base indicator
    indicator = CONFIG_INDICATORS.get(config_attr)
    if not indicator:
        return None

    # Check if config is enabled (general rule for all configs)
    is_enabled = _check_enabled_field(config, resolve_attr)
    if not is_enabled:
        return None

    return indicator


def format_well_filter_config(config_attr: str, config: Any, resolve_attr: Optional[Callable] = None) -> Optional[str]:
    """Format well filter config for preview display.

    GENERAL RULE: Any config with an 'enabled: bool' parameter will only show
    if it resolves to True. This applies to streaming configs (NAP/FIJI/MAT) which
    inherit from WellFilterConfig but also have an 'enabled' field.

    Args:
        config_attr: Config attribute name (e.g., 'step_well_filter_config')
        config: Config object (must be WellFilterConfig)
        resolve_attr: Optional function to resolve lazy config attributes

    Returns:
        Formatted indicator string (e.g., 'FILT+5' or 'FILT-A01') or None if no filter
    """
    from openhcs.core.config import WellFilterConfig, WellFilterMode

    if not isinstance(config, WellFilterConfig):
        return None

    # CRITICAL: Check enabled field first (for streaming configs that inherit from WellFilterConfig)
    # This ensures NAP/FIJI/MAT only show if enabled=True
    is_enabled = _check_enabled_field(config, resolve_attr)
    if not is_enabled:
        return None

    # Resolve well_filter value
    if resolve_attr:
        well_filter = resolve_attr(None, config, 'well_filter', None)
        mode = resolve_attr(None, config, 'well_filter_mode', None)
    else:
        well_filter = getattr(config, 'well_filter', None)
        mode = getattr(config, 'well_filter_mode', WellFilterMode.INCLUDE)

    if well_filter is None:
        return None

    # Format well_filter for display
    if isinstance(well_filter, list):
        wf_display = str(len(well_filter))
    elif isinstance(well_filter, int):
        wf_display = str(well_filter)
    else:
        wf_display = str(well_filter)

    # Add +/- prefix for INCLUDE/EXCLUDE mode
    mode_prefix = '-' if mode == WellFilterMode.EXCLUDE else '+'

    indicator = CONFIG_INDICATORS.get(config_attr, 'FILT')
    return f"{indicator}{mode_prefix}{wf_display}"


def format_config_indicator(config_attr: str, config: Any, resolve_attr: Optional[Callable] = None) -> Optional[str]:
    """Format any config for preview display (dispatcher function).

    GENERAL RULE: Any config with an 'enabled: bool' parameter will only show
    if it resolves to True.

    Args:
        config_attr: Config attribute name
        config: Config object
        resolve_attr: Optional function to resolve lazy config attributes

    Returns:
        Formatted indicator string or None if config should not be shown
    """
    from openhcs.core.config import WellFilterConfig

    # Dispatch to specific formatter based on config type
    if isinstance(config, WellFilterConfig):
        return format_well_filter_config(config_attr, config, resolve_attr)
    else:
        # All other configs use generic formatter (checks enabled field automatically)
        return format_generic_config(config_attr, config, resolve_attr)

