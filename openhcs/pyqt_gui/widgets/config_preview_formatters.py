"""
Centralized config preview formatters for UI widgets.

Single source of truth for how config fields are formatted in preview labels
across PipelineEditor, PlateManager, and other widgets.
"""

from typing import Any, Optional, Dict, Callable


# Config attribute name to display abbreviation mapping
# Maps config attribute names to their preview text indicators
CONFIG_INDICATORS: Dict[str, str] = {
    'step_well_filter_config': 'FILT',
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
        Formatted indicator string (e.g., 'NAP', 'FILT+5' or 'FILT-A01') or None if disabled
    """
    from openhcs.core.config import WellFilterConfig, WellFilterMode

    if not isinstance(config, WellFilterConfig):
        return None

    # CRITICAL: Check enabled field first (for streaming configs that inherit from WellFilterConfig)
    # This ensures NAP/FIJI/MAT only show if enabled=True
    is_enabled = _check_enabled_field(config, resolve_attr)
    if not is_enabled:
        return None

    # Get base indicator
    indicator = CONFIG_INDICATORS.get(config_attr, 'FILT')

    # Resolve well_filter value
    if resolve_attr:
        well_filter = resolve_attr(None, config, 'well_filter', None)
        mode = resolve_attr(None, config, 'well_filter_mode', None)
    else:
        well_filter = getattr(config, 'well_filter', None)
        mode = getattr(config, 'well_filter_mode', WellFilterMode.INCLUDE)

    # If well_filter is None, just show the indicator (e.g., 'NAP', 'FIJI', 'MAT')
    if well_filter is None:
        return indicator

    # Format well_filter for display
    if isinstance(well_filter, list):
        wf_display = str(len(well_filter))
    elif isinstance(well_filter, int):
        wf_display = str(well_filter)
    else:
        wf_display = str(well_filter)

    # Add +/- prefix for INCLUDE/EXCLUDE mode
    mode_prefix = '-' if mode == WellFilterMode.EXCLUDE else '+'

    return f"{indicator}{mode_prefix}{wf_display}"


def check_config_has_unsaved_changes(
    config_attr: str,
    config: Any,
    resolve_attr: Optional[Callable],
    parent_obj: Any,
    live_context_snapshot: Any,
    scope_filter: Optional[str] = None,
    saved_context_snapshot: Any = None
) -> bool:
    """Check if a config has unsaved changes by comparing resolved values.

    Compares resolved config fields between:
    - live_context_snapshot (WITH active form managers = unsaved edits)
    - saved_context_snapshot (WITHOUT active form managers = saved values)

    PERFORMANCE: Uses batch resolution to resolve all fields at once instead of
    one-by-one, and exits early on first difference.

    Args:
        config_attr: Config attribute name (e.g., 'napari_streaming_config')
        config: Config object to check
        resolve_attr: Function to resolve lazy config attributes
                     Signature: resolve_attr(parent_obj, config_obj, attr_name, context) -> value
        parent_obj: Parent object containing the config (step or pipeline config)
        live_context_snapshot: Current live context snapshot (with form managers)
        scope_filter: Optional scope filter to use when collecting saved context (e.g., plate_path)
        saved_context_snapshot: Optional pre-collected saved context snapshot (for performance)

    Returns:
        True if config has unsaved changes, False otherwise
    """
    import dataclasses
    import logging
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

    logger = logging.getLogger(__name__)

    # If no resolver or parent, can't detect changes
    if not resolve_attr or parent_obj is None or live_context_snapshot is None:
        return False

    # Get all dataclass fields to compare
    if not dataclasses.is_dataclass(config):
        return False

    field_names = [f.name for f in dataclasses.fields(config)]
    if not field_names:
        return False

    # PERFORMANCE: Fast path - check if there's a form manager editing THIS SPECIFIC config field
    # OR a parent config field that this config inherits from
    # CRITICAL: Also check if the form manager has EMITTED any changes (has values in _last_emitted_values)
    # This prevents checking configs that have form managers but haven't been modified
    # Example: PipelineConfig editor creates form managers for ALL 16 configs, but only well_filter_config was edited
    has_form_manager_with_changes = False
    parent_type_name = type(parent_obj).__name__

    for manager in ParameterFormManager._active_form_managers:
        # Direct match: manager is editing this exact config field
        # Check both parent_type_name (e.g., "FunctionStep") and common field_ids (e.g., "step")
        if config_attr in manager.parameters:
            # Check if THIS SPECIFIC config field has been emitted (not just if the dict is non-empty)
            # _last_emitted_values is a dict like {'well_filter_config': LazyWellFilterConfig(...)}
            if hasattr(manager, '_last_emitted_values') and config_attr in manager._last_emitted_values:
                has_form_manager_with_changes = True
                logger.info(f"🔍 check_config_has_unsaved_changes: Found form manager with changes for {parent_type_name}.{config_attr} (manager.field_id={manager.field_id})")
                break

        # Inheritance match: manager is editing a parent config that this config inherits from
        # Example: config_attr="step_well_filter_config" inherits from "well_filter_config"
        if config_attr.startswith("step_") and manager.field_id == "PipelineConfig":
            base_config_name = config_attr.replace("step_", "", 1)  # "step_well_filter_config" → "well_filter_config"
            if base_config_name in manager.parameters:
                # Check if THIS SPECIFIC config field has been emitted
                if hasattr(manager, '_last_emitted_values') and base_config_name in manager._last_emitted_values:
                    has_form_manager_with_changes = True
                    logger.info(f"🔍 check_config_has_unsaved_changes: Found form manager with changes for {parent_type_name}.{config_attr} via inheritance from {base_config_name}")
                    break

    if not has_form_manager_with_changes:
        logger.debug(f"🔍 check_config_has_unsaved_changes: No form manager with changes for {parent_type_name}.{config_attr} - skipping field resolution")
        return False



    # Collect saved context snapshot if not provided (WITHOUT active form managers)
    # This is the key: temporarily clear form managers to get saved values
    # CRITICAL: Must increment token to bypass cache, otherwise we get cached live context
    # CRITICAL: Must use same scope_filter as live snapshot to get matching scoped values
    if saved_context_snapshot is None:
        saved_managers = ParameterFormManager._active_form_managers.copy()
        saved_token = ParameterFormManager._live_context_token_counter

        try:
            ParameterFormManager._active_form_managers.clear()
            # Increment token to force cache miss
            ParameterFormManager._live_context_token_counter += 1
            saved_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=scope_filter)
        finally:
            # Restore active form managers and token
            ParameterFormManager._active_form_managers[:] = saved_managers
            ParameterFormManager._live_context_token_counter = saved_token

    # PERFORMANCE: Compare each field and exit early on first difference
    for field_name in field_names:
        # Resolve in LIVE context (with form managers = unsaved edits)
        live_value = resolve_attr(parent_obj, config, field_name, live_context_snapshot)

        # Resolve in SAVED context (without form managers = saved values)
        saved_value = resolve_attr(parent_obj, config, field_name, saved_context_snapshot)

        # Compare values - exit early on first difference
        if live_value != saved_value:
            return True

    return False


def check_step_has_unsaved_changes(
    step: Any,
    config_indicators: dict,
    resolve_attr: Callable,
    live_context_snapshot: Any,
    scope_filter: Optional[str] = None,
    saved_context_snapshot: Any = None
) -> bool:
    """Check if a step has ANY unsaved changes in any of its configs.

    CRITICAL: Checks ALL dataclass configs on the step, not just the ones in config_indicators!
    config_indicators is only used for display formatting, but unsaved changes detection
    must check ALL configs (including step_well_filter_config, processing_config, etc.)

    PERFORMANCE:
    - Caches result by (step_id, live_context_token) to avoid redundant checks
    - Collects saved context snapshot ONCE and reuses it for all config checks
    - Exits early on first detected change

    Args:
        step: FunctionStep to check
        config_indicators: Dict mapping config attribute names to indicators (NOT USED for detection, only for compatibility)
        resolve_attr: Function to resolve lazy config attributes
        live_context_snapshot: Current live context snapshot
        scope_filter: Optional scope filter to use when collecting saved context (e.g., plate_path)
        saved_context_snapshot: Optional pre-collected saved context snapshot (for batch processing)

    Returns:
        True if step has any unsaved changes, False otherwise
    """
    import logging
    import dataclasses
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager

    logger = logging.getLogger(__name__)

    logger.info(f"🔍 check_step_has_unsaved_changes: Checking step '{getattr(step, 'name', 'unknown')}', live_context_snapshot={live_context_snapshot is not None}")

    # PERFORMANCE: Cache result by (step_id, token) to avoid redundant checks
    # Use id(step) as unique identifier for this step instance
    if live_context_snapshot is not None:
        cache_key = (id(step), live_context_snapshot.token)
        if not hasattr(check_step_has_unsaved_changes, '_cache'):
            check_step_has_unsaved_changes._cache = {}

        if cache_key in check_step_has_unsaved_changes._cache:
            cached_result = check_step_has_unsaved_changes._cache[cache_key]
            logger.info(f"🔍 check_step_has_unsaved_changes: Using cached result for step '{getattr(step, 'name', 'unknown')}': {cached_result}")
            return cached_result

        logger.info(f"🔍 check_step_has_unsaved_changes: Cache miss for step '{getattr(step, 'name', 'unknown')}', proceeding with check")
    else:
        logger.info(f"🔍 check_step_has_unsaved_changes: No live_context_snapshot provided, returning False")
        return False

    # PERFORMANCE: Collect saved context snapshot ONCE for all configs
    # This avoids collecting it separately for each config (3x per step)
    # If saved_context_snapshot is provided, reuse it (for batch processing of multiple steps)
    if saved_context_snapshot is None:
        saved_managers = ParameterFormManager._active_form_managers.copy()
        saved_token = ParameterFormManager._live_context_token_counter

        try:
            ParameterFormManager._active_form_managers.clear()
            ParameterFormManager._live_context_token_counter += 1
            saved_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=scope_filter)
        finally:
            ParameterFormManager._active_form_managers[:] = saved_managers
            ParameterFormManager._live_context_token_counter = saved_token

    # CRITICAL: Check ALL dataclass configs on the step, not just the ones in config_indicators!
    # Works for both dataclass and non-dataclass objects (e.g., FunctionStep)
    # Pattern from LiveContextResolver.resolve_all_lazy_attrs()

    # Discover attribute names from the object
    if dataclasses.is_dataclass(step):
        # Dataclass: use fields() to get all field names
        all_field_names = [f.name for f in dataclasses.fields(step)]
        logger.info(f"🔍 check_step_has_unsaved_changes: Step is dataclass, found {len(all_field_names)} fields")
    else:
        # Non-dataclass: introspect object to find dataclass attributes
        # Get all attributes from the object's __dict__ and class
        all_field_names = []
        for attr_name in dir(step):
            if attr_name.startswith('_'):
                continue
            try:
                attr_value = getattr(step, attr_name)
                # Check if this attribute is a dataclass (lazy or not)
                if dataclasses.is_dataclass(attr_value):
                    all_field_names.append(attr_name)
            except (AttributeError, TypeError):
                continue
        logger.info(f"🔍 check_step_has_unsaved_changes: Step is non-dataclass, found {len(all_field_names)} dataclass attrs")

    # Filter to only dataclass attributes
    all_config_attrs = []
    for field_name in all_field_names:
        field_value = getattr(step, field_name, None)
        if field_value is not None and dataclasses.is_dataclass(field_value):
            all_config_attrs.append(field_name)

    logger.info(f"🔍 check_step_has_unsaved_changes: Found {len(all_config_attrs)} dataclass configs: {all_config_attrs}")

    # Check each config for unsaved changes (exits early on first change)
    for config_attr in all_config_attrs:
        config = getattr(step, config_attr, None)
        if config is None:
            continue

        has_changes = check_config_has_unsaved_changes(
            config_attr,
            config,
            resolve_attr,
            step,
            live_context_snapshot,
            scope_filter=scope_filter,
            saved_context_snapshot=saved_context_snapshot  # PERFORMANCE: Reuse saved snapshot
        )

        if has_changes:
            logger.debug(f"✅ UNSAVED CHANGES DETECTED in step '{getattr(step, 'name', 'unknown')}' config '{config_attr}'")
            if live_context_snapshot is not None:
                check_step_has_unsaved_changes._cache[cache_key] = True
            return True

    # No changes found - cache the result
    if live_context_snapshot is not None:
        check_step_has_unsaved_changes._cache[cache_key] = False
    return False


def format_config_indicator(
    config_attr: str,
    config: Any,
    resolve_attr: Optional[Callable] = None,
    parent_obj: Any = None,
    live_context_snapshot: Any = None
) -> Optional[str]:
    """Format any config for preview display (dispatcher function).

    GENERAL RULE: Any config with an 'enabled: bool' parameter will only show
    if it resolves to True.

    Note: Unsaved changes are now indicated at the step/item level (in the step name),
    not per-config label. The parent_obj and live_context_snapshot parameters are kept
    for backward compatibility but are not used here.

    Args:
        config_attr: Config attribute name
        config: Config object
        resolve_attr: Optional function to resolve lazy config attributes
        parent_obj: Optional parent object (kept for backward compatibility)
        live_context_snapshot: Optional live context snapshot (kept for backward compatibility)

    Returns:
        Formatted indicator string or None if config should not be shown.
    """
    from openhcs.core.config import WellFilterConfig

    # Dispatch to specific formatter based on config type
    if isinstance(config, WellFilterConfig):
        result = format_well_filter_config(config_attr, config, resolve_attr)
    else:
        # All other configs use generic formatter (checks enabled field automatically)
        result = format_generic_config(config_attr, config, resolve_attr)

    return result

