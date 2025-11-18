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

    # PERFORMANCE: Fast path - check if there's a form manager that has emitted changes
    # for a field whose PATH or TYPE matches (or is related to) this config's type.
    #
    # CRITICAL: Use PATH-BASED and TYPE-BASED matching, not name-based patterns!
    # This avoids hardcoding "step_" prefix or specific type names.
    #
    # Algorithm:
    # 1. Direct path match: Check if field path contains config_attr
    #    (e.g., "GlobalPipelineConfig.step_materialization_config.well_filter" matches "step_materialization_config")
    # 2. Type-based match: Check if any emitted value's type matches this config's type
    #    (handles inheritance: step_well_filter_config inherits from well_filter_config)
    #
    # This works because _last_emitted_values is now keyed by full field paths.
    parent_type_name = type(parent_obj).__name__
    config_type = type(config)

    has_form_manager_with_changes = False

    for manager in ParameterFormManager._active_form_managers:
        if not hasattr(manager, '_last_emitted_values') or not manager._last_emitted_values:
            continue

        # CRITICAL: Apply scope filter to prevent cross-plate contamination
        # If scope_filter is provided (e.g., plate path), only check managers in that scope
        if scope_filter is not None and manager.scope_id is not None:
            if not ParameterFormManager._is_scope_visible_static(manager.scope_id, scope_filter):
                continue

        # Check each emitted field path
        # field_path format: "GlobalPipelineConfig.step_materialization_config.well_filter"
        for field_path, field_value in manager._last_emitted_values.items():
            # Direct path match: check if this field path references this config
            # Examples:
            #   config_attr="step_materialization_config"
            #   field_path="GlobalPipelineConfig.step_materialization_config.well_filter" → MATCH
            #   field_path="GlobalPipelineConfig.step_materialization_config" → MATCH
            #   field_path="PipelineConfig.step_well_filter_config" → NO MATCH
            path_parts = field_path.split('.')
            if len(path_parts) >= 2:
                # Second part is the config attribute (first part is the root object type)
                config_attr_from_path = path_parts[1]
                if config_attr_from_path == config_attr:
                    has_form_manager_with_changes = True
                    logger.debug(
                        f"🔍 check_config_has_unsaved_changes: Found path match for "
                        f"{config_attr} in field path {field_path}"
                    )
                    break

            # Type-based match: check if any emitted value's type is related to this config's type
            # This handles inheritance without hardcoding field names
            if field_value is not None:
                field_type = type(field_value)

                # Check if types are related via isinstance (handles MRO inheritance)
                # Example: LazyStepWellFilterConfig inherits from LazyWellFilterConfig
                if isinstance(config, field_type) or isinstance(field_value, config_type):
                    has_form_manager_with_changes = True
                    logger.debug(
                        f"🔍 check_config_has_unsaved_changes: Found type match for "
                        f"{config_attr} (config type={config_type.__name__}, "
                        f"emitted field={field_path}, field type={field_type.__name__})"
                    )
                    break

        if has_form_manager_with_changes:
            break

    if not has_form_manager_with_changes:
        logger.debug(
            "🔍 check_config_has_unsaved_changes: No form managers with changes for "
            f"{parent_type_name}.{config_attr} (config type={config_type.__name__}) - skipping field resolution"
        )
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

    step_token = getattr(step, '_pipeline_scope_token', None)
    logger.info(f"🔍 check_step_has_unsaved_changes: Checking step '{getattr(step, 'name', 'unknown')}', step_token={step_token}, scope_filter={scope_filter}, live_context_snapshot={live_context_snapshot is not None}")

    # Build expected step scope for this step (used for scope matching)
    expected_step_scope = None
    if scope_filter and step_token:
        expected_step_scope = f"{scope_filter}::{step_token}"
        logger.info(f"🔍 check_step_has_unsaved_changes: Expected step scope: {expected_step_scope}")

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
        logger.info(f"🔍 check_step_has_unsaved_changes: No live_context_snapshot provided, cache disabled")

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

    # PERFORMANCE: Fast path - check if ANY form manager has changes that could affect this step
    # Collect all config objects ONCE to avoid repeated getattr() calls
    step_configs = {}  # config_attr -> config object
    for config_attr in all_config_attrs:
        config = getattr(step, config_attr, None)
        if config is not None:
            step_configs[config_attr] = config

    # PERFORMANCE: Phase 1-ALT - O(1) type-based cache lookup
    # Instead of iterating through all managers and their emitted values,
    # check if any of this step's config TYPES have been marked as changed
    has_any_relevant_changes = False

    for config_attr, config in step_configs.items():
        config_type = type(config)
        if config_type in ParameterFormManager._configs_with_unsaved_changes:
            has_any_relevant_changes = True
            logger.debug(
                f"🔍 check_step_has_unsaved_changes: Type-based cache hit for {config_attr} "
                f"(type={config_type.__name__}, changed_fields={ParameterFormManager._configs_with_unsaved_changes[config_type]})"
            )
            break

    # Additional scope-based filtering for step-specific changes
    # If a step-specific scope is expected, verify at least one manager with matching scope has changes
    if has_any_relevant_changes and expected_step_scope:
        scope_matched = False
        for manager in ParameterFormManager._active_form_managers:
            if not hasattr(manager, '_last_emitted_values') or not manager._last_emitted_values:
                continue

            # CRITICAL: Apply plate-level scope filter to prevent cross-plate contamination
            # If scope_filter is provided (e.g., plate path), only check managers in that scope
            if scope_filter is not None and manager.scope_id is not None:
                if not ParameterFormManager._is_scope_visible_static(manager.scope_id, scope_filter):
                    continue

            # If manager has step-specific scope, it must match
            if manager.scope_id and '::step_' in manager.scope_id:
                if manager.scope_id == expected_step_scope:
                    scope_matched = True
                    logger.debug(f"🔍 check_step_has_unsaved_changes: Scope match found for {manager.field_id}")
                    break
            else:
                # Non-step-specific manager (plate/global) affects all steps
                scope_matched = True
                break

        if not scope_matched:
            has_any_relevant_changes = False
            logger.debug(f"🔍 check_step_has_unsaved_changes: Type-based cache hit, but no scope match for {expected_step_scope}")

    if not has_any_relevant_changes:
        logger.info(f"🔍 check_step_has_unsaved_changes: No relevant changes for step '{getattr(step, 'name', 'unknown')}' - skipping (fast-path)")
        if live_context_snapshot is not None:
            check_step_has_unsaved_changes._cache[cache_key] = False
        return False
    else:
        logger.info(f"🔍 check_step_has_unsaved_changes: Found relevant changes for step '{getattr(step, 'name', 'unknown')}' - proceeding to full check")

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
            logger.info(f"✅ UNSAVED CHANGES DETECTED in step '{getattr(step, 'name', 'unknown')}' config '{config_attr}'")
            if live_context_snapshot is not None:
                check_step_has_unsaved_changes._cache[cache_key] = True
            return True

    # No changes found - cache the result
    logger.info(f"🔍 check_step_has_unsaved_changes: No unsaved changes found for step '{getattr(step, 'name', 'unknown')}'")
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
