"""
Consolidated Parameter Operations Service.

Merges:
- ParameterResetService: Type-safe parameter reset with discriminated union dispatch
- PlaceholderRefreshService: Placeholder resolution and live context management

Key features:
1. Type-safe dispatch using ParameterInfo discriminated unions
2. Auto-discovery of handlers via ParameterServiceABC
3. Placeholder resolution with live context from other windows
4. Consistent widget update + signal emission
"""

from __future__ import annotations
from typing import Any, TYPE_CHECKING
import logging

from openhcs.utils.performance_monitor import timer, get_monitor
from .parameter_service_abc import ParameterServiceABC

if TYPE_CHECKING:
    from openhcs.ui.shared.parameter_info_types import (
        OptionalDataclassInfo,
        DirectDataclassInfo,
        GenericInfo
    )

logger = logging.getLogger(__name__)


def _compute_overlay(
    manager,
    exclude_field: str | None = None,
) -> dict | None:
    """
    Compute overlay dict for context stack building.

    Consolidates overlay computation for both bulk and targeted refresh:
    - Selects base values from manager.parameters
    - Excludes specified field if needed (for single-field refresh)
    - Includes exclude_params from object_instance (for hidden fields)

    Args:
        manager: The parameter form manager
        exclude_field: Field name to exclude from overlay (prevents self-shadowing)

    Returns:
        Dict of overlay values, or None if no values
    """
    from dataclasses import is_dataclass, fields

    base = manager.parameters
    if not base:
        return None

    overlay = base.copy()

    # Exclude field being resolved (prevents None value from shadowing inherited value)
    if exclude_field:
        overlay.pop(exclude_field, None)

    # Include exclude_params from object_instance (hidden fields not in form)
    obj = manager.object_instance
    exclude_params = getattr(manager, 'exclude_params', None) or []
    if obj and exclude_params:
        if is_dataclass(obj):
            allowed = {f.name for f in fields(obj)}
        else:
            allowed = set(dir(obj))
        for excluded in exclude_params:
            if excluded not in overlay and excluded in allowed:
                overlay[excluded] = getattr(obj, excluded)

    return overlay


def _build_live_values(
    manager,
    live_context: dict[type, dict] | None,
    exclude_field: str | None = None,
) -> dict[type, dict] | None:
    """
    Build unified live_values dict for build_context_stack.

    Merges cross-window live context with current manager's overlay values.
    The overlay is keyed by manager's object_instance type.

    Args:
        manager: The parameter form manager
        live_context: Dict from collect_live_context (type → values)
        exclude_field: Field to exclude from overlay (prevents self-shadowing)

    Returns:
        Merged dict[type, dict] for build_context_stack, or None if empty
    """
    overlay = _compute_overlay(manager, exclude_field=exclude_field)
    mgr_type = type(manager.object_instance)

    if live_context is None and overlay is None:
        return None

    # Start with live_context copy or empty dict
    live_values = dict(live_context) if live_context else {}

    # Merge overlay into live_values under manager's type
    if overlay is not None:
        live_values[mgr_type] = overlay

    return live_values if live_values else None


class ParameterOpsService(ParameterServiceABC):
    """
    Consolidated service for parameter reset and placeholder refresh.

    Examples:
        service = ParameterOpsService()

        # Reset parameter:
        service.reset_parameter(manager, param_name)
        
        # Refresh placeholders with live context:
        service.refresh_with_live_context(manager)
        
        # Refresh all placeholders in a form:
        service.refresh_all_placeholders(manager)
    """

    def __init__(self):
        """Initialize with widget operations dependency."""
        super().__init__()
        from openhcs.ui.shared.widget_operations import WidgetOperations
        self.widget_ops = WidgetOperations

    def _get_handler_prefix(self) -> str:
        """Return handler method prefix for auto-discovery."""
        return '_reset_'

    # ========== PARAMETER RESET (from ParameterResetService) ==========

    def reset_parameter(self, manager, param_name: str) -> None:
        """Reset parameter using type-safe dispatch."""
        info = manager.form_structure.get_parameter_info(param_name)
        self.dispatch(info, manager)

    def _reset_OptionalDataclassInfo(self, info: OptionalDataclassInfo, manager) -> None:
        """Reset Optional[Dataclass] field - sync checkbox and reset nested manager."""
        param_name = info.name
        reset_value = self._get_reset_value(manager, param_name)
        manager.parameters[param_name] = reset_value

        if param_name in manager.widgets:
            container = manager.widgets[param_name]
            from .widget_service import WidgetService
            from .signal_service import SignalService

            checkbox = WidgetService.find_optional_checkbox(manager, param_name)
            if checkbox:
                with SignalService.block_signals(checkbox):
                    checkbox.setChecked(reset_value is not None and reset_value.enabled)

            try:
                group = WidgetService.find_group_box(container)
                if group:
                    group.setEnabled(reset_value is not None)
            except Exception:
                pass

        nested_manager = manager.nested_managers.get(param_name)
        if nested_manager:
            nested_manager.reset_all_parameters()

    def _reset_DirectDataclassInfo(self, info: DirectDataclassInfo, manager) -> None:
        """Reset direct Dataclass field - reset nested manager only.

        NOTE: We do NOT call update_widget_value on the container widget here.
        DirectDataclass fields use GroupBoxWithHelp containers which don't implement
        ValueSettable (they're just containers, not value widgets). The nested manager's
        reset_all_parameters() call handles resetting all the actual value widgets inside.
        """
        param_name = info.name
        nested_manager = manager.nested_managers.get(param_name)
        if nested_manager:
            nested_manager.reset_all_parameters()

    def _reset_GenericInfo(self, info: GenericInfo, manager) -> None:
        """Reset generic field to signature default.

        SIMPLIFIED: Set value and refresh placeholder with proper context.
        Same approach as reset_all_parameters but for single field.
        """
        param_name = info.name
        reset_value = self._get_reset_value(manager, param_name)
        logger.info(f"      🔧 _reset_GenericInfo: {manager.field_id}.{param_name} -> {repr(reset_value)[:30]}")

        # Update parameters and tracking
        manager.parameters[param_name] = reset_value
        self._update_reset_tracking(manager, param_name, reset_value)

        # CRITICAL: Invalidate cache token BEFORE refreshing placeholder
        # Otherwise refresh_single_placeholder will use stale cached values
        from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
        LiveContextService.increment_token()

        if param_name in manager.widgets:
            widget = manager.widgets[param_name]

            # Update widget value
            from .signal_service import SignalService
            with SignalService.block_signals(widget):
                manager._widget_service.update_widget_value(
                    widget, reset_value, param_name, skip_context_behavior=False, manager=manager
                )

            # Refresh placeholder with proper context (same as reset_all_parameters does)
            # This builds context stack with root values for sibling inheritance
            if reset_value is None:
                self.refresh_single_placeholder(manager, param_name)

            logger.info(f"      ✅ Reset complete")

    @staticmethod
    def _get_reset_value(manager, param_name: str) -> Any:
        """Get reset value based on editing context."""
        if manager.config.is_global_config_editing and manager.object_instance:
            try:
                return object.__getattribute__(type(manager.object_instance), param_name)
            except AttributeError:
                pass
        return manager.param_defaults.get(param_name)

    @staticmethod
    def _update_reset_tracking(manager, param_name: str, reset_value: Any) -> None:
        """Update reset field tracking for lazy behavior."""
        field_path = f"{manager.field_id}.{param_name}"
        if reset_value is None:
            manager.reset_fields.add(param_name)
            manager.shared_reset_fields.add(field_path)
            manager._user_set_fields.discard(param_name)
        else:
            manager.reset_fields.discard(param_name)
            manager.shared_reset_fields.discard(field_path)

    # ========== PLACEHOLDER REFRESH (from PlaceholderRefreshService) ==========

    # DELETED: refresh_affected_siblings - moved to FieldChangeDispatcher

    def refresh_single_placeholder(self, manager, field_name: str) -> None:
        """Refresh placeholder for a single field in a manager.

        Only updates if:
        1. The field exists as a widget in the manager
        2. The current value is None (needs placeholder)

        Args:
            manager: The manager containing the field
            field_name: Name of the field to refresh
        """
        logger.info(f"        🔄 refresh_single_placeholder: {manager.field_id}.{field_name}")

        # Check if field exists in this manager's widgets
        if field_name not in manager.widgets:
            logger.warning(f"        ⏭️  {field_name} not in widgets")
            return

        # Only refresh if value is None (needs placeholder)
        current_value = manager.parameters.get(field_name)
        if current_value is not None:
            logger.info(f"        ⏭️  {field_name} has value={repr(current_value)[:30]}, no placeholder needed")
            return

        logger.info(f"        ✅ {field_name} value is None, computing placeholder...")

        from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
        from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
        from openhcs.config_framework.context_manager import build_context_stack

        # Find root manager for scope-filtered collection
        root_manager = manager
        while root_manager._parent_manager is not None:
            root_manager = root_manager._parent_manager

        # Collect live context from other windows (scope-filtered)
        live_context_snapshot = ParameterFormManager.collect_live_context(
            scope_filter=manager.scope_id,
            for_type=type(root_manager.object_instance)
        )
        live_context = live_context_snapshot.values if live_context_snapshot else None

        # Build unified live_values (merges live_context + current overlay)
        live_values = _build_live_values(manager, live_context, exclude_field=field_name)

        stack = build_context_stack(
            context_obj=manager.context_obj,
            object_instance=manager.object_instance,
            live_values=live_values,
        )

        with stack:
            from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
            obj_type_for_resolution = type(manager.object_instance)
            if obj_type_for_resolution:
                lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(obj_type_for_resolution)
                if lazy_type:
                    obj_type_for_resolution = lazy_type

            placeholder_text = manager.service.get_placeholder_text(field_name, obj_type_for_resolution)
            logger.info(f"        📝 Computed placeholder: {repr(placeholder_text)[:50]}")

            if placeholder_text:
                widget = manager.widgets[field_name]
                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
                logger.info(f"        ✅ Applied placeholder to widget")

                # Keep enabled-field styling in sync when placeholder changes the visual state
                if field_name == 'enabled':
                    try:
                        resolved_value = manager._widget_ops.get_value(widget)
                        manager._enabled_field_styling_service.on_enabled_field_changed(
                            manager, 'enabled', resolved_value
                        )
                    except Exception:
                        logger.exception("Failed to apply enabled styling after placeholder refresh")
            else:
                logger.warning(f"        ⚠️  No placeholder text computed")

    def refresh_with_live_context(self, manager) -> None:
        """Refresh placeholders using live values from tree registry."""
        logger.debug(f"🔍 REFRESH: {manager.field_id} (id={id(manager)}) refreshing placeholders")
        self.refresh_all_placeholders(manager)
        manager._apply_to_nested_managers(
            lambda _, nested_manager: self.refresh_with_live_context(nested_manager)
        )

    def refresh_all_placeholders(self, manager) -> None:
        """Refresh placeholder text for all widgets in a form."""
        with timer(f"_refresh_all_placeholders ({manager.field_id})", threshold_ms=5.0):
            if not manager.object_instance:
                logger.debug(f"[PLACEHOLDER] {manager.field_id}: No obj_type, skipping")
                return

            from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
            from openhcs.config_framework.context_manager import build_context_stack

            logger.debug(f"[PLACEHOLDER] {manager.field_id}: Building context stack")
            # Find root manager for scope-filtered collection
            root_manager = manager
            while root_manager._parent_manager is not None:
                root_manager = root_manager._parent_manager

            # Collect live context from other windows (scope-filtered)
            live_context_snapshot = ParameterFormManager.collect_live_context(
                scope_filter=manager.scope_id,
                for_type=type(root_manager.object_instance)
            )
            live_context = live_context_snapshot.values if live_context_snapshot else None

            # Build unified live_values (merges live_context + current overlay)
            live_values = _build_live_values(manager, live_context)

            stack = build_context_stack(
                context_obj=manager.context_obj,
                object_instance=manager.object_instance,
                live_values=live_values,
            )

            with stack:
                monitor = get_monitor("Placeholder resolution per field")
                from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
                obj_type_for_resolution = type(manager.object_instance)
                if obj_type_for_resolution:
                    lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(obj_type_for_resolution)
                    if lazy_type:
                        obj_type_for_resolution = lazy_type

                for param_name, widget in manager.widgets.items():
                    current_value = manager.parameters.get(param_name)
                    should_apply_placeholder = (current_value is None)

                    if should_apply_placeholder:
                        with monitor.measure():
                            placeholder_text = manager.service.get_placeholder_text(param_name, obj_type_for_resolution)
                            if placeholder_text:
                                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
