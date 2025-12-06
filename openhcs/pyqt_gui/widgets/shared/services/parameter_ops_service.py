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

    @staticmethod
    def _get_effective_context_obj(manager):
        """
        Get the context object to use when building the context stack.

        Falls back to the parent manager's object_instance when this manager
        has no explicit context_obj so nested configs still see their parent
        layer for sibling inheritance.
        """
        if manager.context_obj is not None:
            return manager.context_obj

        parent = manager._parent_manager
        if parent is not None:
            return parent.object_instance

        return None

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
        logger.info(f"🔬 RESET_TRACE: _reset_GenericInfo: {manager.field_id}.{param_name}")
        logger.info(f"🔬 RESET_TRACE: reset_value={repr(reset_value)[:50]}")

        # Update parameters and tracking
        old_value = manager.parameters.get(param_name)
        logger.info(f"🔬 RESET_TRACE: old_value={repr(old_value)[:50]}")
        manager.parameters[param_name] = reset_value
        logger.info(f"🔬 RESET_TRACE: Set parameters[{param_name}] = {repr(reset_value)[:50]}")

        logger.info(f"🔬 RESET_TRACE: BEFORE _update_reset_tracking: _user_set_fields={manager._user_set_fields}")
        self._update_reset_tracking(manager, param_name, reset_value)
        logger.info(f"🔬 RESET_TRACE: AFTER _update_reset_tracking: _user_set_fields={manager._user_set_fields}")

        # CRITICAL: Invalidate cache token BEFORE refreshing placeholder
        # Otherwise refresh_single_placeholder will use stale cached values
        from openhcs.pyqt_gui.widgets.shared.services.live_context_service import LiveContextService
        old_token = LiveContextService.get_token()
        LiveContextService.increment_token()
        new_token = LiveContextService.get_token()
        logger.info(f"🔬 RESET_TRACE: Incremented token: {old_token} -> {new_token}")

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
                logger.info(f"🔬 RESET_TRACE: Calling refresh_single_placeholder for {param_name}")
                self.refresh_single_placeholder(manager, param_name)
                logger.info(f"🔬 RESET_TRACE: Done refresh_single_placeholder")

            logger.info(f"🔬 RESET_TRACE: _reset_GenericInfo complete")

    @staticmethod
    def _get_reset_value(manager, param_name: str) -> Any:
        """Get reset value from param_defaults (signature defaults)."""
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

        Uses ObjectState.get_resolved_value() for resolution, then formats for display.

        Args:
            manager: The manager containing the field
            field_name: Name of the field to refresh
        """
        logger.info(f"🔬 RESET_TRACE: refresh_single_placeholder: {manager.field_id}.{field_name}")

        # Check if field exists in this manager's widgets
        if field_name not in manager.widgets:
            logger.warning(f"🔬 RESET_TRACE: {field_name} not in widgets, skipping")
            return

        # Only refresh if value is None (needs placeholder)
        current_value = manager.state.parameters.get(field_name)
        logger.info(f"🔬 RESET_TRACE: current_value={repr(current_value)[:50]}")
        if current_value is not None:
            logger.info(f"🔬 RESET_TRACE: value is not None, no placeholder needed")
            return

        logger.info(f"🔬 RESET_TRACE: value is None, calling get_resolved_value...")
        logger.info(f"🔬 RESET_TRACE: _user_set_fields BEFORE resolution={manager._user_set_fields}")

        from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

        # Get raw resolved value from ObjectState (handles context building internally)
        resolved_value = manager.state.get_resolved_value(field_name)
        logger.info(f"🔬 RESET_TRACE: resolved_value={repr(resolved_value)[:50]}")

        # Format for display (VIEW responsibility)
        placeholder_text = LazyDefaultPlaceholderService._format_placeholder_text(
            resolved_value, manager.config.placeholder_prefix
        )
        logger.info(f"        📝 Formatted placeholder: {repr(placeholder_text)[:50]}")

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
        """Refresh placeholder text for all widgets in a form.

        Uses ObjectState.get_resolved_value() for resolution, then formats for display.
        """
        with timer(f"_refresh_all_placeholders ({manager.field_id})", threshold_ms=5.0):
            if not manager.object_instance:
                logger.debug(f"[PLACEHOLDER] {manager.field_id}: No obj_type, skipping")
                return

            from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
            from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService

            logger.debug(f"[PLACEHOLDER] {manager.field_id}: Refreshing placeholders via ObjectState")

            monitor = get_monitor("Placeholder resolution per field")

            for param_name, widget in manager.widgets.items():
                current_value = manager.state.parameters.get(param_name)
                should_apply_placeholder = (current_value is None)

                if should_apply_placeholder:
                    with monitor.measure():
                        # Get raw resolved value from ObjectState
                        resolved_value = manager.state.get_resolved_value(param_name)
                        # Format for display (VIEW responsibility)
                        placeholder_text = LazyDefaultPlaceholderService._format_placeholder_text(
                            resolved_value, manager.config.placeholder_prefix
                        )
                        if placeholder_text:
                            PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
