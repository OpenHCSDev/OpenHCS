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
from contextlib import ExitStack
import dataclasses
from dataclasses import is_dataclass
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
        """Reset direct Dataclass field - reset nested manager only."""
        param_name = info.name
        nested_manager = manager.nested_managers.get(param_name)
        if nested_manager:
            nested_manager.reset_all_parameters()

        if param_name in manager.widgets:
            manager._widget_service.update_widget_value(
                manager.widgets[param_name],
                manager.parameters.get(param_name),
                param_name,
                skip_context_behavior=False,
                manager=manager
            )

    def _reset_GenericInfo(self, info: GenericInfo, manager) -> None:
        """Reset generic field with context-aware reset value."""
        param_name = info.name
        reset_value = self._get_reset_value(manager, param_name)
        manager.parameters[param_name] = reset_value
        self._update_reset_tracking(manager, param_name, reset_value)

        if param_name in manager.widgets:
            widget = manager.widgets[param_name]
            manager._widget_service.update_widget_value(
                widget, reset_value, param_name, skip_context_behavior=True, manager=manager
            )

    @staticmethod
    def _get_reset_value(manager, param_name: str) -> Any:
        """Get reset value based on editing context."""
        if manager.config.is_global_config_editing and manager.dataclass_type:
            try:
                return object.__getattribute__(manager.dataclass_type, param_name)
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

    def refresh_with_live_context(self, manager, use_user_modified_only: bool = False) -> None:
        """Refresh placeholders using live values from tree registry."""
        logger.debug(f"🔍 REFRESH: {manager.field_id} (id={id(manager)}) refreshing placeholders")
        self.refresh_all_placeholders(manager, use_user_modified_only)
        manager._apply_to_nested_managers(
            lambda name, nested_manager: self.refresh_with_live_context(nested_manager, use_user_modified_only)
        )

    def refresh_all_placeholders(self, manager, use_user_modified_only: bool = False) -> None:
        """Refresh placeholder text for all widgets in a form."""
        with timer(f"_refresh_all_placeholders ({manager.field_id})", threshold_ms=5.0):
            if not manager.dataclass_type:
                logger.debug(f"[PLACEHOLDER] {manager.field_id}: No dataclass_type, skipping")
                return

            from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
            from openhcs.config_framework.context_manager import config_context

            logger.debug(f"[PLACEHOLDER] {manager.field_id}: Building context stack")
            live_context = ParameterFormManager.collect_live_context(scope_filter=manager.scope_id)
            overlay = manager.get_user_modified_values() if use_user_modified_only else manager.parameters

            with ExitStack() as stack:
                if manager.context_obj is not None:
                    stack.enter_context(config_context(manager.context_obj))

                if manager.dataclass_type and overlay:
                    try:
                        if is_dataclass(manager.dataclass_type):
                            overlay_dict = overlay.copy()
                            for excluded_param in getattr(manager, 'exclude_params', []):
                                if excluded_param not in overlay_dict and hasattr(manager.object_instance, excluded_param):
                                    overlay_dict[excluded_param] = getattr(manager.object_instance, excluded_param)
                            overlay_instance = manager.dataclass_type(**overlay_dict)
                            stack.enter_context(config_context(overlay_instance))
                    except Exception:
                        pass

                monitor = get_monitor("Placeholder resolution per field")
                from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
                dataclass_type_for_resolution = manager.dataclass_type
                if dataclass_type_for_resolution:
                    lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(dataclass_type_for_resolution)
                    if lazy_type:
                        dataclass_type_for_resolution = lazy_type

                for param_name, widget in manager.widgets.items():
                    current_value = manager.parameters.get(param_name)
                    should_apply_placeholder = (current_value is None)

                    if should_apply_placeholder:
                        with monitor.measure():
                            placeholder_text = manager.service.get_placeholder_text(param_name, dataclass_type_for_resolution)
                            if placeholder_text:
                                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)

