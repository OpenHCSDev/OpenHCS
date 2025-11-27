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

        # Build context stack for resolution
        live_context_snapshot = ParameterFormManager.collect_live_context(
            scope_filter=manager.scope_id,
            for_type=manager.dataclass_type
        )
        live_context = live_context_snapshot.values if live_context_snapshot else None

        # Find root manager to get complete form values (enables sibling inheritance)
        # Root form (GlobalPipelineConfig/PipelineConfig/Step) contains all nested configs
        root_manager = manager
        while getattr(root_manager, '_parent_manager', None) is not None:
            root_manager = root_manager._parent_manager

        # Use root manager's values and type for context (not just this nested manager's)
        root_values = root_manager.get_user_modified_values() if root_manager != manager else None
        root_type = getattr(root_manager, 'dataclass_type', None)
        if root_values:
            value_types = {k: type(v).__name__ for k, v in root_values.items()}
            logger.info(f"        🔍 ROOT: field_id={root_manager.field_id}, type={root_type}, values={value_types}")
        if root_type:
            from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
            lazy_root_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(root_type)
            if lazy_root_type:
                root_type = lazy_root_type

        stack = build_context_stack(
            context_obj=manager.context_obj,
            overlay=manager.parameters,
            dataclass_type=manager.dataclass_type,
            live_context=live_context,
            is_global_config_editing=getattr(manager.config, 'is_global_config_editing', False),
            global_config_type=getattr(manager.config, 'global_config_type', None),
            root_form_values=root_values,
            root_form_type=root_type,
        )

        with stack:
            from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
            dataclass_type_for_resolution = manager.dataclass_type
            if dataclass_type_for_resolution:
                lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(dataclass_type_for_resolution)
                if lazy_type:
                    dataclass_type_for_resolution = lazy_type

            placeholder_text = manager.service.get_placeholder_text(field_name, dataclass_type_for_resolution)
            logger.info(f"        📝 Computed placeholder: {repr(placeholder_text)[:50]}")

            if placeholder_text:
                widget = manager.widgets[field_name]
                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
                logger.info(f"        ✅ Applied placeholder to widget")
            else:
                logger.warning(f"        ⚠️  No placeholder text computed")

    def refresh_with_live_context(self, manager, use_user_modified_only: bool = False) -> None:
        """Refresh placeholders using live values from tree registry."""
        logger.debug(f"🔍 REFRESH: {manager.field_id} (id={id(manager)}) refreshing placeholders")
        self.refresh_all_placeholders(manager, use_user_modified_only)
        manager._apply_to_nested_managers(
            lambda _, nested_manager: self.refresh_with_live_context(nested_manager, use_user_modified_only)
        )

    def refresh_all_placeholders(self, manager, use_user_modified_only: bool = False) -> None:
        """Refresh placeholder text for all widgets in a form."""
        with timer(f"_refresh_all_placeholders ({manager.field_id})", threshold_ms=5.0):
            if not manager.dataclass_type:
                logger.debug(f"[PLACEHOLDER] {manager.field_id}: No dataclass_type, skipping")
                return

            from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
            from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
            from openhcs.config_framework.context_manager import build_context_stack

            logger.debug(f"[PLACEHOLDER] {manager.field_id}: Building context stack")
            live_context_snapshot = ParameterFormManager.collect_live_context(
                scope_filter=manager.scope_id,
                for_type=manager.dataclass_type
            )
            # Extract .values dict from LiveContextSnapshot for build_context_stack
            live_context = live_context_snapshot.values if live_context_snapshot else None
            overlay = manager.get_user_modified_values() if use_user_modified_only else manager.parameters

            # Handle excluded params in overlay
            if overlay:
                overlay_dict = overlay.copy()
                for excluded_param in getattr(manager, 'exclude_params', []):
                    if excluded_param not in overlay_dict and hasattr(manager.object_instance, excluded_param):
                        overlay_dict[excluded_param] = getattr(manager.object_instance, excluded_param)
            else:
                overlay_dict = None

            # Find root manager to get complete form values (enables sibling inheritance)
            root_manager = manager
            while getattr(root_manager, '_parent_manager', None) is not None:
                root_manager = root_manager._parent_manager

            root_values = root_manager.get_user_modified_values() if root_manager != manager else None
            root_type = getattr(root_manager, 'dataclass_type', None)
            if root_type:
                from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
                lazy_root_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(root_type)
                if lazy_root_type:
                    root_type = lazy_root_type

            # Use framework-agnostic context stack building from config_framework
            stack = build_context_stack(
                context_obj=manager.context_obj,
                overlay=overlay_dict,
                dataclass_type=manager.dataclass_type,
                live_context=live_context,
                is_global_config_editing=getattr(manager.config, 'is_global_config_editing', False),
                global_config_type=getattr(manager.config, 'global_config_type', None),
                root_form_values=root_values,
                root_form_type=root_type,
            )

            with stack:
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
