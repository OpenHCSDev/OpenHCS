"""
Parameter reset service with type-safe discriminated union dispatch.

Uses React-style discriminated unions for type-safe parameter handling.
Eliminates all type-checking smells by using ParameterInfo polymorphism.

Key features:
1. Type-safe dispatch using ParameterInfo discriminated unions
2. Auto-discovery of handlers via ParameterServiceABC
3. Zero boilerplate - just define handler methods
4. Consistent widget update + signal emission
5. Proper reset field tracking

Pattern:
    Instead of:
        if ParameterTypeUtils.is_optional_dataclass(param_type):
            # ... 30 lines
        elif is_dataclass(param_type):
            # ... 15 lines
        else:
            # ... 40 lines

    Use:
        service.reset_parameter(manager, param_name)
        # Auto-dispatches to correct handler based on ParameterInfo type
"""

from __future__ import annotations
from typing import Any, TYPE_CHECKING
import logging

from .parameter_service_abc import ParameterServiceABC

if TYPE_CHECKING:
    from openhcs.ui.shared.parameter_info_types import (
        OptionalDataclassInfo,
        DirectDataclassInfo,
        GenericInfo
    )

logger = logging.getLogger(__name__)


class ParameterResetService(ParameterServiceABC):
    """
    Service for resetting parameters with type-safe dispatch.

    Uses discriminated unions to eliminate type-checking smells.
    Handlers are auto-discovered based on ParameterInfo class names.
    """

    def _get_handler_prefix(self) -> str:
        """Return handler method prefix for auto-discovery."""
        return '_reset_'

    def reset_parameter(self, manager, param_name: str) -> None:
        """
        Reset parameter using type-safe dispatch.

        Gets ParameterInfo from form structure and dispatches to
        the appropriate handler based on its type.
        """
        info = manager.form_structure.get_parameter_info(param_name)
        self.dispatch(info, manager)
    

    # ========== TYPE-SAFE RESET HANDLERS ==========

    def _reset_OptionalDataclassInfo(self, info: OptionalDataclassInfo, manager) -> None:
        """
        Reset Optional[Dataclass] field - sync checkbox and reset nested manager.

        Type checker knows info is OptionalDataclassInfo!
        """
        param_name = info.name
        reset_value = self._get_reset_value(manager, param_name)

        # Update parameter dict
        manager.parameters[param_name] = reset_value

        # Update checkbox widget
        if param_name in manager.widgets:
            container = manager.widgets[param_name]

            # Find and update checkbox
            from openhcs.pyqt_gui.widgets.shared.services.widget_finder_service import WidgetFinderService
            from openhcs.pyqt_gui.widgets.shared.services.signal_blocking_service import SignalBlockingService

            checkbox = WidgetFinderService.find_optional_checkbox(manager, param_name)
            if checkbox:
                with SignalBlockingService.block_signals(checkbox):
                    checkbox.setChecked(reset_value is not None and reset_value.enabled)

            # Update group box enabled state
            try:
                group = WidgetFinderService.find_group_box(container)
                if group:
                    group.setEnabled(reset_value is not None)
            except Exception:
                pass

        # Reset nested manager contents
        nested_manager = manager.nested_managers.get(param_name)
        if nested_manager:
            nested_manager.reset_all_parameters()

        # Emit signal
        manager.parameter_changed.emit(param_name, reset_value)
    
    def _reset_DirectDataclassInfo(self, info: DirectDataclassInfo, manager) -> None:
        """
        Reset direct Dataclass field - reset nested manager only, keep instance.

        For non-optional dataclass fields, we don't replace the instance.
        Instead, we recursively reset the nested manager's contents.

        Type checker knows info is DirectDataclassInfo!
        """
        param_name = info.name

        # Reset nested manager (don't modify parameter dict)
        nested_manager = manager.nested_managers.get(param_name)
        if nested_manager:
            nested_manager.reset_all_parameters()

        # Refresh placeholder on container widget
        if param_name in manager.widgets:
            manager._apply_context_behavior(manager.widgets[param_name], None, param_name)

        # Emit signal with unchanged container value
        manager.parameter_changed.emit(param_name, manager.parameters.get(param_name))
    
    def _reset_GenericInfo(self, info: GenericInfo, manager) -> None:
        """
        Reset generic field with context-aware reset value.

        Type checker knows info is GenericInfo!
        """
        param_name = info.name
        reset_value = self._get_reset_value(manager, param_name)

        # Update parameter dict
        manager.parameters[param_name] = reset_value

        # Track reset fields for lazy behavior
        self._update_reset_tracking(manager, param_name, reset_value)

        # Update widget
        if param_name in manager.widgets:
            widget = manager.widgets[param_name]
            manager.update_widget_value(widget, reset_value, param_name)

            # Apply placeholder for None values (lazy behavior)
            if reset_value is None and not manager._in_reset:
                self._apply_placeholder_for_none(manager, param_name, widget)

        # Emit signal
        manager.parameter_changed.emit(param_name, reset_value)
    
    # ========== HELPER METHODS ==========
    
    @staticmethod
    def _get_reset_value(manager, param_name: str) -> Any:
        """
        Get reset value based on editing context.
        
        For global config editing: Use static class defaults (not None)
        For lazy config editing: Use signature defaults (None for inheritance)
        """
        # For global config editing, use static class defaults
        if manager.config.is_global_config_editing and manager.dataclass_type:
            try:
                static_default = object.__getattribute__(manager.dataclass_type, param_name)
                return static_default
            except AttributeError:
                pass
        
        # Fallback to signature default
        return manager.param_defaults.get(param_name)
    
    @staticmethod
    def _update_reset_tracking(manager, param_name: str, reset_value: Any) -> None:
        """Update reset field tracking for lazy behavior."""
        field_path = f"{manager.field_id}.{param_name}"
        
        if reset_value is None:
            # Track as reset field
            manager.reset_fields.add(param_name)
            manager.shared_reset_fields.add(field_path)
        else:
            # Remove from reset tracking
            manager.reset_fields.discard(param_name)
            manager.shared_reset_fields.discard(field_path)
    
    @staticmethod
    def _apply_placeholder_for_none(manager, param_name: str, widget) -> None:
        """Apply placeholder text for None values (lazy behavior)."""
        # Build overlay from current form state
        overlay = manager.get_current_values()
        
        # Collect live context from other windows
        live_context = manager._collect_live_context_from_other_windows() if manager._parent_manager is None else None
        
        # Build context stack and apply placeholder
        from openhcs.pyqt_gui.widgets.shared.context_layer_builders import build_context_stack
        with build_context_stack(manager, overlay, live_context=live_context):
            placeholder_text = manager.service.get_placeholder_text(param_name, manager.dataclass_type)
            if placeholder_text:
                from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer
                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
