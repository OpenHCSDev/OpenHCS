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
from functools import wraps

from .parameter_service_abc import ParameterServiceABC

# Optional performance monitoring - stub if not available
try:
    from pyqt_formgen.core.performance_monitor import timer, get_monitor
except ImportError:
    def timer(name):
        """No-op timer decorator when performance_monitor not available."""
        def decorator(func):
            @wraps(func)
            def wrapper(*args, **kwargs):
                return func(*args, **kwargs)
            return wrapper
        return decorator

    def get_monitor():
        """No-op monitor when performance_monitor not available."""
        return None

if TYPE_CHECKING:
    from pyqt_formgen.forms import (
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
        from pyqt_formgen.forms import WidgetOperations
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
        # CRITICAL: Compute full dotted path for nested PFMs
        dotted_path = f'{manager.field_prefix}.{param_name}' if manager.field_prefix else param_name
        # MODEL mutation through ObjectState (handles tracking)
        manager.state.reset_parameter(dotted_path)
        reset_value = manager.state.parameters.get(dotted_path)

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

        MODEL mutation through ObjectState, then VIEW-only widget updates.
        """
        param_name = info.name
        # CRITICAL: Compute full dotted path for nested PFMs
        dotted_path = f'{manager.field_prefix}.{param_name}' if manager.field_prefix else param_name
        # MODEL mutation through ObjectState (handles tracking, cache invalidation)
        manager.state.reset_parameter(dotted_path)
        reset_value = manager.state.parameters.get(dotted_path)

        # Invalidate cache token BEFORE refreshing placeholder
        from objectstate import ObjectStateRegistry
        ObjectStateRegistry.increment_token()

        # VIEW-only: Update widget
        if param_name in manager.widgets:
            widget = manager.widgets[param_name]
            from .signal_service import SignalService
            with SignalService.block_signals(widget):
                manager._widget_service.update_widget_value(
                    widget, reset_value, param_name, skip_context_behavior=False, manager=manager
                )
            # Refresh placeholder if value is None
            if reset_value is None:
                self.refresh_single_placeholder(manager, param_name)

    # DELETED: _get_reset_value - ObjectState owns defaults
    # DELETED: _update_reset_tracking - ObjectState.reset_parameter handles tracking

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
        logger.debug(f"🔬 RESET_TRACE: refresh_single_placeholder: {manager.field_id}.{field_name}")

        # Check if field exists in this manager's widgets
        if field_name not in manager.widgets:
            logger.debug(f"🔬 RESET_TRACE: {field_name} not in widgets, skipping")
            return

        # Compute full dotted path for nested PFMs
        full_path = f"{manager.field_prefix}.{field_name}" if manager.field_prefix else field_name

        # Only refresh if value is None (needs placeholder)
        # Use manager.parameters (scoped) not state.parameters (full paths)
        current_value = manager.parameters.get(field_name)
        logger.debug(f"🔬 RESET_TRACE: current_value={repr(current_value)[:50]}")
        if current_value is not None:
            logger.debug(f"🔬 RESET_TRACE: value is not None, no placeholder needed")
            return

        logger.debug(f"🔬 RESET_TRACE: value is None, calling get_resolved_value...")

        from pyqt_formgen.forms.widget_strategies import PyQt6WidgetEnhancer
        from objectstate import LazyDefaultPlaceholderService

        # Get raw resolved value from ObjectState (handles context building internally)
        # Use full_path for nested PFMs
        resolved_value = manager.state.get_resolved_value(full_path)
        logger.debug(f"🔬 RESET_TRACE: resolved_value={repr(resolved_value)[:50]}")

        # Format for display (VIEW responsibility)
        placeholder_text = LazyDefaultPlaceholderService._format_placeholder_text(
            resolved_value, manager.config.placeholder_prefix
        )
        logger.debug(f"        📝 Formatted placeholder: {repr(placeholder_text)[:50]}")

        if placeholder_text:
            widget = manager.widgets[field_name]
            PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
            logger.debug(f"        ✅ Applied placeholder to widget")

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

            from pyqt_formgen.forms.widget_strategies import PyQt6WidgetEnhancer
            from objectstate import LazyDefaultPlaceholderService

            logger.debug(f"[PLACEHOLDER] {manager.field_id}: Refreshing placeholders via ObjectState")

            monitor = get_monitor("Placeholder resolution per field")

            for param_name, widget in manager.widgets.items():
                # Guard: Skip deleted widgets (can happen if window closed during async build)
                try:
                    # Access any attribute to check if widget is still valid
                    _ = widget.objectName()
                except RuntimeError:
                    logger.debug(f"[PLACEHOLDER] {manager.field_id}: Widget {param_name} was deleted, skipping")
                    continue

                # Use manager.parameters (scoped) not state.parameters (full paths)
                current_value = manager.parameters.get(param_name)
                should_apply_placeholder = (current_value is None)

                if should_apply_placeholder:
                    with monitor.measure():
                        # Compute full dotted path for nested PFMs
                        full_path = f"{manager.field_prefix}.{param_name}" if manager.field_prefix else param_name
                        # Get raw resolved value from ObjectState using full path
                        resolved_value = manager.state.get_resolved_value(full_path)
                        # Format for display (VIEW responsibility)
                        placeholder_text = LazyDefaultPlaceholderService._format_placeholder_text(
                            resolved_value, manager.config.placeholder_prefix
                        )
                        if placeholder_text:
                            PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
