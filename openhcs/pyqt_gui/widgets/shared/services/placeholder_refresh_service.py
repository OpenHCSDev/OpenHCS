"""
Placeholder Refresh Service - Placeholder resolution and live context management.

Extracts all placeholder refresh logic from ParameterFormManager.
Handles live context collection, placeholder resolution, and cross-window updates.
"""

from typing import Any, Dict, Optional, Type
import dataclasses
from dataclasses import is_dataclass
import logging

from openhcs.utils.performance_monitor import timer, get_monitor

logger = logging.getLogger(__name__)


class PlaceholderRefreshService:
    """
    Service for refreshing placeholders with live context from other windows.

    Stateless service that encapsulates all placeholder refresh operations.
    """

    def __init__(self):
        """Initialize placeholder refresh service (stateless - no dependencies)."""
        from openhcs.ui.shared.widget_operations import WidgetOperations

        self.widget_ops = WidgetOperations
    
    def refresh_with_live_context(self, manager, use_user_modified_only: bool = False) -> None:
        """
        Refresh placeholders using live values from _active_form_managers.

        Context layer builders query _active_form_managers directly to get live values
        from other open windows, eliminating the need for a live_context dict.

        Args:
            manager: ParameterFormManager instance
            use_user_modified_only: If True, builders query only user-modified values (for reset behavior).
                                     If False, builders query all current values (for normal refresh behavior).
        """
        logger.info(f"🔍 REFRESH: {manager.field_id} (id={id(manager)}) refreshing placeholders")

        # Refresh this form's placeholders (builders query _active_form_managers internally)
        self.refresh_all_placeholders(manager, use_user_modified_only)

        # Refresh all nested managers' placeholders
        manager._apply_to_nested_managers(
            lambda name, nested_manager: self.refresh_with_live_context(nested_manager, use_user_modified_only)
        )
    
    def refresh_all_placeholders(self, manager, use_user_modified_only: bool = False) -> None:
        """
        Refresh placeholder text for all widgets in a form.

        Builders query _active_form_managers directly to get live values from other windows.

        Args:
            manager: ParameterFormManager instance
            use_user_modified_only: If True, builders query only user-modified values (for reset behavior).
                                     If False, builders query all current values (for normal refresh behavior).
        """
        with timer(f"_refresh_all_placeholders ({manager.field_id})", threshold_ms=5.0):
            if not manager.dataclass_type:
                logger.debug(f"[PLACEHOLDER] {manager.field_id}: No dataclass_type, skipping")
                return

            # CRITICAL: Use get_user_modified_values() for overlay to ensure only explicitly
            # user-modified values override sibling/parent values. Using manager.parameters
            # would include inherited values, which would incorrectly override sibling values.
            overlay = manager.get_user_modified_values()

            # Build context stack (builders query _active_form_managers internally)
            from openhcs.pyqt_gui.widgets.shared.context_layer_builders import build_context_stack
            from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer

            logger.info(f"[PLACEHOLDER] {manager.field_id}: Building context stack (use_user_modified_only={use_user_modified_only})")

            with build_context_stack(manager, overlay, use_user_modified_only=use_user_modified_only):
                monitor = get_monitor("Placeholder resolution per field")

                # CRITICAL: Use lazy version of dataclass type for placeholder resolution
                # This ensures lazy field resolution works correctly within the context stack
                from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
                dataclass_type_for_resolution = manager.dataclass_type
                if dataclass_type_for_resolution:
                    lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(dataclass_type_for_resolution)
                    if lazy_type:
                        logger.debug(f"[PLACEHOLDER] {manager.field_id}: Using lazy type {lazy_type.__name__}")
                        dataclass_type_for_resolution = lazy_type

                logger.debug(f"[PLACEHOLDER] {manager.field_id}: Processing {len(manager.widgets)} widgets")
                for param_name, widget in manager.widgets.items():
                    # Check current value from parameters
                    current_value = manager.parameters.get(param_name)

                    # Check if widget is in placeholder state
                    widget_in_placeholder_state = widget.property("is_placeholder_state")

                    # CRITICAL: Only apply placeholder text if widget is actually showing a placeholder
                    # (i.e., current_value is None OR widget is already in placeholder state)
                    # Do NOT apply placeholder text to widgets with actual user-entered values
                    should_apply_placeholder = (current_value is None or widget_in_placeholder_state)

                    logger.debug(f"[PLACEHOLDER] {manager.field_id}.{param_name}: value={current_value}, in_placeholder_state={widget_in_placeholder_state}, should_apply={should_apply_placeholder}, widget_type={type(widget).__name__}")

                    if should_apply_placeholder:
                        with monitor.measure():
                            placeholder_text = manager.service.get_placeholder_text(param_name, dataclass_type_for_resolution)
                            logger.info(f"[PLACEHOLDER] {manager.field_id}.{param_name}: resolved text='{placeholder_text}'")
                            if placeholder_text:
                                # Use PyQt6WidgetEnhancer directly for PyQt6 widgets
                                PyQt6WidgetEnhancer.apply_placeholder_text(widget, placeholder_text)
                                logger.debug(f"[PLACEHOLDER] {manager.field_id}.{param_name}: Applied placeholder to {type(widget).__name__}")

