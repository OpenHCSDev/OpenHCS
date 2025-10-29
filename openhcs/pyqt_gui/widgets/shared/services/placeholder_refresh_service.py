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
    
    def refresh_with_live_context(self, manager, live_context: Optional[dict] = None, use_user_modified_only: bool = False) -> None:
        """
        Refresh placeholders with live context from other windows AND current form values.

        CRITICAL: Live context includes:
        1. Values from OTHER windows (cross-window updates)
        2. Current form values (for nested config inheritance within same window)
        3. Sibling nested manager values (for sibling inheritance within same parent)

        This enables nested configs to see parent's current values AND sibling values in real-time.

        Args:
            manager: ParameterFormManager instance
            live_context: Optional pre-collected live context. If None, will collect it.
            use_user_modified_only: If True, only include user-modified values in overlay (for reset behavior).
                                     If False, include all current values (for normal refresh behavior).
        """
        logger.info(f"🔍 REFRESH: {manager.field_id} (id={id(manager)}) refreshing with live context")

        # Only root managers should collect live context (nested managers inherit from parent)
        if live_context is None and manager._parent_manager is None:
            live_context = self.collect_live_context_from_other_windows(manager)
        else:
            live_context = live_context or {}

        # CRITICAL: Add current form's values to live context
        # This allows nested configs to see parent's current values in real-time
        # even when there's only one window open
        # For reset behavior: use get_user_modified_values() so reset fields don't override sibling values
        # For normal refresh: use get_current_values() so edited fields propagate to other fields
        current_values = manager.get_user_modified_values() if use_user_modified_only else manager.get_current_values()
        if current_values:
            obj_type = type(manager.object_instance)
            live_context[obj_type] = current_values
            logger.info(f"🔍 REFRESH: Added current form values to live context for {obj_type.__name__}: {list(current_values.keys())}")

        # CRITICAL: For nested managers, also collect values from sibling nested managers
        # This enables sibling inheritance (e.g., path_planning_config inheriting from well_filter_config)
        if manager._parent_manager is not None:
            logger.info(f"🔍 REFRESH: {manager.field_id} is nested, collecting sibling values")
            for sibling_name, sibling_manager in manager._parent_manager.nested_managers.items():
                # Skip self
                if sibling_manager is manager:
                    continue

                sibling_values = sibling_manager.get_current_values()
                if sibling_values:
                    sibling_type = type(sibling_manager.object_instance)
                    live_context[sibling_type] = sibling_values
                    logger.info(f"🔍 REFRESH: Added sibling {sibling_name} values to live context for {sibling_type.__name__}: {sibling_values}")

        # Refresh this form's placeholders
        self.refresh_all_placeholders(manager, live_context)

        # Refresh all nested managers' placeholders
        # CRITICAL: Use refresh_with_live_context so each nested manager can collect sibling values
        manager._apply_to_nested_managers(
            lambda name, nested_manager: self.refresh_with_live_context(nested_manager, live_context)
        )
    
    def refresh_all_placeholders(self, manager, live_context: Optional[dict] = None) -> None:
        """
        Refresh placeholder text for all widgets in a form.

        Args:
            manager: ParameterFormManager instance
            live_context: Optional dict mapping object instances to their live values from other open windows
        """
        with timer(f"_refresh_all_placeholders ({manager.field_id})", threshold_ms=5.0):
            if not manager.dataclass_type:
                logger.debug(f"[PLACEHOLDER] {manager.field_id}: No dataclass_type, skipping")
                return

            # CRITICAL: Use get_user_modified_values() for overlay to ensure only explicitly
            # user-modified values override sibling/parent values. Using manager.parameters
            # would include inherited values, which would incorrectly override sibling values.
            overlay = manager.get_user_modified_values()

            # Build context stack with live context
            from openhcs.pyqt_gui.widgets.shared.context_layer_builders import build_context_stack
            from openhcs.pyqt_gui.widgets.shared.widget_strategies import PyQt6WidgetEnhancer

            logger.info(f"[PLACEHOLDER] {manager.field_id}: Building context stack with live_context={live_context is not None}")
            if live_context:
                logger.info(f"[PLACEHOLDER] {manager.field_id}: Live context types: {list(live_context.keys())}")

            with build_context_stack(manager, overlay, live_context=live_context):
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
    
    def collect_live_context_from_other_windows(self, manager) -> dict:
        """
        Collect live values from other open form managers for context resolution.

        Returns a dict mapping object types to their current live values.
        This allows matching by type rather than instance identity.

        CRITICAL: Collects from ALL other managers (different instances), including same type.
        CRITICAL: Uses get_user_modified_values() to only collect concrete (non-None) values.
        CRITICAL: Only collects from managers with the SAME scope_id (same orchestrator/plate).

        Args:
            manager: ParameterFormManager instance

        Returns:
            Dict mapping types to their live values
        """
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy

        live_context = {}

        logger.info(f"🔍 COLLECT_CONTEXT: {manager.field_id} (id={id(manager)}) collecting from {len(manager._active_form_managers)} managers")

        for other_manager in manager._active_form_managers:
            # Skip only if it's the SAME INSTANCE (same manager)
            if other_manager is manager:
                logger.info(f"🔍 COLLECT_CONTEXT: Skipping self {other_manager.field_id}")
                continue

            # Only collect from managers in the same scope OR from global scope (None)
            if other_manager.scope_id is not None and manager.scope_id is not None and other_manager.scope_id != manager.scope_id:
                logger.info(f"🔍 COLLECT_CONTEXT: Skipping different scope {other_manager.field_id} (scope {other_manager.scope_id} != {manager.scope_id})")
                continue  # Different orchestrator - skip

            logger.info(f"🔍 COLLECT_CONTEXT: Collecting from {other_manager.field_id} (id={id(other_manager)})")

            # Get only user-modified (concrete, non-None) values
            live_values = other_manager.get_user_modified_values()
            obj_type = type(other_manager.object_instance)

            logger.info(f"🔍 COLLECT_CONTEXT: Got {len(live_values)} live values from {obj_type.__name__}: {list(live_values.keys())}")

            # Map by the actual type (including same type from other windows)
            live_context[obj_type] = live_values

            # Also map by the base/lazy equivalent type for flexible matching
            base_type = get_base_type_for_lazy(obj_type)
            if base_type and base_type != obj_type:
                live_context[base_type] = live_values
                logger.info(f"🔍 COLLECT_CONTEXT: Also mapped base type {base_type.__name__}")

            lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(obj_type)
            if lazy_type and lazy_type != obj_type:
                live_context[lazy_type] = live_values
                logger.info(f"🔍 COLLECT_CONTEXT: Also mapped lazy type {lazy_type.__name__}")

        logger.info(f"🔍 COLLECT_CONTEXT: Final live_context has {len(live_context)} type mappings")
        return live_context
    
    def find_live_values_for_type(self, ctx_type: Type, live_context: dict) -> Optional[dict]:
        """
        Find live values for a context type, checking both exact type and lazy/base equivalents.
        
        Args:
            ctx_type: The type to find live values for
            live_context: Dict mapping types to their live values
        
        Returns:
            Live values dict if found, None otherwise
        """
        if not live_context:
            return None
        
        # Check exact type match first
        if ctx_type in live_context:
            return live_context[ctx_type]
        
        # Check lazy/base equivalents
        from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService
        from openhcs.config_framework.lazy_factory import get_base_type_for_lazy
        
        # If ctx_type is lazy, check its base type
        base_type = get_base_type_for_lazy(ctx_type)
        if base_type and base_type in live_context:
            return live_context[base_type]
        
        # If ctx_type is base, check its lazy type
        lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(ctx_type)
        if lazy_type and lazy_type in live_context:
            return live_context[lazy_type]
        
        return None
    
    def reconstruct_nested_dataclasses(self, live_values: dict, base_instance=None) -> dict:
        """
        Reconstruct nested dataclasses from tuple format (type, dict) to instances.
        
        get_user_modified_values() returns nested dataclasses as (type, dict) tuples
        to preserve only user-modified fields. This function reconstructs them as instances
        by merging the user-modified fields into the base instance's nested dataclasses.
        
        Args:
            live_values: Dict with values, may contain (type, dict) tuples for nested dataclasses
            base_instance: Base dataclass instance to merge into (for nested dataclass fields)
        
        Returns:
            Dict with nested dataclasses reconstructed as instances
        """
        reconstructed = {}
        for field_name, value in live_values.items():
            if isinstance(value, tuple) and len(value) == 2:
                # Nested dataclass in tuple format: (type, dict)
                dataclass_type, field_dict = value
                
                # If we have a base instance, merge into its nested dataclass
                if base_instance and hasattr(base_instance, field_name):
                    base_nested = getattr(base_instance, field_name)
                    if base_nested is not None and is_dataclass(base_nested):
                        # Merge user-modified fields into base nested dataclass
                        reconstructed[field_name] = dataclasses.replace(base_nested, **field_dict)
                    else:
                        # No base nested dataclass, create fresh instance
                        reconstructed[field_name] = dataclass_type(**field_dict)
                else:
                    # No base instance, create fresh instance
                    reconstructed[field_name] = dataclass_type(**field_dict)
            else:
                # Regular value, pass through
                reconstructed[field_name] = value
        return reconstructed

