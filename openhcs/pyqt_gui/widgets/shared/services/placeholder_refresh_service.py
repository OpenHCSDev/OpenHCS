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

    def __init__(self, widget_ops):
        """
        Initialize placeholder refresh service.

        Args:
            widget_ops: WidgetOperations for placeholder operations
        """
        self.widget_ops = widget_ops
    
    def refresh_with_live_context(self, manager, live_context: Optional[dict] = None) -> None:
        """
        Refresh placeholders with live context from other windows.
        
        Args:
            manager: ParameterFormManager instance
            live_context: Optional pre-collected live context. If None, will collect it.
        """
        logger.info(f"🔍 REFRESH: {manager.field_id} (id={id(manager)}) refreshing with live context")
        
        # Only root managers should collect live context (nested managers inherit from parent)
        if live_context is None and manager._parent_manager is None:
            live_context = self.collect_live_context_from_other_windows(manager)
        
        # Refresh this form's placeholders
        self.refresh_all_placeholders(manager, live_context)
        
        # Refresh all nested managers' placeholders
        manager._apply_to_nested_managers(
            lambda name, nested_manager: self.refresh_all_placeholders(nested_manager, live_context)
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
                return

            # Use self.parameters for overlay (has correct None values)
            overlay = manager.parameters

            # Build context stack with live context
            from openhcs.pyqt_gui.widgets.shared.context_layer_builders import build_context_stack
            with build_context_stack(manager, overlay, live_context=live_context):
                monitor = get_monitor("Placeholder resolution per field")
                for param_name, widget in manager.widgets.items():
                    # Check current value from parameters
                    current_value = manager.parameters.get(param_name)
                    
                    # Check if widget is in placeholder state
                    widget_in_placeholder_state = widget.property("is_placeholder_state")
                    
                    if current_value is None or widget_in_placeholder_state:
                        with monitor.measure():
                            placeholder_text = manager.service.get_placeholder_text(param_name, manager.dataclass_type)
                            if placeholder_text:
                                self.widget_ops.try_set_placeholder(widget, placeholder_text)
    
    def collect_live_context_from_other_windows(self, manager) -> dict:
        """
        Collect live values from other open form managers for context resolution.
        
        Returns a dict mapping object types to their current live values.
        This allows matching by type rather than instance identity.
        
        CRITICAL: Only collects context from PARENT types in the hierarchy, not from the same type.
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
        my_type = type(manager.object_instance)
        
        logger.info(f"🔍 COLLECT_CONTEXT: {manager.field_id} (id={id(manager)}) collecting from {len(manager._active_form_managers)} managers")
        
        for other_manager in manager._active_form_managers:
            if other_manager is not manager:
                # Only collect from managers in the same scope OR from global scope (None)
                if other_manager.scope_id is not None and manager.scope_id is not None and other_manager.scope_id != manager.scope_id:
                    continue  # Different orchestrator - skip
                
                logger.info(f"🔍 COLLECT_CONTEXT: Calling get_user_modified_values() on {other_manager.field_id} (id={id(other_manager)})")
                
                # Get only user-modified (concrete, non-None) values
                live_values = other_manager.get_user_modified_values()
                obj_type = type(other_manager.object_instance)
                
                # Only skip if this is EXACTLY the same type as us
                if obj_type == my_type:
                    continue
                
                # Map by the actual type
                live_context[obj_type] = live_values
                
                # Also map by the base/lazy equivalent type for flexible matching
                base_type = get_base_type_for_lazy(obj_type)
                if base_type and base_type != obj_type:
                    live_context[base_type] = live_values
                
                lazy_type = LazyDefaultPlaceholderService._get_lazy_type_for_base(obj_type)
                if lazy_type and lazy_type != obj_type:
                    live_context[lazy_type] = live_values
        
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

