"""
Signal connection service for ParameterFormManager initialization.

Consolidates all signal wiring logic from __init__ into a single service.
This includes:
- Parameter change → placeholder refresh
- Enabled field → styling updates
- Cross-window registration and signal wiring
- Cleanup signal connections
"""

from typing import Any


class SignalConnectionService:
    """
    Service for wiring all signals during ParameterFormManager initialization.
    
    This service handles:
    1. Parameter change signals → placeholder refresh
    2. Enabled field signals → styling updates
    3. Cross-window registration and bidirectional signal wiring
    4. Cleanup signals (destroyed → unregister)
    """
    
    @staticmethod
    def connect_all_signals(manager: Any) -> None:
        """
        Wire all signals for the manager.
        
        Args:
            manager: ParameterFormManager instance
        """
        # 1. Connect parameter changes to live placeholder updates
        # CRITICAL: Don't refresh during reset operations - reset handles placeholders itself
        # CRITICAL: Always use live context from other open windows for placeholder resolution
        # CRITICAL: Don't refresh when 'enabled' field changes - it's styling-only and doesn't affect placeholders
        manager.parameter_changed.connect(
            lambda param_name, value: manager._refresh_with_live_context()
            if not getattr(manager, '_in_reset', False) and param_name != 'enabled'
            else None
        )
        
        # 2. UNIVERSAL ENABLED FIELD BEHAVIOR: Watch for 'enabled' parameter changes and apply styling
        # This works for any form (function parameters, dataclass fields, etc.) that has an 'enabled' parameter
        # When enabled resolves to False, apply visual dimming WITHOUT blocking input
        if 'enabled' in manager.parameters:
            manager.parameter_changed.connect(manager._on_enabled_field_changed_universal)
            
            # CRITICAL: Apply initial styling based on current enabled value
            # This ensures styling is applied on window open, not just when toggled
            # Register callback to run AFTER placeholders are refreshed (not before)
            # because enabled styling needs the resolved placeholder value from the widget
            manager._on_placeholder_refresh_complete_callbacks.append(
                lambda: manager._enabled_styling_service.apply_initial_enabled_styling(manager)
            )
        
        # 3. Connect cleanup signal
        manager.destroyed.connect(manager.unregister_from_cross_window_updates)
    
    @staticmethod
    def register_cross_window_signals(manager: Any) -> None:
        """
        Register manager for cross-window updates (only root managers, not nested).
        
        This should be called by the CALLER using cross_window_registration context manager,
        NOT inside __init__. This method is kept for backward compatibility during migration.
        
        Args:
            manager: ParameterFormManager instance
        """
        # Only register root managers (not nested)
        if manager._parent_manager is not None:
            return
        
        # CRITICAL: Store initial values when window opens for cancel/revert behavior
        # When user cancels, other windows should revert to these initial values, not current edited values
        from dataclasses import is_dataclass
        if hasattr(manager.config, '_resolve_field_value'):
            manager._initial_values_on_open = manager.get_user_modified_values()
        else:
            manager._initial_values_on_open = manager.get_current_values()
        
        # Connect parameter_changed to emit cross-window context changes
        manager.parameter_changed.connect(manager._emit_cross_window_change)
        
        # Connect this instance's signal to all existing instances (bidirectional)
        for existing_manager in manager._active_form_managers:
            # Connect this instance to existing instances
            manager.context_value_changed.connect(existing_manager._on_cross_window_context_changed)
            manager.context_refreshed.connect(existing_manager._on_cross_window_context_refreshed)
            
            # Connect existing instances to this instance
            existing_manager.context_value_changed.connect(manager._on_cross_window_context_changed)
            existing_manager.context_refreshed.connect(manager._on_cross_window_context_refreshed)
        
        # Add this instance to the registry
        manager._active_form_managers.append(manager)

