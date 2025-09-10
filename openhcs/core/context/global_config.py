"""
Global configuration context management for OpenHCS.

Simplified thread-local storage for non-UI usage. UI components use explicit context providers.
"""

import threading
from typing import Dict, Type, Optional, Any


# Simplified thread-local storage for non-UI usage
_global_config_contexts: Dict[Type, threading.local] = {}


def set_current_global_config(config_type: Type, config_instance: Any) -> None:
    """Set current global config for any dataclass type.

    Args:
        config_type: The config type to set
        config_instance: The config instance to set
    """
    # Set thread-local context
    if config_type not in _global_config_contexts:
        _global_config_contexts[config_type] = threading.local()
    _global_config_contexts[config_type].value = config_instance

    # DEBUG: Track thread-local context changes with stack trace
    if hasattr(config_instance, 'step_well_filter_config'):
        step_config = getattr(config_instance, 'step_well_filter_config')
        if hasattr(step_config, 'well_filter'):
            well_filter_value = getattr(step_config, 'well_filter')
            print(f"🔍 THREAD-LOCAL SET: {config_type.__name__} with step_well_filter_config.well_filter = {well_filter_value}")

            # Show stack trace for corruption cases
            if well_filter_value == 1:
                import traceback
                print("🔍 CORRUPTION STACK TRACE:")
                stack_lines = traceback.format_stack(limit=10)
                for line in stack_lines[-5:]:  # Show last 5 stack frames
                    print(f"🔍   {line.strip()}")

    # CRITICAL FIX: No longer emit global context change events during set_current_global_config
    # Context change events are now handled by orchestrator-specific coordinators via parameter_changed signals
    # This prevents cross-orchestrator contamination while maintaining live updates within the same orchestrator
    pass


def get_current_global_config(config_type: Type) -> Optional[Any]:
    """Get current global config for any dataclass type.

    Args:
        config_type: The config type to retrieve

    Returns:
        Current config instance or None
    """
    context = _global_config_contexts.get(config_type)
    return getattr(context, 'value', None) if context else None