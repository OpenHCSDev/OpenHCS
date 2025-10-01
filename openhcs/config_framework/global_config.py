"""
Generic global configuration context management.

Provides thread-local storage for global configuration state.
This is used as the base context for all lazy configuration resolution.
"""

import threading
from typing import Dict, Type, Optional, Any


# Simplified thread-local storage for non-UI usage
_global_config_contexts: Dict[Type, threading.local] = {}


def set_current_global_config(config_type: Type, config_instance: Any, *, caller_context: str = None) -> None:
    """Set current global config for any dataclass type.

    RESTRICTED USE: This should ONLY be called when actually editing the global config,
    not for temporary context switching or orchestrator-specific operations.

    Args:
        config_type: The config type to set
        config_instance: The config instance to set
        caller_context: Optional context description for debugging inappropriate usage
    """
    import inspect

    # Get caller information for debugging inappropriate usage
    frame = inspect.currentframe().f_back
    caller_file = frame.f_code.co_filename
    caller_function = frame.f_code.co_name
    caller_line = frame.f_lineno

    # Set thread-local context
    if config_type not in _global_config_contexts:
        _global_config_contexts[config_type] = threading.local()
    _global_config_contexts[config_type].value = config_instance


def set_global_config_for_editing(config_type: Type, config_instance: Any) -> None:
    """Set global config specifically for editing scenarios.

    This is the ONLY function that should be used for legitimate global config modifications.
    Use this when:
    - User is editing global configuration through UI
    - Application startup is loading cached global config
    - Tests are setting up global config state
    """
    set_current_global_config(config_type, config_instance, caller_context="LEGITIMATE_GLOBAL_CONFIG_EDITING")


def get_current_global_config(config_type: Type) -> Optional[Any]:
    """Get current global config for any dataclass type.

    Args:
        config_type: The config type to retrieve

    Returns:
        Current config instance or None
    """
    context = _global_config_contexts.get(config_type)
    return getattr(context, 'value', None) if context else None