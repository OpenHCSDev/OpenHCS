"""
Global configuration context management for OpenHCS.

Provides thread-local storage and context management for global configuration objects.
"""

import threading
from typing import Dict, Type, Optional, Any
import functools


# Generic thread-local storage for any global config type
_global_config_contexts: Dict[Type, threading.local] = {}

# Per-window context storage to prevent contamination between config windows
_window_contexts: Dict[str, Dict[Type, Any]] = {}


def set_current_global_config(config_type: Type, config_instance: Any, window_id: Optional[str] = None) -> None:
    """Set current global config for any dataclass type.

    Args:
        config_type: The config type to set
        config_instance: The config instance to set
        window_id: Optional window ID for isolated context (prevents cross-window contamination)
    """
    # Set window-specific context if window_id provided (prevents contamination)
    if window_id:
        if window_id not in _window_contexts:
            _window_contexts[window_id] = {}
        _window_contexts[window_id][config_type] = config_instance
        return

    # Fallback to thread-local context
    if config_type not in _global_config_contexts:
        _global_config_contexts[config_type] = threading.local()
    _global_config_contexts[config_type].value = config_instance


def get_current_global_config(config_type: Type, window_id: Optional[str] = None) -> Optional[Any]:
    """Get current global config for any dataclass type.

    Args:
        config_type: The config type to retrieve
        window_id: Optional window ID for isolated context (prevents cross-window contamination)
    """
    # Check window-specific context first (prevents contamination)
    if window_id and window_id in _window_contexts:
        window_context = _window_contexts[window_id]
        if config_type in window_context:
            return window_context[config_type]

    # Fallback to thread-local context
    context = _global_config_contexts.get(config_type)
    return getattr(context, 'value', None) if context else None


def clear_window_context(window_id: str) -> None:
    """Clear context for a specific window to prevent memory leaks."""
    if window_id in _window_contexts:
        del _window_contexts[window_id]


def require_config_context(func):
    """Decorator to ensure config context is available for UI operations."""
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        from openhcs.core.config import GlobalPipelineConfig
        current_context = get_current_global_config(GlobalPipelineConfig)
        if current_context is None:
            raise RuntimeError(
                f"{func.__name__} requires active configuration context. "
                f"Use orchestrator.config_context() or ensure global config is set."
            )
        return func(*args, **kwargs)
    return wrapper


#def get_all_global_config_types() -> list[Type]:
#    """Get all global config types that have been registered.
#
#    Returns:
#        List of all config types that have active contexts
#    """
#    # Get types from thread-local contexts
#    thread_local_types = list(_global_config_contexts.keys())
#
#    # Get types from window contexts
#    window_types = set()
#    for window_context in _window_contexts.values():
#        window_types.update(window_context.keys())
#
#    # Combine and deduplicate
#    all_types = list(set(thread_local_types + list(window_types)))
#    return all_types
#