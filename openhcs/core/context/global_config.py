"""
Global configuration context management for OpenHCS.

Provides thread-local storage and context management for global configuration objects.
"""

import threading
from typing import Dict, Type, Optional, Any
import functools


# Generic thread-local storage for any global config type
_global_config_contexts: Dict[Type, threading.local] = {}


def set_current_global_config(config_type: Type, config_instance: Any) -> None:
    """Set current global config for any dataclass type."""
    if config_type not in _global_config_contexts:
        _global_config_contexts[config_type] = threading.local()
    _global_config_contexts[config_type].value = config_instance


def get_current_global_config(config_type: Type) -> Optional[Any]:
    """Get current global config for any dataclass type."""
    context = _global_config_contexts.get(config_type)
    return getattr(context, 'value', None) if context else None


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
