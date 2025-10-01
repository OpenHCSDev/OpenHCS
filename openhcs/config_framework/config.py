"""
Framework configuration for pluggable base config type.

This module provides the configuration interface for the lazy configuration framework,
allowing applications to specify their base configuration type.

The framework uses pure MRO-based resolution. The dual-axis resolution works by:
1. X-axis: Context flattening (Step → Pipeline → Global contexts merged)
2. Y-axis: MRO traversal (most specific → least specific class in inheritance chain)

You only need to call set_base_config_type() once at application startup.
"""

from typing import Type, Optional


# Global framework configuration
_base_config_type: Optional[Type] = None


def set_base_config_type(config_type: Type) -> None:
    """
    Set the base configuration type for the framework.
    
    This type is used as the root of the configuration hierarchy and should be
    the top-level configuration dataclass for your application.
    
    Args:
        config_type: The base configuration dataclass type
        
    Example:
        >>> from myapp.config import GlobalConfig
        >>> from openhcs.config_framework.config import set_base_config_type
        >>> set_base_config_type(GlobalConfig)
    """
    global _base_config_type
    _base_config_type = config_type


def get_base_config_type() -> Type:
    """
    Get the base configuration type.
    
    Returns:
        The base configuration type
        
    Raises:
        RuntimeError: If base config type has not been set
    """
    if _base_config_type is None:
        raise RuntimeError(
            "Base config type not set. Call set_base_config_type() during "
            "application initialization."
        )
    return _base_config_type


