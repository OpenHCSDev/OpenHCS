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
from dataclasses import dataclass
import os


@dataclass
class FrameworkConfig:
    """
    Global configuration for the config framework itself.

    This controls framework-level behavior like caching, debugging, etc.
    Separate from application config (GlobalPipelineConfig, etc.).
    """

    # DEBUGGING: Master switch to disable ALL token-based caching systems
    # Set to True to bypass all caches and force fresh resolution every time
    # Useful for debugging whether issues are caused by caching bugs or fundamental architecture
    # When True, overrides all individual cache flags below
    disable_all_token_caches: bool = False

    # DEBUGGING: Individual cache system flags (only used if disable_all_token_caches is False)
    # These allow you to selectively disable specific caches to isolate issues
    disable_lazy_resolution_cache: bool = False      # Lazy dataclass field resolution cache
    disable_placeholder_text_cache: bool = False     # Placeholder text cache
    disable_live_context_resolver_cache: bool = False  # Live context resolver cache
    disable_unsaved_changes_cache: bool = False      # Unsaved changes detection cache

    def __post_init__(self):
        """Initialize from environment variables if set."""
        # Master switch
        if os.getenv('OPENHCS_DISABLE_TOKEN_CACHES', '').lower() in ('1', 'true', 'yes'):
            self.disable_all_token_caches = True

        # Individual cache flags
        if os.getenv('OPENHCS_DISABLE_LAZY_RESOLUTION_CACHE', '').lower() in ('1', 'true', 'yes'):
            self.disable_lazy_resolution_cache = True
        if os.getenv('OPENHCS_DISABLE_PLACEHOLDER_CACHE', '').lower() in ('1', 'true', 'yes'):
            self.disable_placeholder_text_cache = True
        if os.getenv('OPENHCS_DISABLE_LIVE_CONTEXT_CACHE', '').lower() in ('1', 'true', 'yes'):
            self.disable_live_context_resolver_cache = True
        if os.getenv('OPENHCS_DISABLE_UNSAVED_CHANGES_CACHE', '').lower() in ('1', 'true', 'yes'):
            self.disable_unsaved_changes_cache = True

    def is_cache_disabled(self, cache_name: str) -> bool:
        """
        Check if a specific cache is disabled.

        Args:
            cache_name: One of 'lazy_resolution', 'placeholder_text', 'live_context_resolver', 'unsaved_changes'

        Returns:
            True if the cache should be disabled (either globally or individually)
        """
        if self.disable_all_token_caches:
            return True

        cache_flags = {
            'lazy_resolution': self.disable_lazy_resolution_cache,
            'placeholder_text': self.disable_placeholder_text_cache,
            'live_context_resolver': self.disable_live_context_resolver_cache,
            'unsaved_changes': self.disable_unsaved_changes_cache,
        }

        return cache_flags.get(cache_name, False)


# Global framework configuration instances
_base_config_type: Optional[Type] = None
_framework_config: FrameworkConfig = FrameworkConfig()


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


def get_framework_config() -> FrameworkConfig:
    """
    Get the global framework configuration.

    Returns:
        The framework configuration instance

    Example:
        >>> from openhcs.config_framework.config import get_framework_config
        >>> config = get_framework_config()
        >>> config.disable_all_token_caches = True  # Disable all caching for debugging
    """
    return _framework_config


