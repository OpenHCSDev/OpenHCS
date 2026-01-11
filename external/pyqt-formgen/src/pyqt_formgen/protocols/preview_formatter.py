"""Preview formatter registry for customizable list item previews.

Allows applications to register custom formatters for specific config types
to control how they appear in list item previews.
"""

from typing import Callable, Any, Dict, Type, Optional


# Type alias for formatter functions
# Takes (config_instance, field_name) -> formatted_string
PreviewFormatter = Callable[[Any, str], str]


class PreviewFormatterRegistry:
    """Registry for preview formatters by config type.

    Applications can register formatters for specific config types to customize
    how fields are displayed in list item previews.

    Example:
        from pyqt_formgen.protocols import PreviewFormatterRegistry

        def format_zarr_config(config, field_name):
            if field_name == 'compression':
                return f"comp={config.compression[:3]}"  # Abbreviate
            return str(getattr(config, field_name))

        PreviewFormatterRegistry.register(ZarrConfig, format_zarr_config)
    """

    _formatters: Dict[Type, PreviewFormatter] = {}

    @classmethod
    def register(cls, config_type: Type, formatter: PreviewFormatter) -> None:
        """Register a formatter for a config type.

        Args:
            config_type: Config class to format
            formatter: Formatter function taking (config, field_name) -> str
        """
        cls._formatters[config_type] = formatter

    @classmethod
    def get_formatter(cls, config_type: Type) -> Optional[PreviewFormatter]:
        """Get formatter for a config type.

        Args:
            config_type: Config class

        Returns:
            Formatter function if registered, None otherwise
        """
        formatter = cls._formatters.get(config_type)
        if formatter:
            return formatter

        # Check base classes (for shared config bases)
        for base in getattr(config_type, "__mro__", ())[1:]:
            formatter = cls._formatters.get(base)
            if formatter:
                return formatter

        return None

    @classmethod
    def format_field(cls, config: Any, field_name: str) -> Optional[str]:
        """Format a field using registered formatter if available.

        Args:
            config: Config instance
            field_name: Field name to format

        Returns:
            Formatted string if formatter available, None otherwise
        """
        formatter = cls.get_formatter(type(config))
        if formatter:
            try:
                return formatter(config, field_name)
            except Exception:
                return None
        return None


# Convenience function for registration
def register_preview_formatter(config_type: Type, formatter: PreviewFormatter) -> None:
    """Register a preview formatter for a config type.

    Args:
        config_type: Config class
        formatter: Formatter function
    """
    PreviewFormatterRegistry.register(config_type, formatter)
