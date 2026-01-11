"""Base configuration class for form generation.

Provides hooks for applications to customize form generation behavior.
"""

from typing import Any, Dict, Optional, Type, List
from dataclasses import dataclass, field


@dataclass
class FormGenConfig:
    """Base configuration for form generation behavior.

    Applications can subclass this to provide custom configuration.

    Attributes:
        enable_placeholder_styling: Whether to apply special styling to placeholder values
        enable_help_buttons: Whether to show help buttons for fields with docstrings
        enable_inheritance_tracking: Whether to show inheritance source indicators
        custom_widget_factories: Custom widget factories by type
    """

    enable_placeholder_styling: bool = True
    enable_help_buttons: bool = True
    enable_inheritance_tracking: bool = True
    custom_widget_factories: Dict[Type, Any] = field(default_factory=dict)
    jedi_project_paths: List[str] = field(default_factory=list)
    log_dir: Optional[str] = None
    log_prefixes: List[str] = field(default_factory=lambda: ["pyqt_formgen_"])
    log_root_logger_name: Optional[str] = None
    performance_logger_name: str = "pyqt_formgen.performance"
    performance_log_filename: str = "performance.log"
    path_cache_file: Optional[str] = None


# Global config instance (set by application)
_form_config: Optional[FormGenConfig] = None


def set_form_config(config: FormGenConfig) -> None:
    """Set the global form generation configuration.

    Args:
        config: FormGenConfig instance
    """
    global _form_config
    _form_config = config


def get_form_config() -> FormGenConfig:
    """Get the current form generation configuration.

    Returns:
        Current FormGenConfig or default if not set
    """
    if _form_config is None:
        return FormGenConfig()
    return _form_config
