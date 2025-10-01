"""
DEPRECATED: Use openhcs.config_framework.dual_axis_resolver instead.

This module is kept for backward compatibility. All functionality
has been moved to the generic configuration framework.

New code should import from openhcs.config_framework:
    from openhcs.config_framework import resolve_field_inheritance
"""

# Re-export everything from the framework for backward compatibility
from openhcs.config_framework.dual_axis_resolver import *  # noqa: F401, F403
