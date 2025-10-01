"""
DEPRECATED: Use openhcs.config_framework.lazy_factory instead.

This module is kept for backward compatibility. All functionality
has been moved to the generic configuration framework.

New code should import from openhcs.config_framework:
    from openhcs.config_framework import LazyDataclassFactory, auto_create_decorator
"""

# Re-export everything from the framework for backward compatibility
from openhcs.config_framework.lazy_factory import *  # noqa: F401, F403
