"""
Framework operations data for memory type system.

This module now imports from the unified framework_config.py.
All framework-specific operations are consolidated in a single source of truth.

DEPRECATED: This module is maintained for backward compatibility.
New code should import directly from framework_config.py.
"""

from openhcs.core.memory.framework_config import _FRAMEWORK_CONFIG

# Re-export for backward compatibility
_FRAMEWORK_OPS = _FRAMEWORK_CONFIG

