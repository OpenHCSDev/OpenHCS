"""
GUI Testing Infrastructure

Provides tools for recording, replaying, and validating GUI interactions.
"""

from openhcs.pyqt_gui.testing.event_recorder import EventRecorder, install_recorder
from openhcs.pyqt_gui.testing.test_validator import TestValidator, WorkflowSnapshot

__all__ = [
    'EventRecorder',
    'install_recorder',
    'TestValidator',
    'WorkflowSnapshot',
]

