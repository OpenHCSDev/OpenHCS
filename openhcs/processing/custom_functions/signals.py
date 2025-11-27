"""
Qt signals for custom function system.

Provides global signal instance to notify UI components when custom functions
change (registered, deleted, reloaded). This enables automatic UI refresh
across multiple open dialogs.

Design:
    - Single global signal instance (custom_function_signals)
    - Emit functions_changed signal after any modification
    - UI components connect to signal for automatic refresh
"""

from PyQt6.QtCore import QObject, pyqtSignal


class CustomFunctionSignals(QObject):
    """
    Qt signals for custom function state changes.

    Signals:
        functions_changed: Emitted when custom functions are added, deleted, or reloaded
                          No arguments - receivers should query manager for current state
    """

    # Signal emitted when custom function registry changes
    functions_changed = pyqtSignal()

    def __init__(self):
        """Initialize signal object."""
        super().__init__()


# Global singleton instance for custom function signals
# All components should connect to this instance
custom_function_signals = CustomFunctionSignals()
