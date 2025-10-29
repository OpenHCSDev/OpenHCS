"""
Context manager for cross-window registration of ParameterFormManager.

This context manager ensures proper registration and cleanup of form managers
for cross-window updates, following the RAII principle.

Usage:
    manager = ParameterFormManager(...)
    with cross_window_registration(manager):
        dialog.exec()  # Manager is registered during dialog lifetime
    # Manager is automatically unregistered when dialog closes
"""

from contextlib import contextmanager
from typing import Any, TYPE_CHECKING

if TYPE_CHECKING:
    from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager


@contextmanager
def cross_window_registration(manager: 'ParameterFormManager'):
    """
    Context manager for cross-window registration.
    
    Ensures proper registration and cleanup of form managers for cross-window updates.
    
    Benefits:
    - Guaranteed cleanup via finally block (RAII principle)
    - Explicit registration at call site (not hidden in __init__)
    - Exception-safe cleanup
    - Testable (can create managers without triggering registration)
    
    Args:
        manager: ParameterFormManager instance to register
        
    Yields:
        The manager instance
        
    Example:
        >>> manager = ParameterFormManager(config, "editor")
        >>> with cross_window_registration(manager):
        ...     dialog.exec()
        # Manager is automatically unregistered when dialog closes
    """
    # Only register root managers (not nested)
    if manager._parent_manager is not None:
        yield manager
        return
    
    try:
        # Registration
        from .signal_connection_service import SignalConnectionService
        SignalConnectionService.register_cross_window_signals(manager)
        
        yield manager
        
    finally:
        # Guaranteed cleanup - even if exception occurs
        manager.unregister_from_cross_window_updates()

