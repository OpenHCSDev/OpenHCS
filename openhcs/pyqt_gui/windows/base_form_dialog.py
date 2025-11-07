"""
Base Form Dialog for PyQt6

Base class for dialogs that use ParameterFormManager to ensure proper cleanup
of cross-window placeholder update connections.

This base class solves the problem of ghost form managers remaining in the
_active_form_managers registry after a dialog closes, which causes infinite
placeholder refresh loops and runaway CPU usage.

The issue occurs because Qt's QDialog.accept() and QDialog.reject() methods
do NOT trigger closeEvent() - they just hide the dialog. This means any cleanup
code in closeEvent() is never called when the user clicks Save or Cancel.

This base class overrides accept(), reject(), and closeEvent() to ensure that
form managers are always unregistered from cross-window updates, regardless of
how the dialog is closed.

The default implementation automatically discovers all ParameterFormManager
instances in the widget tree, so subclasses don't need to manually track them.

Usage:
    1. Inherit from BaseFormDialog instead of QDialog
    2. That's it! All ParameterFormManager instances are automatically discovered and cleaned up.

Example:
    class MyConfigDialog(BaseFormDialog):
        def __init__(self, ...):
            super().__init__(...)
            self.form_manager = ParameterFormManager(...)
            # No need to override _get_form_managers() - automatic discovery!
"""

import logging
from typing import Optional, Protocol

from PyQt6.QtWidgets import QDialog
from PyQt6.QtCore import QEvent

# For save button setup
from PyQt6.QtWidgets import QPushButton
from typing import Callable
from PyQt6.QtCore import Qt

logger = logging.getLogger(__name__)


class HasUnregisterMethod(Protocol):
    """Protocol for objects that can be unregistered from cross-window updates."""
    def unregister_from_cross_window_updates(self) -> None: ...


class BaseFormDialog(QDialog):

    def _setup_save_button(self, button: 'QPushButton', save_callback: Callable):
        """
        Connects a save button to support Shift+Click for 'Save without close'.
        The save_callback should accept only close_window as a keyword argument.
        If Shift is held, close_window will be False (update only); otherwise True.
        """
        from PyQt6.QtWidgets import QApplication
        def _on_save():
            modifiers = QApplication.keyboardModifiers()
            is_shift = modifiers & Qt.KeyboardModifier.ShiftModifier
            save_callback(close_window=not is_shift)
        button.clicked.connect(_on_save)
    """
    Base class for dialogs that use ParameterFormManager.
    
    Automatically handles unregistration from cross-window updates when the dialog
    closes via any method (accept, reject, or closeEvent).
    
    Subclasses should:
    1. Store their ParameterFormManager instance(s) in a way that can be discovered
    2. Override _get_form_managers() to return a list of all form managers to unregister
    
    Example:
        class MyDialog(BaseFormDialog):
            def __init__(self, ...):
                super().__init__(...)
                self.form_manager = ParameterFormManager(...)
                
            def _get_form_managers(self):
                return [self.form_manager]
    """
    
    def __init__(self, parent=None):
        super().__init__(parent)
        self._unregistered = False  # Track if we've already unregistered
        
    def _get_form_managers(self):
        """
        Return a list of all ParameterFormManager instances that need to be unregistered.

        Default implementation recursively searches the widget tree for all
        ParameterFormManager instances. Subclasses can override for custom behavior.

        Returns:
            List of ParameterFormManager instances
        """
        managers = []
        self._collect_form_managers_recursive(self, managers, visited=set())
        return managers

    def _collect_form_managers_recursive(self, widget, managers, visited):
        """
        Recursively collect all ParameterFormManager instances from widget tree.

        This eliminates the need for manual tracking - just inherit from BaseFormDialog
        and all nested form managers will be automatically discovered and cleaned up.

        Uses Protocol-based duck typing to check for unregister method, avoiding
        hasattr smell for guaranteed attributes while still supporting dynamic discovery.

        Args:
            widget: Widget to search
            managers: List to append found managers to
            visited: Set of already-visited widget IDs to prevent infinite loops
        """
        # Prevent infinite loops from circular references
        widget_id = id(widget)
        if widget_id in visited:
            return
        visited.add(widget_id)

        # Check if this widget IS a ParameterFormManager (duck typing via Protocol)
        # This is legitimate hasattr - we're discovering unknown widget types
        if callable(getattr(widget, 'unregister_from_cross_window_updates', None)):
            managers.append(widget)
            return  # Don't recurse into the manager itself

        # Check if this widget HAS a form_manager attribute
        # This is legitimate - form_manager is an optional composition pattern
        form_manager = getattr(widget, 'form_manager', None)
        if form_manager is not None and callable(getattr(form_manager, 'unregister_from_cross_window_updates', None)):
            managers.append(form_manager)

        # Recursively search child widgets using Qt's children() method
        try:
            for child in widget.children():
                self._collect_form_managers_recursive(child, managers, visited)
        except (RuntimeError, AttributeError):
            # Widget already deleted - this is expected during cleanup
            pass

        # Also check common container attributes that might hold widgets
        # These are known patterns in our UI architecture
        for attr_name in ['function_panes', 'step_editor', 'func_editor', 'parameter_editor']:
            attr_value = getattr(widget, attr_name, None)
            if attr_value is not None:
                # Handle lists of widgets
                if isinstance(attr_value, list):
                    for item in attr_value:
                        self._collect_form_managers_recursive(item, managers, visited)
                # Handle single widget
                else:
                    self._collect_form_managers_recursive(attr_value, managers, visited)
    
    def _unregister_all_form_managers(self):
        """Unregister all form managers from cross-window updates."""
        if self._unregistered:
            logger.debug(f"🔍 {self.__class__.__name__}: Already unregistered, skipping")
            return
            
        logger.info(f"🔍 {self.__class__.__name__}: Unregistering all form managers")
        
        managers = self._get_form_managers()
        
        if not managers:
            logger.debug(f"🔍 {self.__class__.__name__}: No form managers found to unregister")
            return
            
        for manager in managers:
            try:
                logger.info(f"🔍 {self.__class__.__name__}: Calling unregister on {manager.field_id} (id={id(manager)})")
                manager.unregister_from_cross_window_updates()
            except Exception as e:
                logger.error(f"Failed to unregister form manager {manager.field_id}: {e}")
                
        self._unregistered = True
        logger.info(f"🔍 {self.__class__.__name__}: All form managers unregistered")
    
    def accept(self):
        """Override accept to unregister before closing."""
        logger.info(f"🔍 {self.__class__.__name__}: accept() called")
        self._unregister_all_form_managers()
        super().accept()
        
    def reject(self):
        """Override reject to unregister before closing."""
        logger.info(f"🔍 {self.__class__.__name__}: reject() called")
        self._unregister_all_form_managers()
        super().reject()
        
    def closeEvent(self, a0):
        """Override closeEvent to unregister before closing."""
        logger.info(f"🔍 {self.__class__.__name__}: closeEvent() called")
        self._unregister_all_form_managers()
        super().closeEvent(a0)

