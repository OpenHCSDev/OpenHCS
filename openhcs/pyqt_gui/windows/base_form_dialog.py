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

Usage:
    1. Inherit from BaseFormDialog instead of QDialog
    2. Override _get_form_managers() to return your form manager instances
    3. That's it! The base class handles all cleanup automatically.

Example:
    class MyConfigDialog(BaseFormDialog):
        def __init__(self, ...):
            super().__init__(...)
            self.form_manager = ParameterFormManager(...)

        def _get_form_managers(self):
            return [self.form_manager]
"""

import logging
from typing import Optional

from PyQt6.QtWidgets import QDialog
from PyQt6.QtCore import QEvent

logger = logging.getLogger(__name__)


class BaseFormDialog(QDialog):
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
        
        Subclasses should override this method to return their form managers.
        
        Returns:
            List of ParameterFormManager instances
        """
        # Default implementation: try to find common attribute names
        managers = []
        
        # Check common attribute names
        for attr_name in ['form_manager', 'step_editor', 'parameter_editor']:
            if hasattr(self, attr_name):
                obj = getattr(self, attr_name)
                
                # If it's a ParameterFormManager, add it
                if hasattr(obj, 'unregister_from_cross_window_updates'):
                    managers.append(obj)
                    
                # If it's a widget that contains a form_manager, add that
                elif hasattr(obj, 'form_manager') and hasattr(obj.form_manager, 'unregister_from_cross_window_updates'):
                    managers.append(obj.form_manager)
                    
        return managers
    
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
        
    def closeEvent(self, event):
        """Override closeEvent to unregister before closing."""
        logger.info(f"🔍 {self.__class__.__name__}: closeEvent() called")
        self._unregister_all_form_managers()
        super().closeEvent(event)

