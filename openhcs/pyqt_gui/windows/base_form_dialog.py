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

# Import ScopedBorderMixin directly from module, avoiding widgets/__init__.py (circular import)
import openhcs.pyqt_gui.widgets.shared.scoped_border_mixin as _scoped_border_module
ScopedBorderMixin = _scoped_border_module.ScopedBorderMixin

logger = logging.getLogger(__name__)


class HasUnregisterMethod(Protocol):
    """Protocol for objects that can be unregistered from cross-window updates."""
    def unregister_from_cross_window_updates(self) -> None: ...


class BaseFormDialog(ScopedBorderMixin, QDialog):
    """Base dialog with automatic singleton-per-scope behavior.

    Ensures only ONE window per (scope_id, window_class) is open at a time.
    If a window for this scope already exists, show() focuses it instead of creating a duplicate.
    """

    def show(self) -> None:
        """Override show to enforce singleton-per-scope behavior.

        If a window with the same scope_key already exists, focus it instead of showing self.
        Otherwise, register self with WindowManager and show normally.

        Also initializes scope-based border styling here (not in __init__) because
        subclasses set scope_id AFTER calling super().__init__().
        """
        from openhcs.pyqt_gui.services.window_manager import WindowManager

        scope_key = self._get_window_scope_key()
        if scope_key is None:
            # No scope_id - just show normally (legacy behavior)
            super().show()
            return

        # Check if window already exists for this scope
        if WindowManager.is_open(scope_key):
            # Focus existing window instead of showing duplicate
            WindowManager.focus_and_navigate(scope_key)
            # DON'T call deleteLater() - it causes crashes because async widget creation
            # (QTimer.singleShot) continues running and references deleted objects.
            # Instead, just return without showing. The window will be garbage collected
            # naturally when all async work completes and references are released.
            logger.debug(f"[SINGLETON] Focused existing window for {scope_key}")
            return

        # Initialize scope-based border styling (ScopedBorderMixin)
        # Done here because scope_id is set by subclass AFTER super().__init__()
        self._init_scope_border()

        # Register self with WindowManager (it will handle closeEvent cleanup)
        WindowManager.register(scope_key, self)
        super().show()
        logger.debug(f"[SINGLETON] Registered and showed new window for {scope_key}")

    def _get_window_scope_key(self) -> Optional[str]:
        """Build unique key for WindowManager registration.

        Returns:
            Unique key like "::PipelineConfig" or "/path/to/plate::ConfigWindow"
            Returns None if no scope_id is set (legacy behavior - no singleton enforcement)
        """
        scope_id = getattr(self, 'scope_id', None)
        if scope_id is None:
            return None

        # Include class name to allow different window types for same scope
        # e.g., ConfigWindow and DualEditorWindow for same plate
        return f"{scope_id}::{self.__class__.__name__}"

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

    def _mark_saved_and_refresh_all(self):
        """Mark all states as saved and refresh placeholders.

        Used by shift-click save to update saved baseline without closing window.
        Regular save calls accept() which also marks saved but additionally closes window.

        CRITICAL: This ensures shift-click save works the same as regular save:
        - Marks all states as saved (reconstructs object_instance from ORM values via to_object())
        - Updates saved baseline so closing window later won't revert changes
        - Refreshes all form managers with new saved values
        - Notifies other windows of changes
        """
        # Mark all states as saved (updates object_instance from ORM values)
        self._apply_state_action('mark_saved')

        # Increment global token to invalidate all caches
        from openhcs.config_framework.object_state import ObjectStateRegistry
        ObjectStateRegistry.increment_token()

        # Refresh all form managers with new saved values as baseline
        from openhcs.pyqt_gui.widgets.shared.services.parameter_ops_service import ParameterOpsService
        for manager in self._get_form_managers():
            ParameterOpsService().refresh_with_live_context(manager)
            # Emit context_changed to notify other windows (bulk refresh)
            manager.context_changed.emit(manager.scope_id or "", "")
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
        self._scope_accent_color = None  # Stored for deferred application to async widgets

        # CRITICAL: Register with global event bus for cross-window updates
        # This is the OpenHCS "set and forget" pattern - all windows automatically
        # receive updates from all other windows without manual connections
        event_bus = self._get_event_bus()
        if event_bus:
            event_bus.register_window(self)
            # Connect to pipeline_changed signal if this window cares about pipeline updates
            if hasattr(self, '_on_pipeline_changed'):
                event_bus.pipeline_changed.connect(self._on_pipeline_changed)
            logger.debug(f"{self.__class__.__name__}: Registered with global event bus")
        
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

    def _apply_scope_accent_styling(self) -> None:
        """Apply scope accent color to all UI elements.

        Called by ScopedBorderMixin._init_scope_border() after scope color scheme is set.
        Styles: input focus borders, HelpButtons. Subclasses can extend for additional elements.
        """
        accent_color = self.get_scope_accent_color()
        if not accent_color:
            return

        # Store for deferred application to async-created widgets
        self._scope_accent_color = accent_color
        hex_color = accent_color.name()

        # Apply window-level stylesheet for input widget focus borders
        input_focus_style = f"""
            QLineEdit:focus {{
                border: 2px solid {hex_color};
            }}
            QComboBox:focus {{
                border: 2px solid {hex_color};
            }}
            QSpinBox:focus {{
                border: 2px solid {hex_color};
            }}
            QDoubleSpinBox:focus {{
                border: 2px solid {hex_color};
            }}
        """
        current_window_style = self.styleSheet() or ""
        self.setStyleSheet(f"{current_window_style}\n{input_focus_style}")

        # Apply to existing HelpButtons now
        self._apply_accent_to_help_buttons()

        # Register callback for async-created widgets using existing infrastructure
        for manager in self._get_form_managers():
            if hasattr(manager, '_on_build_complete_callbacks'):
                manager._on_build_complete_callbacks.append(self._apply_accent_to_help_buttons)

    def _apply_accent_to_help_buttons(self) -> None:
        """Apply scope accent color to all HelpButton, HelpIndicator, GroupBoxWithHelp, FunctionPaneWidget, and tree instances."""
        accent_color = getattr(self, '_scope_accent_color', None)
        if not accent_color:
            return

        from openhcs.pyqt_gui.widgets.shared.clickable_help_components import HelpButton, HelpIndicator, GroupBoxWithHelp
        from openhcs.pyqt_gui.widgets.function_pane import FunctionPaneWidget
        from PyQt6.QtWidgets import QWidget

        # Find all HelpButtons, HelpIndicators, GroupBoxWithHelp, and FunctionPaneWidget in entire dialog
        if isinstance(self, QWidget):
            for help_btn in self.findChildren(HelpButton):
                help_btn.set_scope_accent_color(accent_color)
            for help_indicator in self.findChildren(HelpIndicator):
                help_indicator.set_scope_accent_color(accent_color)
            # Apply scope border pattern to nested groupboxes
            scope_scheme = getattr(self, '_scope_color_scheme', None)
            if scope_scheme:
                for groupbox in self.findChildren(GroupBoxWithHelp):
                    groupbox.set_scope_color_scheme(scope_scheme)
                # FunctionPaneWidget needs scope accent for title color (no border)
                for func_pane in self.findChildren(FunctionPaneWidget):
                    func_pane.set_scope_color_scheme(scope_scheme)
                # FunctionListEditorWidget needs scheme to apply to newly created panes
                from openhcs.pyqt_gui.widgets.function_list_editor import FunctionListEditorWidget
                for func_editor in self.findChildren(FunctionListEditorWidget):
                    func_editor.set_scope_color_scheme(scope_scheme)
                # Apply scope background to hierarchy tree (step editor)
                self._apply_scope_to_hierarchy_trees(scope_scheme)

    def _apply_scope_to_hierarchy_trees(self, scope_scheme) -> None:
        """Apply scope-colored background to hierarchy trees in form managers."""
        from openhcs.pyqt_gui.widgets.shared.config_hierarchy_tree import ConfigHierarchyTreeHelper

        for manager in self._get_form_managers():
            # Get tree from parent widget (step_editor has hierarchy_tree)
            parent = getattr(manager, 'parent', None)
            if parent and callable(parent):
                parent = parent()
            tree = getattr(parent, 'hierarchy_tree', None)
            tree_helper = getattr(parent, 'tree_helper', None)
            if tree and tree_helper and isinstance(tree_helper, ConfigHierarchyTreeHelper):
                tree_helper.apply_scope_background(tree, scope_scheme)

    def _apply_state_action(self, action: str) -> None:
        """Apply a state-level action (mark_saved/restore_saved) to all discovered managers."""
        if action not in ("mark_saved", "restore_saved"):
            return

        seen_states = set()
        for manager in self._get_form_managers():
            try:
                state = manager.state
            except AttributeError:
                continue

            state_id = id(state)
            if state_id in seen_states:
                continue

            try:
                if action == "mark_saved":
                    state.mark_saved()
                else:
                    state.restore_saved()
            except Exception as e:
                field_id = getattr(state, 'field_id', '?')
                logger.warning(f"{self.__class__.__name__}: failed to {action} for state {field_id}: {e}")

            seen_states.add(state_id)
    
    def _get_event_bus(self):
        """Get the global event bus from the service adapter.

        Returns:
            GlobalEventBus instance or None if not found
        """
        try:
            # Navigate up to find main window with service adapter
            current = self.parent()
            while current:
                if hasattr(current, 'service_adapter'):
                    return current.service_adapter.get_event_bus()
                current = current.parent()

            logger.debug(f"{self.__class__.__name__}: Could not find service adapter for event bus")
            return None
        except Exception as e:
            logger.error(f"Error getting event bus: {e}")
            return None

    def _broadcast_pipeline_changed(self, pipeline_steps: list):
        """Broadcast pipeline changed event to all windows via event bus.

        Args:
            pipeline_steps: Updated list of FunctionStep objects
        """
        event_bus = self._get_event_bus()
        if event_bus:
            event_bus.emit_pipeline_changed(pipeline_steps)

    def _broadcast_config_changed(self, config):
        """Broadcast config changed event to all windows via event bus.

        Args:
            config: Updated config object
        """
        event_bus = self._get_event_bus()
        if event_bus:
            event_bus.emit_config_changed(config)

    def _unregister_all_form_managers(self):
        """Unregister all form managers from cross-window updates."""
        if self._unregistered:
            logger.debug(f"🔍 {self.__class__.__name__}: Already unregistered, skipping")
            return

        logger.info(f"🔍 {self.__class__.__name__}: Unregistering all form managers")

        # Unregister from event bus
        event_bus = self._get_event_bus()
        if event_bus:
            event_bus.unregister_window(self)
            logger.debug(f"{self.__class__.__name__}: Unregistered from global event bus")

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
        # Persist current form values as the new saved baseline
        self._apply_state_action('mark_saved')
        self._unregister_all_form_managers()

        # CRITICAL: Cleanup WindowFlashOverlay to prevent memory leak
        from openhcs.pyqt_gui.widgets.shared.flash_mixin import WindowFlashOverlay
        WindowFlashOverlay.cleanup_window(self)
        logger.info(f"🔍 {self.__class__.__name__}: Cleaned up WindowFlashOverlay")

        super().accept()

    def reject(self):
        """Override reject to unregister before closing."""
        logger.info(f"🔍 {self.__class__.__name__}: reject() called")
        # Revert to last saved baseline before closing
        self._apply_state_action('restore_saved')
        self._unregister_all_form_managers()

        # CRITICAL: Cleanup WindowFlashOverlay to prevent memory leak
        from openhcs.pyqt_gui.widgets.shared.flash_mixin import WindowFlashOverlay
        WindowFlashOverlay.cleanup_window(self)
        logger.info(f"🔍 {self.__class__.__name__}: Cleaned up WindowFlashOverlay")

        super().reject()
        
    def closeEvent(self, a0):
        """Override closeEvent to unregister before closing.

        When user closes via X button (not via accept/reject), we need to:
        1. Restore saved state for any unsaved changes
        2. Trigger global refresh so other windows sync
        3. Cleanup WindowFlashOverlay to prevent memory leak
        4. Unregister from WindowManager for singleton tracking
        """
        logger.info(f"🔍 {self.__class__.__name__}: closeEvent() called")

        # Restore saved state (reverts unsaved changes)
        # This is safe even if no changes - restore_saved() is idempotent
        self._apply_state_action('restore_saved')

        self._unregister_all_form_managers()

        # CRITICAL: Cleanup WindowFlashOverlay to prevent memory leak
        # Without this, every window's overlay stays in _overlays dict forever,
        # making flash operations progressively slower (O(n) where n = windows ever opened)
        from openhcs.pyqt_gui.widgets.shared.flash_mixin import WindowFlashOverlay
        WindowFlashOverlay.cleanup_window(self)
        logger.info(f"🔍 {self.__class__.__name__}: Cleaned up WindowFlashOverlay")

        # Unregister from WindowManager so window can be reopened
        from openhcs.pyqt_gui.services.window_manager import WindowManager
        scope_key = self._get_window_scope_key()
        if scope_key:
            WindowManager.unregister(scope_key)
            logger.debug(f"🔍 {self.__class__.__name__}: Unregistered from WindowManager: {scope_key}")

        super().closeEvent(a0)

        # Trigger global refresh AFTER unregistration so other windows
        # re-collect live context without this window's cancelled values
        from openhcs.config_framework.object_state import ObjectStateRegistry
        ObjectStateRegistry.increment_token()
        logger.info(f"🔍 {self.__class__.__name__}: Triggered global refresh after closeEvent")
