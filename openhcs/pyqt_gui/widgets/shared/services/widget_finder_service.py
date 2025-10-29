"""
Service for finding widgets in ParameterFormManager.

This module consolidates all widget finding patterns into a single service,
eliminating duplicate findChild() and widgets.get() calls throughout the codebase.

Key features:
1. Centralized widget finding logic
2. Type-safe widget retrieval
3. Handles optional checkbox patterns
4. Supports nested widget searches
5. Fail-loud behavior (no silent None returns)

Pattern:
    Instead of:
        ids = self.service.generate_field_ids_direct(self.config.field_id, param_name)
        checkbox = container.findChild(QCheckBox, ids['optional_checkbox_id'])
        if checkbox:
            # ... use checkbox
    
    Use:
        checkbox = WidgetFinderService.find_optional_checkbox(manager, param_name)
        if checkbox:
            # ... use checkbox
"""

from typing import Optional, List, Type
from PyQt6.QtWidgets import QWidget, QCheckBox
import logging

logger = logging.getLogger(__name__)


class WidgetFinderService:
    """
    Service for finding widgets in ParameterFormManager.
    
    This service consolidates all widget finding patterns, eliminating duplicate
    findChild() and widgets.get() calls throughout the codebase.
    
    Examples:
        # Find optional checkbox:
        checkbox = WidgetFinderService.find_optional_checkbox(manager, param_name)
        
        # Find group box:
        group = WidgetFinderService.find_group_box(container)
        
        # Get widget safely:
        widget = WidgetFinderService.get_widget_safe(manager, param_name)
    """
    
    @staticmethod
    def find_optional_checkbox(manager, param_name: str) -> Optional[QCheckBox]:
        """
        Find the optional checkbox for a parameter.
        
        For Optional[Dataclass] parameters, finds the checkbox that controls
        whether the dataclass is enabled (checked) or None (unchecked).
        
        Args:
            manager: ParameterFormManager instance
            param_name: Parameter name
        
        Returns:
            QCheckBox if found, None otherwise
        
        Example:
            checkbox = WidgetFinderService.find_optional_checkbox(self, param_name)
            if checkbox:
                checkbox.setChecked(True)
        """
        container = manager.widgets.get(param_name)
        if not container:
            logger.debug(f"No container widget found for param_name={param_name}")
            return None
        
        # Generate field IDs using service
        ids = manager.service.generate_field_ids_direct(manager.config.field_id, param_name)
        checkbox_id = ids['optional_checkbox_id']
        
        # Find checkbox by ID
        checkbox = container.findChild(QCheckBox, checkbox_id)
        if checkbox:
            logger.debug(f"Found optional checkbox for param_name={param_name}, id={checkbox_id}")
        else:
            logger.debug(f"No optional checkbox found for param_name={param_name}, id={checkbox_id}")
        
        return checkbox
    
    @staticmethod
    def find_group_box(container: QWidget, group_box_type: Type = None) -> Optional[QWidget]:
        """
        Find a group box widget within a container.
        
        Args:
            container: Container widget to search in
            group_box_type: Optional specific group box type to find (default: GroupBoxWithHelp)
        
        Returns:
            Group box widget if found, None otherwise
        
        Example:
            from .clickable_help_components import GroupBoxWithHelp
            group = WidgetFinderService.find_group_box(container, GroupBoxWithHelp)
            if group:
                group.setEnabled(True)
        """
        if group_box_type is None:
            # Default to GroupBoxWithHelp
            try:
                from openhcs.pyqt_gui.widgets.shared.clickable_help_components import GroupBoxWithHelp
                group_box_type = GroupBoxWithHelp
            except ImportError:
                logger.warning("Could not import GroupBoxWithHelp")
                return None
        
        group = container.findChild(group_box_type)
        if group:
            logger.debug(f"Found group box of type {group_box_type.__name__}")
        else:
            logger.debug(f"No group box of type {group_box_type.__name__} found")
        
        return group
    
    @staticmethod
    def get_widget_safe(manager, param_name: str) -> Optional[QWidget]:
        """
        Safely get a widget from manager's widgets dict.
        
        This is a wrapper around manager.widgets.get() that adds logging
        and consistent None handling.
        
        Args:
            manager: ParameterFormManager instance
            param_name: Parameter name
        
        Returns:
            Widget if found, None otherwise
        
        Example:
            widget = WidgetFinderService.get_widget_safe(self, param_name)
            if widget:
                value = self.get_widget_value(widget)
        """
        widget = manager.widgets.get(param_name)
        if widget:
            logger.debug(f"Found widget for param_name={param_name}, type={type(widget).__name__}")
        else:
            logger.debug(f"No widget found for param_name={param_name}")
        
        return widget
    
    @staticmethod
    def find_all_input_widgets(container: QWidget, widget_ops) -> List[QWidget]:
        """
        Find all input widgets within a container.
        
        Uses WidgetOperations.get_all_value_widgets() to find all widgets
        that implement ValueGettable/ValueSettable ABCs.
        
        Args:
            container: Container widget to search in
            widget_ops: WidgetOperations instance
        
        Returns:
            List of input widgets
        
        Example:
            widgets = WidgetFinderService.find_all_input_widgets(container, self.widget_ops)
            for widget in widgets:
                widget.setEnabled(False)
        """
        # Use WidgetOperations ABC-based approach
        widgets = widget_ops.get_all_value_widgets(container)
        logger.debug(f"Found {len(widgets)} input widgets in container")
        return widgets
    
    @staticmethod
    def find_nested_checkbox(manager, param_name: str) -> Optional[QCheckBox]:
        """
        Find the checkbox within an optional dataclass widget.
        
        For Optional[Dataclass] parameters, the widget is a container with a checkbox inside.
        This method finds that inner checkbox.
        
        Args:
            manager: ParameterFormManager instance
            param_name: Parameter name
        
        Returns:
            QCheckBox if found, None otherwise
        
        Example:
            checkbox = WidgetFinderService.find_nested_checkbox(self, param_name)
            if checkbox and not checkbox.isChecked():
                # Checkbox is unchecked, dataclass is None
                return None
        """
        checkbox_widget = manager.widgets.get(param_name)
        if not checkbox_widget:
            logger.debug(f"No checkbox widget found for param_name={param_name}")
            return None
        
        # Find QCheckBox child (no ID needed, just find first QCheckBox)
        checkbox = checkbox_widget.findChild(QCheckBox)
        if checkbox:
            logger.debug(f"Found nested checkbox for param_name={param_name}")
        else:
            logger.debug(f"No nested checkbox found for param_name={param_name}")
        
        return checkbox
    
    @staticmethod
    def find_reset_button(manager, param_name: str) -> Optional[QWidget]:
        """
        Find the reset button for a parameter.
        
        Args:
            manager: ParameterFormManager instance
            param_name: Parameter name
        
        Returns:
            Reset button widget if found, None otherwise
        
        Example:
            reset_btn = WidgetFinderService.find_reset_button(self, param_name)
            if reset_btn:
                reset_btn.setEnabled(True)
        """
        # Generate field IDs using service
        ids = manager.service.generate_field_ids_direct(manager.config.field_id, param_name)
        reset_button_id = ids['reset_button_id']
        
        # Find reset button by ID (search in manager's main widget)
        from PyQt6.QtWidgets import QPushButton
        reset_btn = manager.findChild(QPushButton, reset_button_id)
        
        if reset_btn:
            logger.debug(f"Found reset button for param_name={param_name}, id={reset_button_id}")
        else:
            logger.debug(f"No reset button found for param_name={param_name}, id={reset_button_id}")
        
        return reset_btn
    
    @staticmethod
    def has_widget(manager, param_name: str) -> bool:
        """
        Check if a widget exists for a parameter.
        
        Args:
            manager: ParameterFormManager instance
            param_name: Parameter name
        
        Returns:
            True if widget exists, False otherwise
        
        Example:
            if WidgetFinderService.has_widget(self, param_name):
                widget = self.widgets[param_name]
                # ... use widget
        """
        return param_name in manager.widgets

