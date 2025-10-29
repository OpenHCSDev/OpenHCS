"""
Enabled Field Styling Service - Visual styling for enabled/disabled states.

Extracts all enabled field styling logic from ParameterFormManager.
Handles dimming effects, ancestor checking, and nested config styling.
"""

from typing import Any
from PyQt6.QtWidgets import QCheckBox, QLabel, QGraphicsOpacityEffect
import logging

logger = logging.getLogger(__name__)


class EnabledFieldStylingService:
    """
    Service for applying visual styling based on enabled field state.
    
    Stateless service that encapsulates all enabled field styling operations.
    """
    
    def __init__(self, widget_ops):
        """
        Initialize enabled field styling service.
        
        Args:
            widget_ops: WidgetOperations instance for ABC-based widget operations
        """
        self.widget_ops = widget_ops
    
    def apply_initial_enabled_styling(self, manager) -> None:
        """
        Apply initial enabled field styling based on resolved value from widget.
        
        This is called once after all widgets are created to ensure initial styling matches the enabled state.
        
        CRITICAL: This should NOT be called for optional dataclass nested managers when instance is None.
        The None state dimming is handled by the optional dataclass checkbox handler.
        
        Args:
            manager: ParameterFormManager instance
        """
        # Check if this is a nested manager inside an optional dataclass with None instance
        if self._should_skip_optional_dataclass_styling(manager, "INITIAL ENABLED STYLING"):
            return
        
        # Get the enabled widget
        enabled_widget = manager.widgets.get('enabled')
        if not enabled_widget:
            logger.info(f"[INITIAL ENABLED STYLING] field_id={manager.field_id}, no enabled widget found")
            return
        
        # Get resolved value from checkbox
        if isinstance(enabled_widget, QCheckBox):
            resolved_value = enabled_widget.isChecked()
            logger.info(f"[INITIAL ENABLED STYLING] field_id={manager.field_id}, resolved_value={resolved_value} (from checkbox)")
        else:
            # Fallback to parameter value
            resolved_value = manager.parameters.get('enabled')
            if resolved_value is None:
                resolved_value = True  # Default to enabled if we can't resolve
            logger.info(f"[INITIAL ENABLED STYLING] field_id={manager.field_id}, resolved_value={resolved_value} (from parameter)")
        
        # Call the enabled handler with the resolved value
        self.on_enabled_field_changed(manager, 'enabled', resolved_value)
    
    def refresh_enabled_styling(self, manager) -> None:
        """
        Refresh enabled styling for a form and all nested forms.
        
        This should be called when context changes that might affect inherited enabled values.
        Similar to placeholder refresh, but for enabled field styling.
        
        CRITICAL: Skip optional dataclass nested managers when instance is None.
        
        Args:
            manager: ParameterFormManager instance
        """
        # Check if this is a nested manager inside an optional dataclass with None instance
        if self._should_skip_optional_dataclass_styling(manager, "REFRESH ENABLED STYLING"):
            return
        
        # Refresh this form's enabled styling if it has an enabled field
        if 'enabled' in manager.parameters:
            # Get the enabled widget to read the CURRENT resolved value
            enabled_widget = manager.widgets.get('enabled')
            if enabled_widget and isinstance(enabled_widget, QCheckBox):
                # Use the checkbox's current state (which reflects resolved placeholder)
                resolved_value = enabled_widget.isChecked()
            else:
                # Fallback to parameter value
                resolved_value = manager.parameters.get('enabled')
                if resolved_value is None:
                    resolved_value = True
            
            # Apply styling with the resolved value
            self.on_enabled_field_changed(manager, 'enabled', resolved_value)
        
        # Recursively refresh all nested forms' enabled styling
        for nested_manager in manager.nested_managers.values():
            self.refresh_enabled_styling(nested_manager)
    
    def on_enabled_field_changed(self, manager, param_name: str, value: Any) -> None:
        """
        Apply visual styling when 'enabled' parameter changes.
        
        This handler is connected for ANY form that has an 'enabled' parameter.
        When enabled resolves to False, apply visual dimming WITHOUT blocking input.
        
        Args:
            manager: ParameterFormManager instance
            param_name: Parameter name (should be 'enabled')
            value: New value (True/False/None)
        """
        if param_name != 'enabled':
            return
        
        logger.info(f"[ENABLED HANDLER CALLED] field_id={manager.field_id}, param_name={param_name}, value={value}")
        
        # Resolve lazy value
        if value is None:
            # Lazy field - get the resolved placeholder value from the widget
            enabled_widget = manager.widgets.get('enabled')
            if enabled_widget and isinstance(enabled_widget, QCheckBox):
                resolved_value = enabled_widget.isChecked()
            else:
                # Fallback: assume True if we can't resolve
                resolved_value = True
        else:
            resolved_value = value
        
        logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, resolved_value={resolved_value}")
        
        # Get direct widgets (excluding nested managers)
        direct_widgets = self._get_direct_widgets(manager)
        widget_names = [f"{w.__class__.__name__}({w.objectName() or 'no-name'})" for w in direct_widgets[:5]]
        logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, found {len(direct_widgets)} direct widgets, first 5: {widget_names}")
        
        # Check if this is a nested config
        is_nested_config = manager._parent_manager is not None and any(
            nested_manager == manager for nested_manager in manager._parent_manager.nested_managers.values()
        )
        
        if is_nested_config:
            self._apply_nested_config_styling(manager, resolved_value)
        else:
            self._apply_top_level_styling(manager, resolved_value, direct_widgets)
    
    def _should_skip_optional_dataclass_styling(self, manager, log_prefix: str) -> bool:
        """
        Check if this is a nested manager inside an optional dataclass with None instance.
        
        Args:
            manager: ParameterFormManager instance
            log_prefix: Prefix for log messages
        
        Returns:
            True if styling should be skipped, False otherwise
        """
        if manager._parent_manager is not None:
            for param_name, nested_manager in manager._parent_manager.nested_managers.items():
                if nested_manager is manager:
                    param_type = manager._parent_manager.parameter_types.get(param_name)
                    if param_type:
                        from openhcs.ui.shared.parameter_type_utils import ParameterTypeUtils
                        if ParameterTypeUtils.is_optional_dataclass(param_type):
                            instance = manager._parent_manager.parameters.get(param_name)
                            logger.info(f"[{log_prefix}] field_id={manager.field_id}, optional dataclass check: param_name={param_name}, instance={instance}, is_none={instance is None}")
                            if instance is None:
                                logger.info(f"[{log_prefix}] field_id={manager.field_id}, skipping (optional dataclass instance is None)")
                                return True
                    break
        return False
    
    def _get_direct_widgets(self, manager):
        """
        Get widgets that belong to this form, excluding nested ParameterFormManager widgets.
        
        Args:
            manager: ParameterFormManager instance
        
        Returns:
            List of widgets belonging to this form
        """
        direct_widgets = []
        all_widgets = self.widget_ops.get_all_value_widgets(manager)
        logger.info(f"[GET_DIRECT_WIDGETS] field_id={manager.field_id}, total widgets found: {len(all_widgets)}, nested_managers: {list(manager.nested_managers.keys())}")
        
        for widget in all_widgets:
            widget_name = f"{widget.__class__.__name__}({widget.objectName() or 'no-name'})"
            object_name = widget.objectName()
            
            # Check if widget belongs to a nested manager
            belongs_to_nested = False
            for nested_name, nested_manager in manager.nested_managers.items():
                nested_field_id = nested_manager.field_id
                if object_name and object_name.startswith(nested_field_id + '_'):
                    belongs_to_nested = True
                    logger.info(f"[GET_DIRECT_WIDGETS] ❌ EXCLUDE {widget_name} - belongs to nested manager {nested_field_id}")
                    break
            
            if not belongs_to_nested:
                direct_widgets.append(widget)
                logger.info(f"[GET_DIRECT_WIDGETS] ✅ INCLUDE {widget_name}")
        
        logger.info(f"[GET_DIRECT_WIDGETS] field_id={manager.field_id}, returning {len(direct_widgets)} direct widgets")
        return direct_widgets
    
    def _is_any_ancestor_disabled(self, manager) -> bool:
        """
        Check if any ancestor form has enabled=False.

        This is used to determine if a nested config should remain dimmed
        even if its own enabled field is True.

        Args:
            manager: ParameterFormManager instance

        Returns:
            True if any ancestor has enabled=False, False otherwise
        """
        current = manager._parent_manager
        while current is not None:
            if 'enabled' in current.parameters:
                enabled_widget = current.widgets.get('enabled')
                if enabled_widget and isinstance(enabled_widget, QCheckBox):
                    if not enabled_widget.isChecked():
                        return True
            current = current._parent_manager
        return False

    def _apply_nested_config_styling(self, manager, resolved_value: bool) -> None:
        """
        Apply styling to a nested config (inside GroupBox).

        Args:
            manager: ParameterFormManager instance
            resolved_value: Resolved enabled value (True/False)
        """
        # Find the GroupBox container
        group_box = None
        for param_name, nested_manager in manager._parent_manager.nested_managers.items():
            if nested_manager == manager:
                group_box = manager._parent_manager.widgets.get(param_name)
                break

        if not group_box:
            return

        logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, applying to GroupBox container")

        # Check if ANY ancestor has enabled=False
        ancestor_is_disabled = self._is_any_ancestor_disabled(manager)
        logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, ancestor_is_disabled={ancestor_is_disabled}")

        if resolved_value and not ancestor_is_disabled:
            # Enabled=True AND no ancestor is disabled: Remove dimming from GroupBox
            logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, removing dimming from GroupBox")
            for widget in self.widget_ops.get_all_value_widgets(group_box):
                widget.setGraphicsEffect(None)
        elif ancestor_is_disabled:
            # Ancestor is disabled - keep dimming regardless of child's enabled value
            logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, keeping dimming (ancestor disabled)")
            for widget in self.widget_ops.get_all_value_widgets(group_box):
                effect = QGraphicsOpacityEffect()
                effect.setOpacity(0.4)
                widget.setGraphicsEffect(effect)
        else:
            # Enabled=False: Apply dimming to GroupBox widgets
            logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, applying dimming to GroupBox")
            for widget in self.widget_ops.get_all_value_widgets(group_box):
                effect = QGraphicsOpacityEffect()
                effect.setOpacity(0.4)
                widget.setGraphicsEffect(effect)

    def _apply_top_level_styling(self, manager, resolved_value: bool, direct_widgets: list) -> None:
        """
        Apply styling to a top-level form (step, function).

        Args:
            manager: ParameterFormManager instance
            resolved_value: Resolved enabled value (True/False)
            direct_widgets: List of direct widgets (excluding nested managers)
        """
        if resolved_value:
            # Enabled=True: Remove dimming from direct widgets
            logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, removing dimming (enabled=True)")
            for widget in direct_widgets:
                widget.setGraphicsEffect(None)

            # Trigger refresh of all nested configs' enabled styling
            logger.info(f"[ENABLED HANDLER] Refreshing nested configs' enabled styling")
            for nested_manager in manager.nested_managers.values():
                self.refresh_enabled_styling(nested_manager)
        else:
            # Enabled=False: Apply dimming to direct widgets + ALL nested configs
            logger.info(f"[ENABLED HANDLER] field_id={manager.field_id}, applying dimming (enabled=False)")
            for widget in direct_widgets:
                # Skip QLabel widgets when dimming (only dim inputs)
                if isinstance(widget, QLabel):
                    continue
                effect = QGraphicsOpacityEffect()
                effect.setOpacity(0.4)
                widget.setGraphicsEffect(effect)

            # Also dim all nested configs
            logger.info(f"[ENABLED HANDLER] Dimming nested configs, found {len(manager.nested_managers)} nested managers")
            logger.info(f"[ENABLED HANDLER] Available widget keys: {list(manager.widgets.keys())}")
            for param_name, nested_manager in manager.nested_managers.items():
                group_box = manager.widgets.get(param_name)
                logger.info(f"[ENABLED HANDLER] Checking nested config {param_name}, group_box={group_box.__class__.__name__ if group_box else 'None'}")
                if not group_box:
                    logger.info(f"[ENABLED HANDLER] ⚠️ No group_box found for nested config {param_name}, trying nested_manager.field_id={nested_manager.field_id}")
                    # Try using the nested manager's field_id instead
                    group_box = manager.widgets.get(nested_manager.field_id)
                    if not group_box:
                        logger.info(f"[ENABLED HANDLER] ⚠️ Still no group_box found, skipping")
                        continue

                widgets_to_dim = self.widget_ops.get_all_value_widgets(group_box)
                logger.info(f"[ENABLED HANDLER] Applying dimming to nested config {param_name}, found {len(widgets_to_dim)} widgets")
                for widget in widgets_to_dim:
                    effect = QGraphicsOpacityEffect()
                    effect.setOpacity(0.4)
                    widget.setGraphicsEffect(effect)

