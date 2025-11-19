"""Mixin for widgets that have both a tree and a form with flash animations.

This mixin provides:
1. GroupBox flashing when scrolling to a section (double-click tree item)
2. Tree item flashing when nested config placeholders change (cross-window updates)

Used by:
- ConfigWindow
- StepParameterEditorWidget
"""

import logging
from typing import Optional
from PyQt6.QtWidgets import QTreeWidget, QTreeWidgetItem
from PyQt6.QtCore import Qt

logger = logging.getLogger(__name__)


class TreeFormFlashMixin:
    """Mixin for widgets with tree + form that need flash animations.
    
    Requirements:
    - Must have `self.form_manager` (ParameterFormManager instance)
    - Must have `self.hierarchy_tree` or `self.tree_widget` (QTreeWidget instance)
    - Must have `self.scope_id` (str for scope color scheme)
    
    Usage:
        class MyWidget(TreeFormFlashMixin, QWidget):
            def __init__(self):
                super().__init__()
                # ... create form_manager, tree_widget, scope_id ...
                
                # Override form manager's tree flash notification
                self.form_manager._notify_tree_flash = self._flash_tree_item
    """
    
    def _flash_groupbox_for_field(self, field_name: str):
        """Flash the GroupBox for a specific field.
        
        Args:
            field_name: Name of the field whose GroupBox should flash
        """
        # Get the GroupBox widget from root manager
        group_box = self.form_manager.widgets.get(field_name)
        
        if not group_box:
            logger.warning(f"No GroupBox widget found for {field_name}")
            return
        
        # Flash the GroupBox using scope border color
        from PyQt6.QtGui import QColor
        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme
        from openhcs.pyqt_gui.widgets.shared.widget_flash_animation import flash_widget
        
        # Get scope color scheme
        color_scheme = get_scope_color_scheme(self.scope_id)
        
        # Use orchestrator border color for flash (same as window border)
        border_rgb = color_scheme.orchestrator_item_border_rgb
        flash_color = QColor(*border_rgb, 180)  # Border color with high opacity
        
        # Use global registry to prevent overlapping flashes
        flash_widget(group_box, flash_color=flash_color)
        logger.debug(f"✅ Flashed GroupBox for {field_name}")
    
    def _flash_tree_item(self, config_name: str) -> None:
        """Flash tree item for a config when its placeholder changes.
        
        Args:
            config_name: Name of the config that changed (e.g., 'well_filter_config')
        """
        # Get tree widget (support both naming conventions)
        tree_widget = getattr(self, 'tree_widget', None) or getattr(self, 'hierarchy_tree', None)
        
        if tree_widget is None:
            # No tree in this widget
            return
        
        logger.debug(f"🌳 _flash_tree_item called for: {config_name}")
        
        # Find the tree item with this field_name
        item = self._find_tree_item_by_field_name(config_name, tree_widget)
        if not item:
            logger.warning(f"Could not find tree item for config: {config_name}")
            return
        
        logger.debug(f"🔥 Flashing tree item: {config_name}")
        
        # Flash the tree item using global registry
        from PyQt6.QtGui import QColor
        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme
        from openhcs.pyqt_gui.widgets.shared.tree_item_flash_animation import flash_tree_item
        
        # Get scope color scheme for this window
        color_scheme = get_scope_color_scheme(self.scope_id)
        
        # Use orchestrator border color for flash (same as window border)
        border_rgb = color_scheme.orchestrator_item_border_rgb
        flash_color = QColor(*border_rgb, 200)  # Border color with high opacity
        
        # Use global registry to prevent overlapping flashes
        flash_tree_item(tree_widget, item, flash_color)
        
        logger.debug(f"✅ Flashed tree item for {config_name}")
    
    def _find_tree_item_by_field_name(self, field_name: str, tree_widget: QTreeWidget, parent_item: Optional[QTreeWidgetItem] = None):
        """Recursively find tree item by field_name.
        
        Args:
            field_name: Field name to search for
            tree_widget: Tree widget to search in
            parent_item: Parent item to search under (None = search from root)
            
        Returns:
            QTreeWidgetItem if found, None otherwise
        """
        if parent_item is None:
            # Search all top-level items
            logger.debug(f"   Searching tree for field_name: {field_name}")
            logger.debug(f"   Tree has {tree_widget.topLevelItemCount()} top-level items")
            for i in range(tree_widget.topLevelItemCount()):
                item = tree_widget.topLevelItem(i)
                data = item.data(0, Qt.ItemDataRole.UserRole)
                logger.debug(f"     Top-level item {i}: field_name={data.get('field_name') if data else 'None'}, text={item.text(0)}")
                result = self._find_tree_item_by_field_name(field_name, tree_widget, item)
                if result:
                    return result
            logger.warning(f"   No tree item found for field_name: {field_name}")
            return None
        
        # Check if this item matches
        data = parent_item.data(0, Qt.ItemDataRole.UserRole)
        if data and data.get('field_name') == field_name:
            logger.debug(f"   Found matching tree item: {field_name}")
            return parent_item
        
        # Recursively search children
        for i in range(parent_item.childCount()):
            child = parent_item.child(i)
            result = self._find_tree_item_by_field_name(field_name, tree_widget, child)
            if result:
                return result
        
        return None

