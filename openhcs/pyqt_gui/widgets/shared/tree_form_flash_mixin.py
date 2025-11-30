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
                self._register_placeholder_flash_hook()
    """

    def _register_placeholder_flash_hook(self) -> None:
        """Register flash callback. Called after each nested manager is created."""
        # Register on root manager
        if self._on_placeholder_changed not in self.form_manager._on_placeholder_changed_callbacks:
            self.form_manager._on_placeholder_changed_callbacks.append(self._on_placeholder_changed)

        # Register on all existing nested managers
        def register_on_manager(name: str, manager) -> None:
            if self._on_placeholder_changed not in manager._on_placeholder_changed_callbacks:
                manager._on_placeholder_changed_callbacks.append(self._on_placeholder_changed)

        self.form_manager._apply_to_nested_managers(register_on_manager)

        # CRITICAL: Also register a post-build callback to catch async-created nested managers
        def register_on_new_nested():
            self.form_manager._apply_to_nested_managers(register_on_manager)

        self.form_manager._on_build_complete_callbacks.append(register_on_new_nested)
        logger.info(f"🔗 Registered placeholder flash hook on {type(self).__name__}")

    def _on_placeholder_changed(self, config_name: str, field_name: str, dataclass_type: type) -> None:
        """Called when any placeholder value changes. Flash the tree item and groupbox."""
        logger.info(f"🔥 Placeholder changed: {config_name}.{field_name} (type={dataclass_type.__name__ if dataclass_type else 'None'})")
        self._flash_for_config(config_name, dataclass_type)

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
        logger.info(f"✅ Flashed GroupBox for {field_name}")
    
    def _flash_for_config(self, config_name: str, dataclass_type: type = None) -> None:
        """Flash tree item AND groupbox for a config.

        Args:
            config_name: Name of the config (e.g., 'well_filter_config')
            dataclass_type: The dataclass type (for tree matching - more reliable than name)
        """
        from PyQt6.QtGui import QColor
        from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme

        scope_id = getattr(self, 'scope_id', None)
        if not scope_id:
            return

        color_scheme = get_scope_color_scheme(scope_id)
        border_rgb = color_scheme.orchestrator_item_border_rgb
        flash_color = QColor(*border_rgb, 200)

        # 1. Flash the tree item (if tree exists)
        tree_widget = getattr(self, 'tree_widget', None) or getattr(self, 'hierarchy_tree', None)
        if tree_widget is not None:
            # Prefer matching by class type (tree stores "class" in item data)
            item = self._find_tree_item_by_class(dataclass_type, tree_widget) if dataclass_type else None
            # Fall back to field_name matching
            if item is None:
                item = self._find_tree_item_by_field_name(config_name, tree_widget)
            if item:
                from openhcs.pyqt_gui.widgets.shared.tree_item_flash_animation import flash_tree_item
                flash_tree_item(tree_widget, item, flash_color)

        # 2. Flash the groupbox
        self._flash_groupbox_for_field(config_name)
    
    def _find_tree_item_by_class(self, dataclass_type: type, tree_widget: QTreeWidget, parent_item: Optional[QTreeWidgetItem] = None) -> Optional[QTreeWidgetItem]:
        """Recursively find tree item by dataclass type (handles Lazy variants)."""
        if parent_item is None:
            for i in range(tree_widget.topLevelItemCount()):
                result = self._find_tree_item_by_class(dataclass_type, tree_widget, tree_widget.topLevelItem(i))
                if result:
                    return result
            return None

        data = parent_item.data(0, Qt.ItemDataRole.UserRole)
        if data:
            tree_class = data.get('class')
            # Match by: exact type, subclass, or base class (handles LazyX vs X)
            if tree_class and (tree_class == dataclass_type or
                               issubclass(dataclass_type, tree_class) or
                               issubclass(tree_class, dataclass_type)):
                return parent_item

        for i in range(parent_item.childCount()):
            result = self._find_tree_item_by_class(dataclass_type, tree_widget, parent_item.child(i))
            if result:
                return result
        return None

    def _find_tree_item_by_field_name(self, field_name: str, tree_widget: QTreeWidget, parent_item: Optional[QTreeWidgetItem] = None) -> Optional[QTreeWidgetItem]:
        """Recursively find tree item by field_name (fallback for non-dataclass items)."""
        if parent_item is None:
            for i in range(tree_widget.topLevelItemCount()):
                result = self._find_tree_item_by_field_name(field_name, tree_widget, tree_widget.topLevelItem(i))
                if result:
                    return result
            return None

        data = parent_item.data(0, Qt.ItemDataRole.UserRole)
        if data and data.get('field_name') == field_name:
            return parent_item

        for i in range(parent_item.childCount()):
            result = self._find_tree_item_by_field_name(field_name, tree_widget, parent_item.child(i))
            if result:
                return result
        return None

