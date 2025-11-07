"""
Shared helpers for rendering configuration hierarchy trees in the PyQt6 GUI.

Both the pipeline ConfigWindow and the StepParameterEditor need to display the
same inheritance-aware tree that highlights which dataclass sections are
editable and which are inherited. This module centralizes the logic so the UI
widgets only need to provide their dataclass inputs and navigation callbacks.
"""

from __future__ import annotations

from dataclasses import fields, is_dataclass
from typing import Dict, Type

from PyQt6.QtCore import Qt
from PyQt6.QtGui import QColor
from PyQt6.QtWidgets import QTreeWidget, QTreeWidgetItem

from openhcs.core.lazy_placeholder_simplified import LazyDefaultPlaceholderService


class ConfigHierarchyTreeHelper:
    """Utility for building configuration hierarchy trees."""

    _INHERITANCE_TOOLTIP = "This configuration is not editable in the UI (inherited by other configs)"

    def create_tree_widget(
        self,
        *,
        header_label: str = "Configuration Hierarchy",
        minimum_width: int = 0,  # Allow collapsing to 0 for splitter
    ) -> QTreeWidget:
        """Create a pre-configured QTreeWidget for hierarchy display."""
        tree = QTreeWidget()
        tree.setHeaderLabel(header_label)
        tree.setMinimumWidth(minimum_width)  # 0 allows free movement in splitter
        tree.setExpandsOnDoubleClick(False)
        return tree

    def populate_from_root_dataclass(
        self,
        tree: QTreeWidget,
        root_dataclass: Type,
        *,
        skip_root_ui_hidden: bool = True,
    ) -> None:
        """Populate the tree using the children of a root dataclass."""
        if not is_dataclass(root_dataclass):
            return

        self._add_ui_visible_dataclasses_to_tree(
            parent_item=tree,
            dataclass_type=root_dataclass,
            is_root=True,
            skip_root_ui_hidden=skip_root_ui_hidden,
        )

    def populate_from_mapping(
        self,
        tree: QTreeWidget,
        dataclass_mapping: Dict[str, Type],
    ) -> None:
        """Populate the tree given a dict of field_name -> dataclass type."""
        for field_name, dataclass_type in dataclass_mapping.items():
            base_type = self.get_base_type(dataclass_type)
            label = getattr(base_type, "__name__", field_name)

            item = QTreeWidgetItem([label])
            item.setData(
                0,
                Qt.ItemDataRole.UserRole,
                {
                    "type": "dataclass",
                    "class": dataclass_type,
                    "field_name": field_name,
                    "ui_hidden": False,
                },
            )
            tree.addTopLevelItem(item)
            self.add_inheritance_info(item, base_type)

    # ------------------------------------------------------------------
    # Internal helpers shared by both population strategies
    # ------------------------------------------------------------------

    def _add_ui_visible_dataclasses_to_tree(
        self,
        parent_item,
        dataclass_type: Type,
        *,
        is_root: bool = False,
        skip_root_ui_hidden: bool = True,
    ) -> None:
        """Recursively add dataclass children that are shown in the UI."""
        for field in fields(dataclass_type):
            field_type = field.type
            if not is_dataclass(field_type):
                continue

            base_type = self.get_base_type(field_type)
            display_name = getattr(base_type, "__name__", field.name)
            ui_hidden = self.is_field_ui_hidden(dataclass_type, field.name, field_type)

            if is_root and skip_root_ui_hidden and ui_hidden:
                continue

            label = display_name if is_root else f"{field.name} ({display_name})"

            item = QTreeWidgetItem([label])
            item.setData(
                0,
                Qt.ItemDataRole.UserRole,
                {
                    "type": "dataclass",
                    "class": field_type,
                    "field_name": field.name,
                    "ui_hidden": ui_hidden,
                },
            )

            if ui_hidden:
                font = item.font(0)
                font.setItalic(True)
                item.setFont(0, font)
                item.setForeground(0, QColor(128, 128, 128))
                item.setToolTip(0, self._INHERITANCE_TOOLTIP)

            if isinstance(parent_item, QTreeWidget):
                parent_item.addTopLevelItem(item)
            else:
                parent_item.addChild(item)

            self.add_inheritance_info(item, base_type)
            self._add_ui_visible_dataclasses_to_tree(
                parent_item=item,
                dataclass_type=base_type,
                is_root=False,
                skip_root_ui_hidden=False,
            )

    def is_field_ui_hidden(
        self,
        dataclass_type: Type,
        field_name: str,
        field_type: Type,
    ) -> bool:
        """Return True if a field should be hidden in the tree."""
        try:
            field_obj = next(f for f in fields(dataclass_type) if f.name == field_name)
            if field_obj.metadata.get("ui_hidden", False):
                return True
        except (StopIteration, TypeError):
            pass

        base_type = self.get_base_type(field_type)
        if (
            hasattr(base_type, "__dict__")
            and "_ui_hidden" in base_type.__dict__
            and base_type._ui_hidden
        ):
            return True

        return False

    def get_base_type(self, dataclass_type: Type) -> Type:
        """Return the non-lazy base type for a dataclass."""
        if LazyDefaultPlaceholderService.has_lazy_resolution(dataclass_type):
            for base in dataclass_type.__bases__:
                if (
                    base.__name__ != "object"
                    and not LazyDefaultPlaceholderService.has_lazy_resolution(base)
                ):
                    return base

        return dataclass_type

    def add_inheritance_info(
        self,
        parent_item: QTreeWidgetItem,
        dataclass_type: Type,
    ) -> None:
        """Append inheritance information beneath the provided tree item."""
        direct_bases = []
        for cls in dataclass_type.__bases__:
            if cls.__name__ == "object":
                continue
            if not hasattr(cls, "__dataclass_fields__"):
                continue

            base_type = self.get_base_type(cls)
            direct_bases.append(base_type)

        for base_class in direct_bases:
            ui_hidden = (
                hasattr(base_class, "__dict__")
                and "_ui_hidden" in base_class.__dict__
                and base_class._ui_hidden
            )

            base_item = QTreeWidgetItem([base_class.__name__])
            base_item.setData(
                0,
                Qt.ItemDataRole.UserRole,
                {
                    "type": "inheritance_link",
                    "target_class": base_class,
                    "ui_hidden": ui_hidden,
                },
            )

            if ui_hidden:
                font = base_item.font(0)
                font.setItalic(True)
                base_item.setFont(0, font)
                base_item.setForeground(0, QColor(128, 128, 128))
                base_item.setToolTip(0, self._INHERITANCE_TOOLTIP)

            parent_item.addChild(base_item)
            self.add_inheritance_info(base_item, base_class)
