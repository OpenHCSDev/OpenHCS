"""
Shared helpers for rendering configuration hierarchy trees in the PyQt6 GUI.

Both the pipeline ConfigWindow and the StepParameterEditor need to display the
same inheritance-aware tree that highlights which dataclass sections are
editable and which are inherited. This module centralizes the logic so the UI
widgets only need to provide their dataclass inputs and navigation callbacks.
"""

from __future__ import annotations

import logging
from dataclasses import fields, is_dataclass
from typing import Dict, Type, Optional, Iterable

from PyQt6.QtCore import Qt, QRect
from PyQt6.QtGui import QColor, QPainter, QFont, QFontMetrics
from PyQt6.QtWidgets import QTreeWidget, QTreeWidgetItem, QStyledItemDelegate, QStyleOptionViewItem, QStyle

logger = logging.getLogger(__name__)

# Custom data role for flash key (matches list_item_delegate pattern)
TREE_FLASH_KEY_ROLE = Qt.ItemDataRole.UserRole + 20


class TreeItemFlashDelegate(QStyledItemDelegate):
    """Custom delegate for tree items with flash behind text.

    TRUE O(1) ARCHITECTURE: Flash lookup uses pre-computed colors from GlobalFlashCoordinator.
    This delegate draws flash BEHIND text (like MultilinePreviewItemDelegate for list items)
    so text remains readable during flash animations.
    """

    def __init__(self, parent=None, manager=None):
        """Initialize delegate.

        Args:
            parent: Parent widget (QTreeWidget)
            manager: Flash manager with get_flash_color_for_key() method
        """
        super().__init__(parent)
        self._manager = manager

    def paint(self, painter: QPainter, option: QStyleOptionViewItem, index) -> None:
        """Paint tree item with flash BEHIND text."""
        # Prepare a copy to let style draw backgrounds, hover, selection, etc.
        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)

        # Capture text and prevent default text draw
        text = opt.text or ""
        opt.text = ""

        # Draw flash background BEHIND text (inside item rect)
        flash_key = index.data(TREE_FLASH_KEY_ROLE)
        if flash_key and self._manager is not None:
            flash_color = self._manager.get_flash_color_for_key(flash_key)
            if flash_color and flash_color.alpha() > 0:
                # Override flash color to match window's scope color scheme
                # Find parent window with _scope_color_scheme
                window = self.parent()
                while window is not None:
                    scheme = getattr(window, '_scope_color_scheme', None)
                    if scheme:
                        from pyqt_formgen.widgets.shared.scope_color_utils import tint_color_perceptual
                        base_rgb = getattr(scheme, 'base_color_rgb', None)
                        layers = getattr(scheme, 'step_border_layers', None)
                        if base_rgb and layers:
                            _, tint_idx, _ = (layers[0] + ("solid",))[:3]
                            scheme_color = tint_color_perceptual(base_rgb, tint_idx).darker(120)
                            # Keep animation alpha from coordinator
                            flash_color = QColor(scheme_color.red(), scheme_color.green(),
                                                scheme_color.blue(), flash_color.alpha())
                        break
                    window = window.parent() if hasattr(window, 'parent') else None
                painter.fillRect(option.rect, flash_color)

        # Let the style draw selection, hover, backgrounds (except text)
        self.parent().style().drawControl(QStyle.ControlElement.CE_ItemViewItem, opt, painter, self.parent())

        # Now draw text manually ON TOP of flash
        painter.save()

        # Determine text color based on selection state
        is_selected = option.state & QStyle.StateFlag.State_Selected

        # Get font from option
        font = QFont(option.font)

        # Check if item is italic (ui_hidden items use italic)
        item_font = index.data(Qt.ItemDataRole.FontRole)
        if item_font:
            font = QFont(item_font)

        painter.setFont(font)
        fm = QFontMetrics(font)

        # Calculate text position
        # Qt's option.rect is already indented for depth, just add small padding for branch indicator
        text_rect = option.rect
        x_offset = text_rect.left() + 2  # 2px padding after branch indicator
        y_offset = text_rect.top() + fm.ascent() + (text_rect.height() - fm.height()) // 2

        # Determine text color
        if is_selected:
            color = option.palette.highlightedText().color()
        else:
            # Check for custom foreground (ui_hidden items use gray)
            fg = index.data(Qt.ItemDataRole.ForegroundRole)
            if fg:
                color = fg.color() if hasattr(fg, 'color') else QColor(fg)
            else:
                color = option.palette.text().color()

        painter.setPen(color)
        painter.drawText(x_offset, y_offset, text)

        painter.restore()


class ConfigHierarchyTreeHelper:
    """Utility for building configuration hierarchy trees.

    TRUE O(1) FLASH ARCHITECTURE: Tree items are registered with WindowFlashOverlay
    during population. Flash rendering happens in the window overlay's single paintEvent.

    UNIFIED DIRTY TRACKING: Automatically subscribes to ObjectState.on_state_changed()
    when state is provided, and updates tree item styling reactively.
    """

    _INHERITANCE_TOOLTIP = "This configuration is not editable in the UI (inherited by other configs)"

    def __init__(self):
        self._flash_manager = None
        self._current_tree: Optional[QTreeWidget] = None
        # Mapping from dotted path to QTreeWidgetItem for dirty styling updates
        self._path_to_item: Dict[str, QTreeWidgetItem] = {}
        self._dirty_callback = None
        self._tree_for_dirty: Optional[QTreeWidget] = None
        # Dirty tracking subscription
        self._state: Optional['ObjectState'] = None

    def create_tree_widget(
        self,
        *,
        header_label: str = "Configuration Hierarchy",
        minimum_width: int = 0,  # Allow collapsing to 0 for splitter
        flash_manager: Optional['ConfigWindow'] = None,
        state: Optional['ObjectState'] = None,
    ) -> QTreeWidget:
        """Create a pre-configured QTreeWidget for hierarchy display.

        Args:
            header_label: Header text for the tree
            minimum_width: Minimum width (0 allows free splitter movement)
            flash_manager: Manager with register_flash_tree_item() for O(1) flash
            state: ObjectState for automatic dirty tracking subscription
        """
        tree = QTreeWidget()
        tree.setHeaderLabel(header_label)
        tree.setMinimumWidth(minimum_width)  # 0 allows free movement in splitter
        tree.setExpandsOnDoubleClick(False)

        # Store flash manager for use during population
        self._flash_manager = flash_manager
        self._current_tree = tree
        # Fresh mapping per tree build to avoid stale item references
        self._path_to_item = {}
        # Track dirty callbacks per tree to allow rebuilding subscriptions on re-init
        self._tree_for_dirty = tree

        # Install delegate that draws flash BEHIND text
        if flash_manager is not None:
            delegate = TreeItemFlashDelegate(parent=tree, manager=flash_manager)
            tree.setItemDelegate(delegate)

        # Subscribe to dirty state changes for reactive tree styling
        if state is not None:
            self._state = state
            self._subscribe_to_dirty_changes(tree)

        # ASYNC FIX: Re-run dirty styling when async form build completes
        # During async build, nested_managers are populated incrementally, so
        # groupbox dirty markers need to be updated again after all are ready
        if flash_manager is not None and hasattr(flash_manager, '_on_build_complete_callbacks'):
            flash_manager._on_build_complete_callbacks.append(
                lambda: self.initialize_dirty_styling()
            )

        return tree

    def _subscribe_to_dirty_changes(self, tree: QTreeWidget) -> None:
        """Subscribe to ObjectState dirty changes for reactive styling.

        NOTE: This only sets up the subscription. Call initialize_dirty_styling()
        AFTER populating the tree to apply initial dirty state.
        """
        if self._state is None:
            return

        def on_state_changed():
            dirty_fields = self._state.dirty_fields
            self.update_dirty_styling(dirty_fields)
            tree.viewport().update()

        self._state.on_state_changed(on_state_changed)
        self._dirty_callback = on_state_changed
        self._tree_for_dirty = tree  # Store for initialize_dirty_styling

    def initialize_dirty_styling(self) -> None:
        """Apply initial dirty styling based on current state.

        Call this AFTER populating the tree (after _path_to_item is filled).
        """
        if self._state is None:
            return
        dirty_fields = self._state.dirty_fields
        self.update_dirty_styling(dirty_fields)
        if hasattr(self, '_tree_for_dirty') and self._tree_for_dirty:
            self._tree_for_dirty.viewport().update()

    def cleanup_subscriptions(self) -> None:
        """Unsubscribe from ObjectState dirty changes. Call on window close."""
        if self._state is not None:
            if self._dirty_callback is not None:
                self._state.off_state_changed(self._dirty_callback)
                self._dirty_callback = None
            self._state = None

    def apply_scope_background(self, tree: QTreeWidget, scheme) -> None:
        """Apply scope-colored background tint to tree widget.

        Args:
            tree: The QTreeWidget to style
            scheme: ScopeColorScheme with base_color_rgb and step_border_layers
        """
        from pyqt_formgen.widgets.shared.scope_color_utils import tint_color_perceptual
        from pyqt_formgen.widgets.shared.scope_visual_config import ScopeVisualConfig

        base_rgb = getattr(scheme, 'base_color_rgb', None)
        if not base_rgb:
            return

        layers = getattr(scheme, 'step_border_layers', None)
        if layers:
            _, tint_idx, _ = (layers[0] + ("solid",))[:3]
        else:
            tint_idx = 1

        color = tint_color_perceptual(base_rgb, tint_idx)
        opacity = ScopeVisualConfig.TREE_BG_OPACITY

        # Apply via stylesheet (most robust for QTreeWidget)
        r, g, b = color.red(), color.green(), color.blue()
        alpha = int(255 * opacity)
        tree.setStyleSheet(f"""
            QTreeWidget {{
                background-color: rgba({r}, {g}, {b}, {alpha});
            }}
            QTreeWidget::item {{
                background-color: transparent;
            }}
        """)

    def update_dirty_styling(self, dirty_fields: set) -> None:
        """Update tree item AND groupbox styling based on dirty and signature diff fields.

        Two orthogonal visual semantics:
        - Asterisk (*): dirty (resolved_live != resolved_saved)
        - Underline: signature diff (raw != signature default)

        Single source of truth: prefixes computed ONCE and used for both
        tree items and groupbox titles (via flash_manager).
        """
        # Precompute dirty prefixes (for asterisk)
        dirty_prefixes = self._compute_prefixes(dirty_fields)

        # Precompute signature diff prefixes (for underline)
        sig_diff_fields = self._state.signature_diff_fields if self._state else set()
        sig_diff_prefixes = self._compute_prefixes(sig_diff_fields)

        # Update tree items
        seen_items = set()
        for path, item in self._path_to_item.items():
            if id(item) in seen_items:
                continue
            seen_items.add(id(item))

            meta = item.data(0, Qt.ItemDataRole.UserRole) or {}
            field_name = meta.get("field_name")
            class_type = meta.get("class")
            alt_name = self._to_snake_case(getattr(class_type, "__name__", "")) if class_type else None

            is_dirty = self._matches_prefix(path, field_name, alt_name, dirty_prefixes)
            has_sig_diff = self._matches_prefix(path, field_name, alt_name, sig_diff_prefixes)

            # Asterisk for dirty
            current_text = item.text(0)
            has_marker = current_text.startswith("* ")
            if is_dirty and not has_marker:
                item.setText(0, f"* {current_text}")
            elif not is_dirty and has_marker:
                item.setText(0, current_text[2:])  # Remove "* " prefix

            # Underline for signature diff
            font = item.font(0)
            font.setUnderline(has_sig_diff)
            item.setFont(0, font)

        # Update groupbox titles using same prefixes (single source of truth)
        if self._flash_manager is not None:
            self._flash_manager.update_groupbox_dirty_markers(dirty_prefixes, sig_diff_prefixes)

    def _compute_prefixes(self, fields: set) -> set:
        """Compute field paths and all their ancestor prefixes."""
        prefixes = set()
        for field_path in fields:
            parts = field_path.split('.')
            for i in range(1, len(parts) + 1):
                prefixes.add('.'.join(parts[:i]))
        return prefixes

    def _matches_prefix(self, path: str, field_name: str, alt_name: str, prefixes: set) -> bool:
        """Check if any identifier matches the prefix set."""
        return (
            path in prefixes
            or (field_name and field_name in prefixes)
            or (alt_name and alt_name in prefixes)
        )

    def _register_flash_element(self, item: QTreeWidgetItem, field_name: str) -> None:
        """Register tree item for flash rendering.

        Stores SCOPED flash key in item data for delegate lookup, and registers with
        WindowFlashOverlay (with skip_overlay_paint=True since delegate handles painting).

        Tree items use 'tree::' prefix to avoid key collision with groupboxes,
        allowing independent flash control (tree can flash without groupbox and vice versa).
        """
        if self._flash_manager is None or self._current_tree is None:
            return
        if not hasattr(self._flash_manager, 'register_flash_tree_item'):
            return

        # Tree items use separate key namespace to avoid groupbox collision
        tree_key = f"tree::{field_name}"

        # Get scoped key from flash manager (matches what's used for color lookup)
        scoped_key = tree_key
        if hasattr(self._flash_manager, '_get_scoped_flash_key'):
            scoped_key = self._flash_manager._get_scoped_flash_key(tree_key)

        # Store SCOPED flash key in item data for delegate to look up
        item.setData(0, TREE_FLASH_KEY_ROLE, scoped_key)

        tree = self._current_tree
        # Create closure that finds item's current index (handles tree rebuild)
        def get_index():
            return tree.indexFromItem(item)

        self._flash_manager.register_flash_tree_item(tree_key, tree, get_index)

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

        self._current_tree = tree
        self._add_ui_visible_dataclasses_to_tree(
            parent_item=tree,
            obj_type=root_dataclass,
            is_root=True,
            skip_root_ui_hidden=skip_root_ui_hidden,
        )

    def populate_from_mapping(
        self,
        tree: QTreeWidget,
        dataclass_mapping: Dict[str, Type],
    ) -> None:
        """Populate the tree given a dict of field_name -> dataclass type."""
        self._current_tree = tree
        for field_name, obj_type in dataclass_mapping.items():
            base_type = self.get_base_type(obj_type)
            label = getattr(base_type, "__name__", field_name)
            path = field_name
            alt_path = self._to_snake_case(base_type.__name__)

            item = QTreeWidgetItem([label])
            item.setData(
                0,
                Qt.ItemDataRole.UserRole,
                {
                    "type": "dataclass",
                    "class": obj_type,
                    "field_name": field_name,
                    "ui_hidden": False,
                },
            )
            tree.addTopLevelItem(item)
            # Store mapping for dirty styling updates (support both field and snake_case type name)
            self._store_item_paths(item, [path, alt_path])
            # TRUE O(1): Register with WindowFlashOverlay
            self._register_flash_element(item, field_name)
            self.add_inheritance_info(item, base_type)

    # ------------------------------------------------------------------
    # Internal helpers shared by both population strategies
    # ------------------------------------------------------------------

    def _add_ui_visible_dataclasses_to_tree(
        self,
        parent_item,
        obj_type: Type,
        *,
        is_root: bool = False,
        skip_root_ui_hidden: bool = True,
        parent_path: str = "",
    ) -> None:
        """Recursively add dataclass children that are shown in the UI."""
        for field in fields(obj_type):
            field_type = field.type
            if not is_dataclass(field_type):
                continue

            base_type = self.get_base_type(field_type)
            display_name = getattr(base_type, "__name__", field.name)
            ui_hidden = self.is_field_ui_hidden(obj_type, field.name, field_type)

            if is_root and skip_root_ui_hidden and ui_hidden:
                continue

            label = display_name if is_root else f"{field.name} ({display_name})"
            path = field.name if not parent_path else f"{parent_path}.{field.name}"
            alt_name = self._to_snake_case(base_type.__name__)
            alt_path = alt_name if not parent_path else f"{parent_path}.{alt_name}"

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

            # Store mapping for dirty styling updates
            self._store_item_paths(item, [path, alt_path])

            # TRUE O(1): Register with WindowFlashOverlay
            self._register_flash_element(item, field.name)

            self.add_inheritance_info(item, base_type)
            self._add_ui_visible_dataclasses_to_tree(
                parent_item=item,
                obj_type=base_type,
                is_root=False,
                skip_root_ui_hidden=False,
                parent_path=path,
            )

    def _store_item_paths(self, item: QTreeWidgetItem, paths: Iterable[str]) -> None:
        """Store one or more paths for a tree item, skipping empties and duplicates."""
        for path in paths:
            if not path:
                continue
            if path not in self._path_to_item:
                self._path_to_item[path] = item

    @staticmethod
    def _to_snake_case(name: str) -> str:
        """Convert CamelCase/PascalCase to snake_case for matching dirty paths."""
        import re
        if not name:
            return ""
        s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
        return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()

    def is_field_ui_hidden(
        self,
        obj_type: Type,
        field_name: str,
        field_type: Type,
    ) -> bool:
        """Return True if a field should be hidden in the tree."""
        try:
            field_obj = next(f for f in fields(obj_type) if f.name == field_name)
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

    def get_base_type(self, obj_type: Type) -> Type:
        """Return the non-lazy base type for a dataclass.

        If obj_type is a Lazy* class (e.g., LazyVFSConfig), returns its
        non-Lazy base (e.g., VFSConfig). This strips the Lazy wrapper
        so the tree shows clean config names.
        """
        # If name starts with "Lazy", find the non-Lazy base
        if obj_type.__name__.startswith("Lazy"):
            for base in obj_type.__bases__:
                if base.__name__ != "object" and not base.__name__.startswith("Lazy"):
                    return base
        return obj_type

    def add_inheritance_info(
        self,
        parent_item: QTreeWidgetItem,
        obj_type: Type,
    ) -> None:
        """Append inheritance information beneath the provided tree item."""
        direct_bases = []
        for cls in obj_type.__bases__:
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
