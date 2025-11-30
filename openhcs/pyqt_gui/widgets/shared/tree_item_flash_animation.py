"""Flash animation for QTreeWidgetItem updates."""

import logging
from typing import Optional
from PyQt6.QtWidgets import QTreeWidget, QTreeWidgetItem
from PyQt6.QtGui import QColor, QBrush, QFont

from .smooth_flash_base import SmoothFlashAnimatorBase
from .scope_visual_config import ScopeVisualConfig

logger = logging.getLogger(__name__)


class TreeItemFlashAnimator(SmoothFlashAnimatorBase):
    """Smooth flash animation for QTreeWidgetItem background and font changes.

    Design:
    - Does NOT store item references (items can be destroyed during flash)
    - Stores (tree_widget, item_id) for item lookup
    - Gracefully handles item destruction (checks if item exists before restoring)
    - Flashes both background color AND font weight for visibility
    """

    def __init__(
        self,
        tree_widget: QTreeWidget,
        item: QTreeWidgetItem,
        flash_color: QColor
    ):
        """Initialize animator.

        Args:
            tree_widget: Parent tree widget
            item: Tree item to flash
            flash_color: Color to flash with
        """
        self.tree_widget = tree_widget
        self.item_id = id(item)  # Store ID, not reference

        # Store original state when animator is created
        self.original_background = item.background(0)
        self.original_font = item.font(0)
        original_color = self.original_background.color() if self.original_background.style() else QColor(255, 255, 255, 0)

        super().__init__(flash_color, original_color)

    def _find_item(self) -> Optional[QTreeWidgetItem]:
        """Find tree item by ID (handles item recreation)."""
        def search_tree(parent_item=None):
            if parent_item is None:
                for i in range(self.tree_widget.topLevelItemCount()):
                    item = self.tree_widget.topLevelItem(i)
                    if id(item) == self.item_id:
                        return item
                    result = search_tree(item)
                    if result:
                        return result
            else:
                for i in range(parent_item.childCount()):
                    child = parent_item.child(i)
                    if id(child) == self.item_id:
                        return child
                    result = search_tree(child)
                    if result:
                        return result
            return None
        return search_tree()

    def _can_flash(self) -> bool:
        """Check if item still exists."""
        return self._find_item() is not None

    def _prepare_flash(self) -> None:
        """Apply bold font on first flash."""
        item = self._find_item()
        if item:
            flash_font = QFont(self.original_font)
            flash_font.setBold(True)
            item.setFont(0, flash_font)

    def _apply_color(self, color: QColor) -> None:
        """Apply interpolated color to tree item."""
        item = self._find_item()
        if item is None:
            return
        item.setBackground(0, QBrush(color))
        self.tree_widget.viewport().update()

    def _on_animation_complete(self) -> None:
        """Restore original background and font."""
        item = self._find_item()
        if item is not None:
            item.setBackground(0, self.original_background)
            item.setFont(0, self.original_font)
            self.tree_widget.viewport().update()
        logger.debug(f"✅ Smooth flash complete for tree item")


# Global registry of animators (keyed by (tree_widget_id, item_id))
_tree_item_animators: dict[tuple[int, int], TreeItemFlashAnimator] = {}


def flash_tree_item(
    tree_widget: QTreeWidget,
    item: QTreeWidgetItem,
    flash_color: QColor
) -> None:
    """Flash a tree item to indicate update.

    Args:
        tree_widget: Tree widget containing the item
        item: Tree item to flash
        flash_color: Color to flash with
    """
    logger.info(f"🔥 flash_tree_item called for item: {item.text(0)}")

    config = ScopeVisualConfig()
    if not config.LIST_ITEM_FLASH_ENABLED:  # Reuse list item flash config
        logger.info(f"🔥 Flash DISABLED in config")
        return

    if item is None:
        logger.info(f"🔥 Item is None")
        return

    logger.info(f"🔥 Creating/getting animator for tree item")

    key = (id(tree_widget), id(item))

    # Get or create animator
    if key not in _tree_item_animators:
        logger.info(f"🔥 Creating NEW animator for tree item")
        _tree_item_animators[key] = TreeItemFlashAnimator(
            tree_widget, item, flash_color
        )
    else:
        logger.info(f"🔥 Reusing existing animator for tree item")
        # Update flash color in case it changed
        animator = _tree_item_animators[key]
        animator.flash_color = flash_color

    animator = _tree_item_animators[key]
    logger.info(f"🔥 Calling animator.flash_update() for tree item")
    animator.flash_update()


def clear_all_tree_animators(tree_widget: QTreeWidget) -> None:
    """Clear all animators for a specific tree widget.

    Call this before clearing/rebuilding the tree to prevent
    flash animations from accessing destroyed items.

    Args:
        tree_widget: Tree widget whose animators should be cleared
    """
    widget_id = id(tree_widget)
    keys_to_remove = [k for k in _tree_item_animators.keys() if k[0] == widget_id]

    for key in keys_to_remove:
        animator = _tree_item_animators[key]
        animator.stop()  # Stop all animations
        del _tree_item_animators[key]

    if keys_to_remove:
        logger.debug(f"Cleared {len(keys_to_remove)} flash animators for tree widget")

