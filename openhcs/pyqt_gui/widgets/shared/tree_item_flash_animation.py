"""Flash animation for QTreeWidgetItem updates."""

import logging
from typing import Optional
from PyQt6.QtCore import QTimer
from PyQt6.QtWidgets import QTreeWidget, QTreeWidgetItem
from PyQt6.QtGui import QColor, QBrush, QFont

from .scope_visual_config import ScopeVisualConfig

logger = logging.getLogger(__name__)


class TreeItemFlashAnimator:
    """Manages flash animation for QTreeWidgetItem background and font changes.
    
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
        self.flash_color = flash_color
        self.config = ScopeVisualConfig()
        self._flash_timer: Optional[QTimer] = None
        self._is_flashing: bool = False
        
        # Store original state when animator is created
        self.original_background = item.background(0)
        self.original_font = item.font(0)

    def flash_update(self, use_coordinator: bool = True) -> None:
        """Trigger flash animation on item background and font.

        Args:
            use_coordinator: If True, schedule restoration via coordinator to prevent event loop blocking.
        """
        # Find item by searching tree (item might have been recreated)
        item = self._find_item()
        if item is None:  # Item was destroyed
            logger.debug(f"Flash skipped - tree item was destroyed")
            return

        # Apply flash color AND make font bold for visibility
        item.setBackground(0, QBrush(self.flash_color))
        flash_font = QFont(self.original_font)
        flash_font.setBold(True)
        item.setFont(0, flash_font)

        # Force tree widget to repaint
        self.tree_widget.viewport().update()

        if self._is_flashing:
            # Already flashing - cancel old timer if using coordinator
            if use_coordinator:
                if self._flash_timer:
                    self._flash_timer.stop()
            else:
                # Using local timer, just restart it
                if self._flash_timer:
                    self._flash_timer.stop()
                    self._flash_timer.start(self.config.FLASH_DURATION_MS)
            return

        self._is_flashing = True

        # PERFORMANCE: Schedule restoration via coordinator instead of local timer
        if use_coordinator:
            try:
                from openhcs.pyqt_gui.widgets.shared.parameter_form_manager import ParameterFormManager
                ParameterFormManager.schedule_flash_restoration(self, self.config.FLASH_DURATION_MS)
                logger.debug(f"   Scheduled tree item restoration via coordinator ({self.config.FLASH_DURATION_MS}ms)")
            except ImportError:
                use_coordinator = False

        if not use_coordinator:
            # Fallback to local timer
            self._flash_timer = QTimer(self.tree_widget)
            self._flash_timer.setSingleShot(True)
            self._flash_timer.timeout.connect(self._restore_original)
            self._flash_timer.start(self.config.FLASH_DURATION_MS)

    def _find_item(self) -> Optional[QTreeWidgetItem]:
        """Find tree item by ID (handles item recreation)."""
        # Search all items in tree
        def search_tree(parent_item=None):
            if parent_item is None:
                # Search top-level items
                for i in range(self.tree_widget.topLevelItemCount()):
                    item = self.tree_widget.topLevelItem(i)
                    if id(item) == self.item_id:
                        return item
                    result = search_tree(item)
                    if result:
                        return result
            else:
                # Search children
                for i in range(parent_item.childCount()):
                    child = parent_item.child(i)
                    if id(child) == self.item_id:
                        return child
                    result = search_tree(child)
                    if result:
                        return result
            return None
        
        return search_tree()

    def _restore_original(self) -> None:
        """Restore original background and font."""
        item = self._find_item()
        if item is None:  # Item was destroyed during flash
            logger.debug(f"Flash restore skipped - tree item was destroyed")
            self._is_flashing = False
            return

        # Restore original state
        item.setBackground(0, self.original_background)
        item.setFont(0, self.original_font)
        self.tree_widget.viewport().update()
        
        self._is_flashing = False


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
    logger.debug(f"🔥 flash_tree_item called for item: {item.text(0)}")

    config = ScopeVisualConfig()
    if not config.LIST_ITEM_FLASH_ENABLED:  # Reuse list item flash config
        logger.debug(f"🔥 Flash DISABLED in config")
        return

    if item is None:
        logger.debug(f"🔥 Item is None")
        return

    logger.debug(f"🔥 Creating/getting animator for tree item")

    key = (id(tree_widget), id(item))

    # Get or create animator
    if key not in _tree_item_animators:
        logger.debug(f"🔥 Creating NEW animator for tree item")
        _tree_item_animators[key] = TreeItemFlashAnimator(
            tree_widget, item, flash_color
        )
    else:
        logger.debug(f"🔥 Reusing existing animator for tree item")
        # Update flash color in case it changed
        animator = _tree_item_animators[key]
        animator.flash_color = flash_color

    animator = _tree_item_animators[key]
    logger.debug(f"🔥 Calling animator.flash_update() for tree item")
    animator.flash_update()


def clear_all_tree_animators(tree_widget: QTreeWidget) -> None:
    """Clear all animators for a specific tree widget.
    
    Call this before clearing/rebuilding the tree to prevent
    flash timers from accessing destroyed items.
    
    Args:
        tree_widget: Tree widget whose animators should be cleared
    """
    widget_id = id(tree_widget)
    keys_to_remove = [k for k in _tree_item_animators.keys() if k[0] == widget_id]
    
    for key in keys_to_remove:
        animator = _tree_item_animators[key]
        # Stop any active flash timers
        if animator._flash_timer and animator._flash_timer.isActive():
            animator._flash_timer.stop()
        del _tree_item_animators[key]
    
    if keys_to_remove:
        logger.debug(f"Cleared {len(keys_to_remove)} flash animators for tree widget")

