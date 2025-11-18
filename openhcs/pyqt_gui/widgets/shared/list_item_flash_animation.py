"""Flash animation for QListWidgetItem updates."""

import logging
from typing import Optional
from PyQt6.QtCore import QTimer
from PyQt6.QtWidgets import QListWidget
from PyQt6.QtGui import QColor

from .scope_visual_config import ScopeVisualConfig, ListItemType

logger = logging.getLogger(__name__)


class ListItemFlashAnimator:
    """Manages flash animation for QListWidgetItem background color changes.
    
    Design:
    - Does NOT store item references (items can be destroyed during flash)
    - Stores (list_widget, row, scope_id, item_type) for color recomputation
    - Gracefully handles item destruction (checks if item exists before restoring)
    """

    def __init__(
        self,
        list_widget: QListWidget,
        row: int,
        scope_id: str,
        item_type: ListItemType
    ):
        """Initialize animator.

        Args:
            list_widget: Parent list widget
            row: Row index of item
            scope_id: Scope identifier for color recomputation
            item_type: Type of list item (orchestrator or step)
        """
        self.list_widget = list_widget
        self.row = row
        self.scope_id = scope_id
        self.item_type = item_type
        self.config = ScopeVisualConfig()
        self._flash_timer: Optional[QTimer] = None
        self._is_flashing: bool = False

    def flash_update(self) -> None:
        """Trigger flash animation on item background by increasing opacity."""
        logger.info(f"🔥 flash_update called for row {self.row}")

        item = self.list_widget.item(self.row)
        if item is None:  # Item was destroyed
            logger.info(f"🔥 Flash skipped - item at row {self.row} no longer exists")
            return

        # Get the correct background color from scope
        from .scope_color_utils import get_scope_color_scheme
        color_scheme = get_scope_color_scheme(self.scope_id)
        correct_color = self.item_type.get_background_color(color_scheme)

        logger.info(f"🔥 correct_color={correct_color}, item_type={self.item_type}")

        if correct_color is not None:
            # Flash by increasing opacity to 100% (same color, just full opacity)
            flash_color = QColor(correct_color)
            flash_color.setAlpha(127)  # Full opacity
            logger.info(f"🔥 Setting flash color: {flash_color.name()} alpha={flash_color.alpha()}")
            item.setBackground(flash_color)

        if self._is_flashing:
            # Already flashing - restart timer (flash color already re-applied above)
            logger.info(f"🔥 Already flashing - restarting timer")
            if self._flash_timer:
                self._flash_timer.stop()
                self._flash_timer.start(self.config.FLASH_DURATION_MS)
            return

        logger.info(f"🔥 Starting NEW flash animation")
        self._is_flashing = True

        # Setup timer to restore correct background
        self._flash_timer = QTimer(self.list_widget)
        self._flash_timer.setSingleShot(True)
        self._flash_timer.timeout.connect(self._restore_background)
        self._flash_timer.start(self.config.FLASH_DURATION_MS)
        logger.info(f"🔥 Flash timer started for {self.config.FLASH_DURATION_MS}ms")

    def _restore_background(self) -> None:
        """Restore correct background color by recomputing from scope."""
        item = self.list_widget.item(self.row)
        if item is None:  # Item was destroyed during flash
            logger.debug(f"Flash restore skipped - item at row {self.row} was destroyed")
            self._is_flashing = False
            return

        # Recompute correct color from scope_id (handles list rebuilds during flash)
        from PyQt6.QtGui import QBrush
        from .scope_color_utils import get_scope_color_scheme
        color_scheme = get_scope_color_scheme(self.scope_id)

        # Use enum-based polymorphic dispatch to get correct color
        correct_color = self.item_type.get_background_color(color_scheme)

        # Handle None (transparent) background
        if correct_color is None:
            item.setBackground(QBrush())  # Empty brush = transparent
        else:
            item.setBackground(correct_color)

        self._is_flashing = False


# Global registry of animators (keyed by (list_widget_id, item_row))
_list_item_animators: dict[tuple[int, int], ListItemFlashAnimator] = {}


def flash_list_item(
    list_widget: QListWidget,
    row: int,
    scope_id: str,
    item_type: ListItemType
) -> None:
    """Flash a list item to indicate update.

    Args:
        list_widget: List widget containing the item
        row: Row index of item to flash
        scope_id: Scope identifier for color recomputation
        item_type: Type of list item (orchestrator or step)
    """
    logger.info(f"🔥 flash_list_item called: row={row}, scope_id={scope_id}, item_type={item_type}")

    config = ScopeVisualConfig()
    if not config.LIST_ITEM_FLASH_ENABLED:
        logger.info(f"🔥 Flash DISABLED in config")
        return

    item = list_widget.item(row)
    if item is None:
        logger.info(f"🔥 Item at row {row} is None")
        return

    logger.info(f"🔥 Creating/getting animator for row {row}")

    key = (id(list_widget), row)

    # Get or create animator
    if key not in _list_item_animators:
        logger.info(f"🔥 Creating NEW animator for row {row}")
        _list_item_animators[key] = ListItemFlashAnimator(
            list_widget, row, scope_id, item_type
        )
    else:
        logger.info(f"🔥 Reusing existing animator for row {row}")
        # Update scope_id and item_type in case item was recreated
        animator = _list_item_animators[key]
        animator.scope_id = scope_id
        animator.item_type = item_type

    animator = _list_item_animators[key]
    logger.info(f"🔥 Calling animator.flash_update() for row {row}")
    animator.flash_update()


def clear_all_animators(list_widget: QListWidget) -> None:
    """Clear all animators for a specific list widget.
    
    Call this before clearing/rebuilding the list to prevent
    flash timers from accessing destroyed items.
    
    Args:
        list_widget: List widget whose animators should be cleared
    """
    widget_id = id(list_widget)
    keys_to_remove = [k for k in _list_item_animators.keys() if k[0] == widget_id]
    
    for key in keys_to_remove:
        animator = _list_item_animators[key]
        # Stop any active flash timers
        if animator._flash_timer and animator._flash_timer.isActive():
            animator._flash_timer.stop()
        del _list_item_animators[key]
    
    if keys_to_remove:
        logger.debug(f"Cleared {len(keys_to_remove)} flash animators for list widget")

