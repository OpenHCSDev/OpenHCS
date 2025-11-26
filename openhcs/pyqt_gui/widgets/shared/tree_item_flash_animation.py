"""Flash animation for QTreeWidgetItem updates.

Uses QVariantAnimation for smooth 60fps color transitions:
- Rapid fade-in (~100ms) with OutQuad easing
- Hold at max flash while rapid updates continue
- Smooth fade-out (~350ms) with InOutCubic easing when updates stop
"""

import logging
from typing import Optional
from PyQt6.QtCore import QVariantAnimation, QEasingCurve, QTimer
from PyQt6.QtWidgets import QTreeWidget, QTreeWidgetItem
from PyQt6.QtGui import QColor, QBrush, QFont

from .scope_visual_config import ScopeVisualConfig

logger = logging.getLogger(__name__)


class TreeItemFlashAnimator:
    """Manages smooth flash animation for QTreeWidgetItem background and font changes.

    Uses QVariantAnimation for 60fps color interpolation with:
    - Rapid fade-in: 100ms with OutQuad easing (quick snap to flash color)
    - Hold at max: stays at flash color while rapid updates continue
    - Smooth fade-out: 350ms with InOutCubic easing (when updates stop)

    Design:
    - Does NOT store item references (items can be destroyed during flash)
    - Stores (tree_widget, item_id) for item lookup
    - Gracefully handles item destruction (checks if item exists before restoring)
    - Flashes both background color AND font weight for visibility
    """

    # Animation timing constants
    FADE_IN_DURATION_MS: int = 100   # Rapid fade-in
    FADE_OUT_DURATION_MS: int = 350  # Smooth fade-out
    HOLD_DURATION_MS: int = 150      # Hold at max flash before fade-out

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
        self._is_flashing: bool = False

        # Store original state when animator is created
        self.original_background = item.background(0)
        self.original_font = item.font(0)
        # Extract original color from brush
        self._original_color = self.original_background.color() if self.original_background.style() else QColor(0, 0, 0, 0)

        # Create fade-in animation
        self._fade_in_anim = QVariantAnimation()
        self._fade_in_anim.setDuration(self.FADE_IN_DURATION_MS)
        self._fade_in_anim.setEasingCurve(QEasingCurve.Type.OutQuad)
        self._fade_in_anim.valueChanged.connect(self._apply_color)
        self._fade_in_anim.finished.connect(self._on_fade_in_complete)

        # Create fade-out animation
        self._fade_out_anim = QVariantAnimation()
        self._fade_out_anim.setDuration(self.FADE_OUT_DURATION_MS)
        self._fade_out_anim.setEasingCurve(QEasingCurve.Type.InOutCubic)
        self._fade_out_anim.valueChanged.connect(self._apply_color)
        self._fade_out_anim.finished.connect(self._on_animation_complete)

        # Hold timer - resets on each flash, starts fade-out when expires
        self._hold_timer = QTimer()
        self._hold_timer.setSingleShot(True)
        self._hold_timer.timeout.connect(self._start_fade_out)

    def flash_update(self, use_coordinator: bool = False) -> None:  # noqa: ARG002
        """Trigger smooth flash animation on item background and font.

        Args:
            use_coordinator: Ignored (kept for API compatibility). Animations are self-contained.
        """
        del use_coordinator  # Unused, kept for API compatibility
        item = self._find_item()
        if item is None:
            return

        # If already flashing, just reset the hold timer (stay at max flash)
        if self._is_flashing:
            self._hold_timer.stop()
            self._fade_out_anim.stop()
            # Ensure we're at max flash color
            self._apply_color(self.flash_color)
            self._hold_timer.start(self.HOLD_DURATION_MS)
            return

        # First flash - set bold font and start fade-in
        self._is_flashing = True

        flash_font = QFont(self.original_font)
        flash_font.setBold(True)
        item.setFont(0, flash_font)

        # Start fade-in: original -> flash color
        self._fade_in_anim.setStartValue(self._original_color)
        self._fade_in_anim.setEndValue(self.flash_color)
        self._fade_in_anim.start()

    def _on_fade_in_complete(self) -> None:
        """Called when fade-in completes. Start hold timer."""
        self._hold_timer.start(self.HOLD_DURATION_MS)

    def _start_fade_out(self) -> None:
        """Called when hold timer expires. Start fade-out animation."""
        self._fade_out_anim.setStartValue(self.flash_color)
        self._fade_out_anim.setEndValue(self._original_color)
        self._fade_out_anim.start()

    def _apply_color(self, color: QColor) -> None:
        """Apply interpolated color to tree item. Called ~60 times/sec during animation."""
        item = self._find_item()
        if item is None:
            return
        item.setBackground(0, QBrush(color))
        self.tree_widget.viewport().update()

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

    def _on_animation_complete(self) -> None:
        """Called when fade-out completes. Restore original state."""
        self._is_flashing = False
        item = self._find_item()
        if item is None:
            return
        item.setBackground(0, self.original_background)
        item.setFont(0, self.original_font)
        self.tree_widget.viewport().update()

    def _restore_original(self) -> None:
        """Immediate restoration (for cleanup/cancellation)."""
        self._fade_in_anim.stop()
        self._fade_out_anim.stop()
        self._on_animation_complete()

    def stop(self) -> None:
        """Stop all animations immediately."""
        self._fade_in_anim.stop()
        self._fade_out_anim.stop()
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
    animations from accessing destroyed items.

    Args:
        tree_widget: Tree widget whose animators should be cleared
    """
    widget_id = id(tree_widget)
    keys_to_remove = [k for k in _tree_item_animators.keys() if k[0] == widget_id]

    for key in keys_to_remove:
        animator = _tree_item_animators[key]
        animator.stop()
        del _tree_item_animators[key]

    if keys_to_remove:
        logger.debug(f"Cleared {len(keys_to_remove)} flash animators for tree widget")

