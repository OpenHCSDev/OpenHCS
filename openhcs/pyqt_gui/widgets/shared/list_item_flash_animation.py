"""Flash animation for QListWidgetItem updates.

Uses QVariantAnimation for smooth 60fps color transitions:
- Rapid fade-in (~100ms) with OutQuad easing
- Hold at max flash while rapid updates continue
- Smooth fade-out (~350ms) with InOutCubic easing when updates stop
"""

import logging
from typing import Optional
from PyQt6.QtCore import QVariantAnimation, QEasingCurve, QTimer
from PyQt6.QtWidgets import QListWidget
from PyQt6.QtGui import QColor, QBrush

from .scope_visual_config import ScopeVisualConfig, ListItemType

logger = logging.getLogger(__name__)


class ListItemFlashAnimator:
    """Manages smooth flash animation for QListWidgetItem background color changes.

    Uses QVariantAnimation for 60fps color interpolation with:
    - Rapid fade-in: 100ms with OutQuad easing (quick snap to flash color)
    - Hold at max: stays at flash color while rapid updates continue
    - Smooth fade-out: 350ms with InOutCubic easing (when updates stop)

    Design:
    - Does NOT store item references (items can be destroyed during flash)
    - Stores (list_widget, row, scope_id, item_type) for color recomputation
    - Gracefully handles item destruction (checks if item exists before restoring)
    """

    # Animation timing constants
    FADE_IN_DURATION_MS: int = 100   # Rapid fade-in
    FADE_OUT_DURATION_MS: int = 350  # Smooth fade-out
    HOLD_DURATION_MS: int = 150      # Hold at max flash before fade-out
    FLASH_ALPHA: int = 95            # Flash color alpha (high opacity)

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
        self._is_flashing: bool = False
        self._original_color: Optional[QColor] = None
        self._flash_color: Optional[QColor] = None

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

    def flash_update(self) -> None:
        """Trigger smooth flash animation on item background."""
        item = self.list_widget.item(self.row)
        if item is None:
            return

        # If already flashing, just reset the hold timer (stay at max flash)
        if self._is_flashing and self._flash_color is not None:
            self._hold_timer.stop()
            self._fade_out_anim.stop()
            # Ensure we're at max flash color
            self._apply_color(self._flash_color)
            self._hold_timer.start(self.HOLD_DURATION_MS)
            return

        # First flash - capture original and compute flash color
        from .scope_color_utils import get_scope_color_scheme
        color_scheme = get_scope_color_scheme(self.scope_id)
        correct_color = self.item_type.get_background_color(color_scheme)

        self._original_color = correct_color if correct_color else QColor(0, 0, 0, 0)
        if correct_color is not None:
            self._flash_color = QColor(correct_color)
            self._flash_color.setAlpha(self.FLASH_ALPHA)
        else:
            self._flash_color = QColor(144, 238, 144, self.FLASH_ALPHA)

        self._is_flashing = True

        # Start fade-in: original -> flash color
        self._fade_in_anim.setStartValue(self._original_color)
        self._fade_in_anim.setEndValue(self._flash_color)
        self._fade_in_anim.start()

    def _on_fade_in_complete(self) -> None:
        """Called when fade-in completes. Start hold timer."""
        self._hold_timer.start(self.HOLD_DURATION_MS)

    def _start_fade_out(self) -> None:
        """Called when hold timer expires. Start fade-out animation."""
        self._fade_out_anim.setStartValue(self._flash_color)
        self._fade_out_anim.setEndValue(self._original_color)
        self._fade_out_anim.start()

    def _apply_color(self, color: QColor) -> None:
        """Apply interpolated color to list item. Called ~60 times/sec during animation."""
        item = self.list_widget.item(self.row)
        if item is None:
            return
        item.setBackground(color)
        self.list_widget.update()

    def _on_animation_complete(self) -> None:
        """Called when fade-out completes. Restore original state."""
        self._is_flashing = False
        item = self.list_widget.item(self.row)
        if item is None:
            return

        # Recompute correct color (handles list rebuilds during flash)
        from .scope_color_utils import get_scope_color_scheme
        color_scheme = get_scope_color_scheme(self.scope_id)
        correct_color = self.item_type.get_background_color(color_scheme)

        if correct_color is None:
            item.setBackground(QBrush())  # Empty brush = transparent
        else:
            item.setBackground(correct_color)
        self.list_widget.update()

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


def is_item_flashing(list_widget: QListWidget, row: int) -> bool:
    """Check if a list item is currently flashing.

    Args:
        list_widget: List widget containing the item
        row: Row index of item to check

    Returns:
        True if item is currently flashing, False otherwise
    """
    key = (id(list_widget), row)
    if key in _list_item_animators:
        return _list_item_animators[key]._is_flashing
    return False


def reapply_flash_if_active(list_widget: QListWidget, row: int) -> None:
    """Reapply flash color if item is currently flashing.

    With smooth animations, this restarts the animation from scratch
    to ensure visual continuity after background overwrites.

    Args:
        list_widget: List widget containing the item
        row: Row index of item
    """
    key = (id(list_widget), row)
    if key in _list_item_animators:
        animator = _list_item_animators[key]
        if animator._is_flashing:
            # Restart the animation from scratch
            animator.flash_update()


def clear_all_animators(list_widget: QListWidget) -> None:
    """Clear all animators for a specific list widget.

    Call this before clearing/rebuilding the list to prevent
    animations from accessing destroyed items.

    Args:
        list_widget: List widget whose animators should be cleared
    """
    widget_id = id(list_widget)
    keys_to_remove = [k for k in _list_item_animators.keys() if k[0] == widget_id]

    for key in keys_to_remove:
        animator = _list_item_animators[key]
        animator.stop()
        del _list_item_animators[key]

    if keys_to_remove:
        logger.debug(f"Cleared {len(keys_to_remove)} flash animators for list widget")

