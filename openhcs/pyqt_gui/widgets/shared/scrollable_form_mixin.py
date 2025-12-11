"""
Mixin for widgets that manage a ParameterFormManager with a scroll area.

Provides common functionality for scrolling to sections in the form.
Used by ConfigWindow and StepParameterEditorWidget.
"""
import logging
from PyQt6.QtWidgets import QScrollArea

logger = logging.getLogger(__name__)


class ScrollableFormMixin:
    """
    Mixin for widgets that have:
    - self.scroll_area: QScrollArea containing the form
    - self.form_manager: ParameterFormManager with nested_managers

    Provides scroll-to-section functionality.
    Optionally triggers flash animation on the target groupbox.
    """

    # Type hints for attributes that must be provided by the implementing class
    scroll_area: QScrollArea
    form_manager: 'ParameterFormManager'  # Forward reference

    def _scroll_to_section(self, field_name: str, flash: bool = True):
        """Scroll to a specific section or field in the form.

        Supports both:
        - Section names (e.g., 'path_planning_config') - scrolls to groupbox
        - Dotted paths (e.g., 'path_planning_config.well_filter') - scrolls to specific widget

        Args:
            field_name: The field name or dotted path to scroll to
            flash: If True, flash the target groupbox after scrolling
        """
        logger.info(f"🔍 Scrolling to section: {field_name}")

        if not hasattr(self, 'scroll_area') or self.scroll_area is None:
            logger.warning("Scroll area not initialized; cannot navigate to section")
            return

        # Parse dotted path to navigate through nested managers
        parts = field_name.split('.')
        current_manager = self.form_manager
        target_widget = None
        section_name = parts[0]  # For flashing the groupbox

        # Navigate through nested managers for all but the last part
        for i, part in enumerate(parts[:-1]):
            if part not in current_manager.nested_managers:
                logger.warning(f"❌ Part '{part}' not in nested_managers at depth {i}")
                return
            current_manager = current_manager.nested_managers[part]

        # The last part is either a nested manager (section) or a widget (leaf field)
        leaf_name = parts[-1]

        if leaf_name in current_manager.nested_managers:
            # It's a section - scroll to first widget in that section
            nested_manager = current_manager.nested_managers[leaf_name]
            if hasattr(nested_manager, 'widgets') and nested_manager.widgets:
                first_param_name = next(iter(nested_manager.widgets.keys()))
                target_widget = nested_manager.widgets[first_param_name]
        elif leaf_name in current_manager.widgets:
            # It's a leaf widget - scroll directly to it
            target_widget = current_manager.widgets[leaf_name]
        else:
            # Single-part path that's a nested manager key
            if len(parts) == 1 and leaf_name in self.form_manager.nested_managers:
                nested_manager = self.form_manager.nested_managers[leaf_name]
                if hasattr(nested_manager, 'widgets') and nested_manager.widgets:
                    first_param_name = next(iter(nested_manager.widgets.keys()))
                    target_widget = nested_manager.widgets[first_param_name]
            else:
                logger.warning(f"❌ Leaf '{leaf_name}' not found in widgets or nested_managers")
                return

        if target_widget is None:
            logger.warning(f"⚠️ No target widget found for {field_name}")
            return

        # Map widget position to scroll area coordinates and scroll to it
        widget_pos = target_widget.mapTo(self.scroll_area.widget(), target_widget.rect().topLeft())
        v_scroll_bar = self.scroll_area.verticalScrollBar()

        # Scroll to widget position with offset to show context above
        target_scroll = max(0, widget_pos.y() - 50)
        v_scroll_bar.setValue(target_scroll)

        logger.info(f"✅ Scrolled to {field_name}")

        # Invalidate flash overlay geometry cache after programmatic scroll
        # (scroll bar setValue doesn't trigger Wheel events that event filter catches)
        # Use 'self' (the ConfigWindow/StepParameterEditorWidget) not form_manager
        from openhcs.pyqt_gui.widgets.shared.flash_mixin import WindowFlashOverlay
        WindowFlashOverlay.invalidate_cache_for_widget(self)  # type: ignore[arg-type]

        # Flash the target groupbox to highlight it (LOCAL to this window only)
        # Route through root form_manager (only root initializes FlashMixin)
        if flash and hasattr(self.form_manager, 'queue_flash_local'):
            # Use local flash for navigation - only this window, not cross-window
            logger.info(f"⚡ FLASH_DEBUG: Calling queue_flash_local({section_name}) on form_manager scope_id={getattr(self.form_manager, 'scope_id', 'NONE')}")
            self.form_manager.queue_flash_local(section_name)
            logger.debug(f"⚡ Flashed groupbox for {section_name} (local)")

    def select_and_scroll_to_field(self, field_path: str) -> None:
        """Public API for WindowManager navigation protocol.

        Scrolls to and highlights the specified field.
        This method name matches the protocol expected by WindowManager.focus_and_navigate().
        """
        self._scroll_to_section(field_path, flash=True)
