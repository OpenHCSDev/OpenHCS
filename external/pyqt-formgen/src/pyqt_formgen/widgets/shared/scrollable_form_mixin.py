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
        groupbox_widget = None  # For section navigation, use groupbox for sizing

        if leaf_name in current_manager.nested_managers:
            # It's a section - get the groupbox for proper sizing
            nested_manager = current_manager.nested_managers[leaf_name]
            # Get the groupbox widget that contains this section
            if hasattr(self.form_manager, '_get_groupbox_for_prefix'):
                groupbox_widget = self.form_manager._get_groupbox_for_prefix(leaf_name)
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
                # Get the groupbox widget for this section
                if hasattr(self.form_manager, '_get_groupbox_for_prefix'):
                    groupbox_widget = self.form_manager._get_groupbox_for_prefix(leaf_name)
                if hasattr(nested_manager, 'widgets') and nested_manager.widgets:
                    first_param_name = next(iter(nested_manager.widgets.keys()))
                    target_widget = nested_manager.widgets[first_param_name]
            else:
                logger.warning(f"❌ Leaf '{leaf_name}' not found in widgets or nested_managers")
                return

        if target_widget is None:
            logger.warning(f"⚠️ No target widget found for {field_name}")
            return

        # Map widget position to scroll area content coordinates
        content_widget = self.scroll_area.widget()

        # Determine if this is a field (has '.') or a groupbox
        is_field = '.' in field_name

        # For groupbox navigation, use the groupbox for sizing (not the first field inside it)
        sizing_widget = groupbox_widget if (groupbox_widget is not None and not is_field) else target_widget

        widget_pos = sizing_widget.mapTo(content_widget, sizing_widget.rect().topLeft())
        widget_height = sizing_widget.height()
        widget_top = widget_pos.y()
        widget_bottom = widget_top + widget_height

        v_scroll_bar = self.scroll_area.verticalScrollBar()
        viewport_height = self.scroll_area.viewport().height()
        viewport_top = v_scroll_bar.value()
        viewport_bottom = viewport_top + viewport_height

        # Check if widget is fully visible in viewport
        is_fully_visible = widget_top >= viewport_top and widget_bottom <= viewport_bottom

        if is_fully_visible:
            logger.info(f"✅ Target {field_name} already visible, skipping scroll")
        else:
            if is_field:
                # Field in groupbox - try to fit entire groupbox if possible
                groupbox_for_field = groupbox_widget or self.form_manager._get_groupbox_for_prefix(section_name)
                if groupbox_for_field:
                    gb_pos = groupbox_for_field.mapTo(content_widget, groupbox_for_field.rect().topLeft())
                    gb_height = groupbox_for_field.height()
                    gb_top = gb_pos.y()

                    if gb_height <= viewport_height:
                        # Groupbox fits in viewport - show entire groupbox, centered
                        gb_center = gb_top + gb_height // 2
                        target_scroll = max(0, gb_center - viewport_height // 2)
                        logger.debug(f"📜 SCROLL: Field {field_name} - groupbox fits, centering groupbox: gb_height={gb_height}, viewport_height={viewport_height}")
                    else:
                        # Groupbox doesn't fit - center the field itself
                        field_pos = target_widget.mapTo(content_widget, target_widget.rect().topLeft())
                        field_center = field_pos.y() + target_widget.height() // 2
                        target_scroll = max(0, field_center - viewport_height // 2)
                        logger.debug(f"📜 SCROLL: Field {field_name} - groupbox too tall, centering field")
                else:
                    # No groupbox found - center the field
                    field_pos = target_widget.mapTo(content_widget, target_widget.rect().topLeft())
                    field_center = field_pos.y() + target_widget.height() // 2
                    target_scroll = max(0, field_center - viewport_height // 2)
            else:
                # Groupbox → center or top-align if taller than viewport
                if widget_height >= viewport_height:
                    # Groupbox taller than viewport - top align
                    target_scroll = widget_top
                    logger.debug(f"📜 SCROLL: {field_name} taller than viewport, top-aligning: widget_height={widget_height}, viewport_height={viewport_height}")
                else:
                    # Center the groupbox vertically in viewport
                    widget_center = widget_top + widget_height // 2
                    target_scroll = max(0, widget_center - viewport_height // 2)
                    logger.debug(f"📜 SCROLL: {field_name} centering: widget_top={widget_top}, widget_height={widget_height}, widget_center={widget_center}, viewport_height={viewport_height}, target_scroll={target_scroll}")

            v_scroll_bar.setValue(target_scroll)
            logger.info(f"✅ Scrolled to {field_name} (target_scroll={target_scroll})")

            # Invalidate flash overlay geometry cache after programmatic scroll
            from pyqt_formgen.animation import WindowFlashOverlay
            WindowFlashOverlay.invalidate_cache_for_widget(self)  # type: ignore[arg-type]

        # Flash the target to highlight it (LOCAL to this window only)
        # Use LEAF flash if we have a specific field, groupbox flash for sections
        if flash and hasattr(self.form_manager, 'queue_flash_local'):
            # Check if this is a leaf field (dotted path with specific widget)
            if target_widget is not None and '.' in field_name:
                # Use leaf flash - register dynamically and queue
                self._queue_leaf_flash_for_navigation(section_name, leaf_name, target_widget)
            else:
                # Section-level flash (no specific leaf widget)
                # Queue both groupbox (standard masking) and tree item
                logger.info(f"⚡ FLASH_DEBUG: Calling queue_flash_local({section_name}) on form_manager scope_id={getattr(self.form_manager, 'scope_id', 'NONE')}")
                self.form_manager.queue_flash_local(section_name)
                self.form_manager.queue_flash_local(f"tree::{section_name}")
            logger.debug(f"⚡ Flashed for {field_name} (local)")

    def _queue_leaf_flash_for_navigation(self, section_name: str, leaf_name: str, leaf_widget) -> None:
        """Queue a leaf flash for navigation to a specific field.

        Uses INVERSE masking: flash the groupbox + all siblings, mask the leaf widget.
        This highlights "the context around the source field" when navigating via provenance.
        """
        # Find the groupbox for this section
        groupbox = self.form_manager._get_groupbox_for_prefix(section_name)
        if not groupbox:
            # Fallback to section flash
            logger.debug(f"[FLASH] No groupbox for {section_name}, falling back to section flash")
            self.form_manager.queue_flash_local(section_name)
            return

        # Register leaf flash element dynamically
        # Use '.' for attribute access (not '::' which is for scope hierarchy)
        leaf_flash_key = f"{section_name}.{leaf_name}"
        self.form_manager.register_flash_leaf(leaf_flash_key, groupbox, leaf_widget)

        # Queue BOTH flashes so they're in sync:
        # 1. Leaf flash for groupbox (inverse masking)
        # 2. Tree item flash (uses tree:: prefix to avoid groupbox collision)
        self.form_manager.queue_flash_local(leaf_flash_key)
        self.form_manager.queue_flash_local(f"tree::{section_name}")
        logger.info(f"⚡ FLASH_DEBUG: Leaf flash for navigation: key={leaf_flash_key}, tree_key=tree::{section_name}")

    def select_and_scroll_to_field(self, field_path: str) -> None:
        """Public API for WindowManager navigation protocol.

        Scrolls to and highlights the specified field.
        This method name matches the protocol expected by WindowManager.focus_and_navigate().
        """
        self._scroll_to_section(field_path, flash=True)
