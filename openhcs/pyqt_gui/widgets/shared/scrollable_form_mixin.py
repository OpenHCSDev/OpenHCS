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
    """
    
    # Type hints for attributes that must be provided by the implementing class
    scroll_area: QScrollArea
    form_manager: 'ParameterFormManager'  # Forward reference
    
    def _scroll_to_section(self, field_name: str):
        """Scroll to a specific section in the form."""
        logger.info(f"🔍 Scrolling to section: {field_name}")

        if not hasattr(self, 'scroll_area') or self.scroll_area is None:
            logger.warning("Scroll area not initialized; cannot navigate to section")
            return

        # Find the nested manager for this section
        if field_name not in self.form_manager.nested_managers:
            logger.warning(f"❌ Field '{field_name}' not in nested_managers")
            return

        nested_manager = self.form_manager.nested_managers[field_name]

        # Find the first widget in this nested manager
        if not (hasattr(nested_manager, 'widgets') and nested_manager.widgets):
            logger.warning(f"⚠️ No widgets found in {field_name}")
            return

        first_param_name = next(iter(nested_manager.widgets.keys()))
        first_widget = nested_manager.widgets[first_param_name]

        # Map widget position to scroll area coordinates and scroll to it
        widget_pos = first_widget.mapTo(self.scroll_area.widget(), first_widget.rect().topLeft())
        v_scroll_bar = self.scroll_area.verticalScrollBar()
        
        # Scroll to widget position with offset to show context above
        target_scroll = max(0, widget_pos.y() - 50)
        v_scroll_bar.setValue(target_scroll)
        
        logger.info(f"✅ Scrolled to {field_name}")

