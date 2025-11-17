====================================
Visual Feedback Integration Guide
====================================

*For developers implementing scope-based visual feedback in new widgets*

Overview
========

This guide shows how to integrate the scope-based visual feedback system into new widgets. The system provides:

- **Scope-based coloring** for list items and windows
- **Flash animations** for list items and form widgets
- **Layered borders** for visual differentiation
- **Dual tracking** (flash detection vs label updates)

Prerequisites
=============

Before integrating visual feedback, ensure your widget:

1. Uses ``CrossWindowPreviewMixin`` for cross-window updates
2. Has a clear scope hierarchy (orchestrator → steps or similar)
3. Uses ``QListWidget`` for displaying items (if applicable)
4. Uses ``MultilinePreviewItemDelegate`` for custom rendering (if applicable)

Integration Steps
=================

Step 1: Apply Scope-Based Styling to List Items
------------------------------------------------

For widgets that display list items (like PipelineEditor or PlateManager):

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme
   from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ListItemType
   
   def _apply_item_styling(self, item: QListWidgetItem, scope_id: str, item_type: ListItemType) -> None:
       """Apply scope-based background color and border to list item.
       
       Args:
           item: List widget item to style
           scope_id: Scope identifier (e.g., "/path/to/plate::step_0@5")
           item_type: Type of item (ORCHESTRATOR or STEP)
       """
       # Get color scheme for this scope
       color_scheme = get_scope_color_scheme(scope_id)
       
       # Apply background color using enum-driven polymorphic dispatch
       bg_color = item_type.get_background_color(color_scheme)
       if bg_color is not None:
           item.setBackground(bg_color)
       
       # Store border data for delegate rendering
       # UserRole + 3: border_layers (list of (width, tint_index, pattern) tuples)
       # UserRole + 4: base_color_rgb (tuple of RGB values)
       if item_type == ListItemType.ORCHESTRATOR:
           # Simple border for orchestrators
           item.setData(Qt.ItemDataRole.UserRole + 3, [(3, 1, 'solid')])
           item.setData(Qt.ItemDataRole.UserRole + 4, color_scheme.orchestrator_item_border_rgb)
       else:
           # Layered borders for steps
           item.setData(Qt.ItemDataRole.UserRole + 3, color_scheme.step_border_layers)
           item.setData(Qt.ItemDataRole.UserRole + 4, color_scheme.step_window_border_rgb)

**Key points**:

- Use ``@position`` suffix in scope_id for per-orchestrator step indexing
- Store border data in UserRole + 3 and UserRole + 4 for delegate rendering
- Use ``ListItemType`` enum for polymorphic color selection

Step 2: Implement Incremental Updates with Flash
-------------------------------------------------

Override ``_refresh_items_by_index()`` to handle incremental updates:

.. code-block:: python

   def _refresh_step_items_by_index(
       self,
       indices: List[int],
       live_context_snapshot,
       label_subset: Optional[Set[int]] = None,
       changed_fields: Optional[Set[str]] = None,
       live_context_before=None,
   ) -> None:
       """Refresh step items with incremental updates and flash animations.

       CRITICAL: Apply styling BEFORE flash to prevent overwriting flash color.
       """
       for step_index in indices:
           step = self.pipeline_steps[step_index]
           item = self.step_list.item(step_index)

           should_update_labels = (
               label_subset is None or step_index in label_subset
           )

           # Get preview instance (merges step-scoped live values)
           step_for_display = self._get_step_preview_instance(step, live_context_snapshot)

           # Format display text (resolves through hierarchy)
           display_text = self._format_resolved_step_for_display(
               step_for_display, live_context_snapshot
           )

           # CRITICAL: Apply styling BEFORE flash (so flash color isn't overwritten)
           if should_update_labels:
               self._apply_step_item_styling(item)

           # Flash on incremental update
           self._flash_step_item(step_index)

           # Update label
           if should_update_labels:
               item.setText(display_text)

**Critical Ordering Requirement**:

The order of operations is critical to prevent flash animations from being invisible:

1. **Apply styling FIRST** - Sets the normal background color
2. **Flash SECOND** - Temporarily increases opacity to 100%
3. **Update label LAST** - Changes text content

If you apply styling AFTER flash, the styling will overwrite the flash color and the
flash will be invisible to users.

**Key points**:

- ``_pending_label_keys`` contains only items with registered preview field changes
- ``_pending_changed_fields`` contains ALL changed fields (for future flash detection)
- Currently flashing on ALL incremental updates (flash detection will be added later)

Step 3: Separate Full Refresh from Incremental Updates
-------------------------------------------------------

Implement ``_handle_full_preview_refresh()`` WITHOUT flash:

.. code-block:: python

   def _handle_full_preview_refresh(self) -> None:
       """Handle full refresh WITHOUT flash (used for window close/reset events).

       Full refresh does NOT flash - it's just reverting to saved values.
       Flash only happens in incremental updates where we know what changed.
       """
       self.update_step_list()

**Key points**:

- Full refresh is triggered by window close/reset events
- These events revert to saved values (not actual changes)
- Only incremental updates should flash (where we know exactly what changed)

Step 4: Add Flash Animation
----------------------------

Implement flash methods for list items:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.list_item_flash_animation import flash_list_item
   
   def _flash_step_item(self, step_index: int) -> None:
       """Flash step list item to indicate update.
       
       Args:
           step_index: Index of step whose item should flash
       """
       if 0 <= step_index < self.step_list.count():
           step = self.pipeline_steps[step_index]
           scope_id = self._build_step_scope_id(step, position=step_index)
           
           flash_list_item(
               list_widget=self.step_list,
               row=step_index,
               scope_id=scope_id,
               item_type=ListItemType.STEP
           )

**Key points**:

- Use ``flash_list_item()`` for list items
- Use ``flash_widget()`` for form widgets
- Include ``@position`` suffix in scope_id for correct color restoration

Step 5: Clear Animators on List Rebuild
----------------------------------------

Call ``clear_all_animators()`` before rebuilding list to prevent flash timers accessing destroyed items:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.list_item_flash_animation import clear_all_animators
   
   def update_step_list(self) -> None:
       """Rebuild step list with scope-based styling."""
       # Clear flash animators before destroying items
       clear_all_animators()
       
       # Clear and rebuild list
       self.step_list.clear()
       
       for idx, step in enumerate(self.pipeline_steps):
           item = QListWidgetItem(self._format_step_label(step))
           
           # Apply scope-based styling
           scope_id = self._build_step_scope_id(step, position=idx)
           self._apply_step_item_styling(item, scope_id, idx)
           
           self.step_list.addItem(item)

Step 6: Apply Window Borders (Optional)
----------------------------------------

For editor windows, apply colored borders matching the scope:

.. code-block:: python

   from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme
   
   def _apply_window_styling(self, scope_id: str) -> None:
       """Apply colored border to window.
       
       Args:
           scope_id: Scope identifier for color selection
       """
       color_scheme = get_scope_color_scheme(scope_id)
       border_color = color_scheme.step_window_border_rgb
       
       # Apply border stylesheet
       self.setStyleSheet(f"""
           QWidget {{
               border: 3px solid rgb{border_color};
           }}
       """)

Complete Example
================

Here's a complete example integrating all components:

.. code-block:: python

   from PyQt6.QtWidgets import QWidget, QListWidget, QListWidgetItem
   from openhcs.pyqt_gui.widgets.mixins import CrossWindowPreviewMixin
   from openhcs.pyqt_gui.widgets.shared.scope_visual_config import ListItemType
   from openhcs.pyqt_gui.widgets.shared.scope_color_utils import get_scope_color_scheme
   from openhcs.pyqt_gui.widgets.shared.list_item_flash_animation import (
       flash_list_item, clear_all_animators
   )
   
   class MyListWidget(QWidget, CrossWindowPreviewMixin):
       def __init__(self):
           super().__init__()
           self._init_cross_window_preview_mixin()
           
           # Register preview scopes
           self.register_preview_scope(
               root_name='item',
               editing_types=(MyItem,),
               scope_resolver=lambda item, ctx: self._build_item_scope_id(item),
               aliases=('MyItem',),
           )
           
           # Enable preview fields
           self.enable_preview_for_field(
               'config.enabled',
               lambda v: '✓' if v else '✗',
               scope_root='item'
           )
       
       def _build_item_scope_id(self, item: MyItem, position: Optional[int] = None) -> str:
           """Build scope ID for item."""
           base_scope = f"{self.orchestrator_path}::{item._token}"
           if position is not None:
               return f"{base_scope}@{position}"
           return base_scope
       
       def _apply_item_styling(self, list_item: QListWidgetItem, scope_id: str, position: int) -> None:
           """Apply scope-based styling."""
           color_scheme = get_scope_color_scheme(scope_id)
           bg_color = ListItemType.STEP.get_background_color(color_scheme)
           
           if bg_color is not None:
               list_item.setBackground(bg_color)
           
           list_item.setData(Qt.ItemDataRole.UserRole + 3, color_scheme.step_border_layers)
           list_item.setData(Qt.ItemDataRole.UserRole + 4, color_scheme.step_window_border_rgb)
       
       def _refresh_items_by_index(self, indices: Set[int]) -> None:
           """Refresh items with flash detection."""
           label_subset = self._pending_label_keys & indices
           changed_fields = self._pending_changed_fields
           
           live_context_before = self._last_live_context_snapshot
           live_context_after = self._collect_live_context()
           
           for idx in indices:
               item_data = self.items[idx]
               
               if idx in label_subset:
                   self._update_item_label(idx, item_data)
               
               if self._check_resolved_value_changed(
                   item_data, changed_fields, live_context_before, live_context_after
               ):
                   self._flash_item(idx)
       
       def _flash_item(self, index: int) -> None:
           """Flash item to indicate update."""
           if 0 <= index < self.list_widget.count():
               item_data = self.items[index]
               scope_id = self._build_item_scope_id(item_data, position=index)
               
               flash_list_item(
                   list_widget=self.list_widget,
                   row=index,
                   scope_id=scope_id,
                   item_type=ListItemType.STEP
               )
       
       def update_list(self) -> None:
           """Rebuild list with styling."""
           clear_all_animators()
           self.list_widget.clear()
           
           for idx, item_data in enumerate(self.items):
               list_item = QListWidgetItem(self._format_label(item_data))
               scope_id = self._build_item_scope_id(item_data, position=idx)
               self._apply_item_styling(list_item, scope_id, idx)
               self.list_widget.addItem(list_item)

See Also
========

- :doc:`../architecture/scope_visual_feedback_system` - Complete architecture documentation
- :doc:`../architecture/gui_performance_patterns` - Cross-window preview system
- :doc:`../architecture/configuration_framework` - Lazy configuration and context system

