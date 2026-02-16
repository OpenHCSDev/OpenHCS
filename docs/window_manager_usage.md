# WindowManager Usage Guide

## Overview

`WindowManager` provides singleton window management with navigation support for inheritance tracking.

**Key Features:**
- One window per scope_id (prevents duplicate windows)
- Auto-cleanup on close (no manual unregistration)
- Navigation API for focusing + scrolling to fields
- Fail-loud on stale references

## Basic Usage

### Show or Focus Window

```python
from openhcs.pyqt_gui.services.window_manager import WindowManager

# Define factory function that creates the window
def create_config_window():
    return ConfigWindow(
        config_class=PipelineConfig,
        initial_config=current_config,
        parent=self,
        on_save_callback=self._on_config_saved,
        scope_id="plate1"
    )

# Show window (creates new or focuses existing)
window = WindowManager.show_or_focus("plate1", create_config_window)
```

**Before WindowManager:**
```python
# Old way - creates duplicate windows
config_window = ConfigWindow(...)
config_window.show()
```

**After WindowManager:**
```python
# New way - singleton per scope
WindowManager.show_or_focus(scope_id, lambda: ConfigWindow(...))
```

## Migration Examples

### PlateManager: Edit Config Button

**Before:**
```python
def action_edit_config(self):
    """Edit configuration for selected plate."""
    config_window = ConfigWindow(
        config_class=PipelineConfig,
        initial_config=self._get_current_config(),
        parent=self,
        on_save_callback=self._on_config_saved,
        scope_id=str(self.selected_plate_path)
    )
    config_window.show()
```

**After:**
```python
def action_edit_config(self):
    """Edit configuration for selected plate."""
    from openhcs.pyqt_gui.services.window_manager import WindowManager

    scope_id = str(self.selected_plate_path)

    def create_window():
        return ConfigWindow(
            config_class=PipelineConfig,
            initial_config=self._get_current_config(),
            parent=self,
            on_save_callback=self._on_config_saved,
            scope_id=scope_id
        )

    WindowManager.show_or_focus(scope_id, create_window)
```

### PipelineEditor: Edit Step Button

**Before:**
```python
def action_edit(self):
    """Edit selected step."""
    step_window = DualEditorWindow(
        editing_step=selected_step,
        parent=self,
        on_save_callback=self._on_step_saved,
        scope_id=f"{self.scope_id}::step_{index}"
    )
    step_window.show()
```

**After:**
```python
def action_edit(self):
    """Edit selected step."""
    from openhcs.pyqt_gui.services.window_manager import WindowManager

    scope_id = f"{self.scope_id}::step_{index}"

    def create_window():
        return DualEditorWindow(
            editing_step=selected_step,
            parent=self,
            on_save_callback=self._on_step_saved,
            scope_id=scope_id
        )

    WindowManager.show_or_focus(scope_id, create_window)
```

## Navigation API (Future: Inheritance Tracking)

### Basic Navigation

```python
# Focus window without navigation
WindowManager.focus_and_navigate(scope_id="plate1")

# Focus window and navigate to item
WindowManager.focus_and_navigate(
    scope_id="plate1",
    item_id="step_3"  # Select step 3 in list
)

# Focus window and navigate to field
WindowManager.focus_and_navigate(
    scope_id="plate1",
    field_path="well_filter_config.well_filter"  # Scroll to this field
)
```

### Implementing Navigation in Windows

Windows can optionally implement navigation methods:

```python
class ConfigWindow(BaseFormDialog):
    """Config window with navigation support."""

    def select_and_scroll_to_field(self, field_path: str):
        """Navigate to field in tree/form (called by WindowManager).

        Args:
            field_path: Dotted path like "well_filter_config.well_filter"
        """
        # 1. Find tree item matching field_path
        tree_item = self.tree_helper.find_item_by_path(self.tree_widget, field_path)
        if not tree_item:
            return

        # 2. Expand parent nodes
        parent = tree_item.parent()
        while parent:
            parent.setExpanded(True)
            parent = parent.parent()

        # 3. Select and scroll to item
        self.tree_widget.setCurrentItem(tree_item)
        self.tree_widget.scrollToItem(tree_item)

        # 4. Flash to highlight
        self.queue_flash(field_path)


class DualEditorWindow(BaseFormDialog):
    """Step editor with navigation support."""

    def select_and_scroll_to_item(self, item_id: str):
        """Navigate to tab/section for item (called by WindowManager).

        Args:
            item_id: Item identifier (e.g., tab index, field name)
        """
        # Switch to tab containing the item
        tab_index = self._get_tab_for_item(item_id)
        if tab_index >= 0:
            self.tab_widget.setCurrentIndex(tab_index)

        # Scroll to widget
        widget = self._get_widget_for_item(item_id)
        if widget:
            widget.setFocus()
```

## Future: Inheritance Tracking

When user clicks an inherited field, show source window and scroll to it:

```python
class InheritanceTreeWidget(QTreeWidget):
    """Tree widget showing field inheritance."""

    def on_field_clicked(self, field_path: str, source_scope: str):
        """User clicked field - show source window and scroll to it.

        Args:
            field_path: Field that was clicked
            source_scope: Scope where field is defined (not inherited)
        """
        from openhcs.pyqt_gui.services.window_manager import WindowManager

        # Try to focus existing window and navigate
        if WindowManager.focus_and_navigate(source_scope, field_path=field_path):
            return  # Window exists and navigated

        # Window not open - create it and navigate
        def create_window():
            return ConfigWindow(
                config_class=self._get_config_class(source_scope),
                initial_config=self._get_config(source_scope),
                scope_id=source_scope
            )

        window = WindowManager.show_or_focus(source_scope, create_window)

        # Navigate after window is shown (give Qt time to render)
        QTimer.singleShot(100, lambda: window.select_and_scroll_to_field(field_path))
```

## Utility Methods

```python
# Check if window is open
if WindowManager.is_open("plate1"):
    print("Config window already open for plate1")

# Get all open window scopes
open_scopes = WindowManager.get_open_scopes()
print(f"Open windows: {open_scopes}")

# Programmatically close window
WindowManager.close_window("plate1")
```

## Architecture Notes

### Auto-Cleanup

Windows are automatically unregistered when closed (no manual cleanup needed):

```python
# WindowManager hooks into closeEvent
window.closeEvent = lambda event: (
    unregister_from_registry(),
    call_original_closeEvent(event)
)
```

### Fail-Loud on Stale References

If window is deleted but still in registry, raises RuntimeError:

```python
try:
    window.isVisible()  # Test if still valid
except RuntimeError:
    # Window deleted - clean up stale reference
    del WindowManager._scoped_windows[scope_id]
```

### Duck Typing for Navigation

Navigation methods are optional - windows implement if supported:

```python
# WindowManager checks if method exists before calling
if hasattr(window, 'select_and_scroll_to_field'):
    window.select_and_scroll_to_field(field_path)
```

## Benefits

1. **Prevents duplicate windows**: Only one config window per plate
2. **Better UX**: Clicking "Edit Config" brings existing window to front
3. **Auto-cleanup**: No memory leaks from forgotten window references
4. **Extensible**: Navigation API ready for inheritance tracking
5. **Fail-loud**: Catches deleted windows early
6. **Fits OpenHCS patterns**: Like ObjectStateRegistry for states
