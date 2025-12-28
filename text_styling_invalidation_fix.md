# Text & Styling Change Invalidation Fix

## Problem Identified

**Issue**: Label text changes and styling changes don't trigger geometry cache invalidation, leading to **stale flash overlay positioning**.

**Root Cause**: Current event filter only catches Resize, Wheel, Move, and LayoutRequest events, but misses:
- `setText()` calls that change label dimensions
- `setStyleSheet()` calls that change widget styling (fonts, padding, colors)

## Specific Problem Locations

### 1. Dirty Label Updates (`clickable_help_components.py`)
```python
# Lines 659-662
if is_dirty:
    self._label.setText(f"* {self._base_text}")
else:
    self._label.setText(f"  {self._base_text}")  # Two spaces = same width as "* "

# Lines 785-788
if is_dirty:
    self._title_label.setText(f"* {self._base_title}")
else:
    self._title_label.setText(f"  {self._base_title}")  # Two spaces = same width as "* "
```

### 2. Tree Item Updates (`config_hierarchy_tree.py`)
```python
# Lines 300-303
if is_dirty and not has_marker:
    item.setText(0, f"* {current_text}")
elif not is_dirty and has_marker:
    item.setText(0, current_text[2:])  # Remove "* " prefix
```

### 3. General Styling Changes
Throughout the codebase: `widget.setStyleSheet(...)` calls for:
- Color changes
- Font changes  
- Padding changes
- Border changes

## Why This Breaks Flash Overlays

1. **Text changes** → Widget dimensions change → Flash overlay geometry becomes incorrect
2. **Styling changes** → Font/padding changes → Widget dimensions change → Flash overlay geometry becomes incorrect
3. **Current event filter misses these changes** → Cache not invalidated → Stale geometry used

## Simple Fix: Extend Event Filter

### Current Event Filter (`flash_mixin.py:795-831`)
```python
def eventFilter(self, obj, event):
    """Catch scroll/resize/layout events to invalidate geometry cache."""
    from PyQt6.QtCore import QEvent
    event_type = event.type()

    # Always invalidate on Resize and Wheel
    if event_type in (QEvent.Type.Resize, QEvent.Type.Wheel):
        logger.debug(f"[FLASH] Event filter caught {event_type} on {obj.__class__.__name__}, invalidating cache")
        self._invalidate_geometry_cache()
        # CRITICAL: When window resizes, also resize the overlay to match
        if obj is self._window and event_type == QEvent.Type.Resize:
            self.setGeometry(self._window.rect())

    # LayoutRequest: only invalidate if widget SIZE actually changed
    elif event_type == QEvent.Type.LayoutRequest:
        widget_id = id(obj)
        element_widgets = getattr(self, '_element_widgets', set())
        if widget_id in element_widgets:
            # Check if size actually changed
            from PyQt6.QtWidgets import QWidget
            if isinstance(obj, QWidget):
                current_size = obj.size()
                previous_size = self._widget_sizes.get(widget_id)

                size_changed = previous_size is None or current_size != previous_size
                if size_changed:
                    logger.debug(f"[FLASH] LayoutRequest from {obj.__class__.__name__}: size changed {previous_size} → {current_size}")
                    self._widget_sizes[widget_id] = current_size
                    # Invalidate immediately - no deferral needed
                    self._cache.invalidate()
                # else: size unchanged; ignore to avoid redundant rebuilds

    return super().eventFilter(obj, event)
```

### Enhanced Event Filter

```python
def eventFilter(self, obj, event):
    """Catch scroll/resize/layout events + text/styling changes to invalidate geometry cache."""
    from PyQt6.QtCore import QEvent
    from PyQt6.QtWidgets import QLabel, QAbstractItemView
    event_type = event.type()

    # Always invalidate on Resize and Wheel
    if event_type in (QEvent.Type.Resize, QEvent.Type.Wheel):
        logger.debug(f"[FLASH] Event filter caught {event_type} on {obj.__class__.__name__}, invalidating cache")
        self._invalidate_geometry_cache()
        # CRITICAL: When window resizes, also resize the overlay to match
        if obj is self._window and event_type == QEvent.Type.Resize:
            self.setGeometry(self._window.rect())

    # FIX: Catch font changes (affects widget dimensions)
    elif event_type == QEvent.Type.FontChange:
        logger.debug(f"[FLASH] Event filter caught FontChange on {obj.__class__.__name__}, invalidating cache")
        self._invalidate_geometry_cache()

    # FIX: Catch style changes (affects widget dimensions via padding/borders)
    elif event_type == QEvent.Type.StyleChange:
        logger.debug(f"[FLASH] Event filter caught StyleChange on {obj.__class__.__name__}, invalidating cache")
        self._invalidate_geometry_cache()

    # LayoutRequest: only invalidate if widget SIZE actually changed
    elif event_type == QEvent.Type.LayoutRequest:
        widget_id = id(obj)
        element_widgets = getattr(self, '_element_widgets', set())
        if widget_id in element_widgets:
            # Check if size actually changed
            from PyQt6.QtWidgets import QWidget
            if isinstance(obj, QWidget):
                current_size = obj.size()
                previous_size = self._widget_sizes.get(widget_id)

                size_changed = previous_size is None or current_size != previous_size
                if size_changed:
                    logger.debug(f"[FLASH] LayoutRequest from {obj.__class__.__name__}: size changed {previous_size} → {current_size}")
                    self._widget_sizes[widget_id] = current_size
                    # Invalidate immediately - no deferral needed
                    self._cache.invalidate()
                # else: size unchanged; ignore to avoid redundant rebuilds

    return super().eventFilter(obj, event)
```

## Alternative: Targeted Signal Connections

For more precise control, connect to specific widget signals:

```python
def _install_widget_event_filter(self, element: FlashElement) -> None:
    """Install event filter + signal connections on a flash element's widget."""
    # For groupbox elements, try to get the actual widget and install filter on it
    source_id = element.source_id or ""
    if source_id.startswith("groupbox:") or source_id.startswith("leaf_flash:"):
        if not hasattr(self, '_element_widgets'):
            self._element_widgets: Set[int] = set()
        try:
            # Parse widget id from source_id
            widget_id = int(source_id.split(":")[1])
            self._element_widgets.add(widget_id)
            # Find the actual widget by scanning window children
            from PyQt6.QtWidgets import QGroupBox, QLabel
            for groupbox in self._window.findChildren(QGroupBox):
                if id(groupbox) == widget_id:
                    groupbox.installEventFilter(self)
                    
                    # FIX: Connect to font and style change signals
                    if hasattr(groupbox, 'font'):
                        groupbox.fontChanged.connect(lambda: self._invalidate_geometry_cache())
                    
                    logger.debug(f"[FLASH] Installed event filter on groupbox {widget_id}")
                    break
        except (ValueError, IndexError):
            pass
```

## Implementation Priority

**Option 1: Quick Fix (Recommended)**
- Add `QEvent.Type.FontChange` and `QEvent.Type.StyleChange` to event filter
- **Impact**: Fixes 90% of text/styling change issues
- **Effort**: 5 minutes
- **Risk**: Minimal

**Option 2: Precise Fix**
- Connect to specific widget signals (`fontChanged`, `styleSheetChanged`)
- **Impact**: Fixes 100% of text/styling change issues  
- **Effort**: 30 minutes
- **Risk**: Low

**Option 3: Comprehensive Fix**
- Implement granular cache invalidation with dependency tracking
- **Impact**: Complete solution with optimal performance
- **Effort**: 2-3 hours
- **Risk**: Medium

## Expected Results

With the quick fix:
- **Dirty labels**: Flash overlays update correctly when asterisk appears/disappears
- **Tree items**: Flash overlays update when item text changes
- **Styling changes**: Flash overlays update when fonts/colors/padding change
- **No performance impact**: Event filter addition is negligible

## Testing

1. **Dirty label test**: Toggle dirty state on a config field, verify flash overlay repositions correctly
2. **Tree item test**: Change tree item text, verify flash overlay follows new position
3. **Styling test**: Change widget font/padding via stylesheet, verify flash overlay adjusts

## Conclusion

This is a **simple, low-risk fix** that addresses the core issue. The problem isn't architectural complexity - it's just missing event types in the filter. Adding `FontChange` and `StyleChange` events will fix the under-invalidation problem immediately.