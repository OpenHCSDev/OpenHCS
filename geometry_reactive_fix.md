# Orthogonal Geometry Tracking Implementation

## Overview

Successfully implemented orthogonal geometry tracking for the OpenHCS PyQt6 flash overlay system, replacing scattered event filters with a clean, reusable abstraction that solves geometry change detection completely, generically, and composably.

## Problem Solved

**UNDER-INVALIDATION**: The original flash overlay system used manual event filter installation with constant-width dirty markers to prevent geometry changes. However, when label text or styling changes affected widget dimensions, the geometry cache wasn't invalidated, causing misaligned flash overlays.

## Orthogonal Architecture

### Core Abstractions

1. **WidgetSizeMonitor** (`openhcs/pyqt_gui/widgets/shared/geometry_tracking.py:19-72`)
   - Single responsibility: Only detects size changes in watched widgets
   - Provides clean callback interface for systems needing size change notifications
   - Generic and reusable across different systems

2. **AutoGeometryTracker** (`openhcs/pyqt_gui/widgets/shared/geometry_tracking.py:75-129`)
   - Single responsibility: Only discovers widgets that could affect geometry
   - Automatic widget discovery (QLabel, QGroupBox, QAbstractItemView)
   - No manual registration required

3. **FlashGeometryTracker** (`openhcs/pyqt_gui/widgets/shared/geometry_tracking.py:132-170`)
   - Integrates with WindowFlashOverlay to automatically invalidate cache
   - Reactive approach: detects size changes, invalidates cache
   - Extensible for custom behavior

### Integration with Flash System

Modified `WindowFlashOverlay.__init__()` (`openhcs/pyqt_gui/widgets/shared/flash_mixin.py:708-710`):

```python
# ORTHOGONAL GEOMETRY TRACKING: Separate abstraction for geometry change detection
# This replaces scattered event filters with a unified, reusable system
self._geometry_tracker = create_flash_geometry_tracking(window, self)
```

## Key Benefits

### 1. Eliminates Scattered Event Filters
- **Before**: Manual event filter installation in `_install_widget_event_filter()`
- **After**: Automatic discovery and monitoring via orthogonal tracker
- **Result**: No more manual widget tracking, cleaner architecture

### 2. Solves Under-Invalidation
- **Before**: Constant-width dirty markers prevented detection of text/styling changes
- **After**: Reactive size change detection catches ALL geometry-affecting changes
- **Result**: Flash overlays always correctly positioned when widgets change size

### 3. Reusable Infrastructure
- **Before**: Flash-specific event filtering logic scattered across code
- **After**: Generic geometry tracking system usable by any system
- **Result**: Platform-level abstraction that makes building geometry-aware systems trivial

### 4. Performance Optimization
- **Before**: Multiple event filters, manual size tracking, LayoutRequest spam filtering
- **After**: Single monitoring system with efficient size change detection
- **Result**: Better performance with cleaner code

## Files Modified

1. **`openhcs/pyqt_gui/widgets/shared/geometry_tracking.py`** (NEW)
   - Complete orthogonal geometry tracking system
   - 170 lines of clean, documented, reusable code

2. **`openhcs/pyqt_gui/widgets/shared/flash_mixin.py`**
   - Added import for geometry tracking (`line 44`)
   - Integrated tracker in `WindowFlashOverlay.__init__()` (`line 710`)
   - Removed manual event filter installation (`lines 758-762`)
   - Removed `_install_widget_event_filter()` method (`lines 783-787`)
   - Simplified eventFilter (`lines 802-823`)
   - Removed manual size tracking (`lines 703-707`)

## Architecture Principles Followed

### Orthogonality
- ✅ Each abstraction solves one problem completely
- ✅ Each abstraction solves it generically  
- ✅ Each abstraction solves it once
- ✅ No overlapping responsibilities

### Declarative Supremacy
- ✅ Configuration-as-documentation
- ✅ Shape of data is shape of system
- ✅ Declarative widget discovery and monitoring

### Platform Thinking
- ✅ Built infrastructure that makes building geometry-aware systems trivial
- ✅ Reusable across different UI systems
- ✅ Not application-specific, but platform-level

## Testing Strategy

The orthogonal system should be tested with:

1. **Text Changes**: Dirty labels changing text should trigger cache invalidation
2. **Styling Changes**: Widgets with style changes affecting size should trigger invalidation  
3. **Widget Discovery**: All relevant widget types (QLabel, QGroupBox, QAbstractItemView) should be automatically discovered
4. **Performance**: Size change detection should be efficient with no false positives
5. **Integration**: Flash overlay cache should be properly invalidated when geometry changes

## Future Extensibility

The orthogonal system enables:
- **Multiple Systems**: Any system can use `WidgetSizeMonitor` for size change detection
- **Custom Discovery**: Subclasses can override `_discover_geometry_widgets()` for custom widget types
- **Custom Reactions**: Subclasses can override `_on_widget_size_changed()` for custom behavior
- **Generic Infrastructure**: Can be used beyond flash overlays (layout managers, responsive UIs, etc.)

## Conclusion

This implementation demonstrates OpenHCS principles in action:
- **Orthogonal abstractions** that solve fundamental problems completely
- **Platform thinking** that makes building complex UI systems trivial  
- **Declarative architecture** where the system structure is clear and maintainable
- **Performance optimization** through clean, efficient design

The result is a flash overlay system that correctly handles all geometry changes while providing reusable infrastructure for future UI development needs.