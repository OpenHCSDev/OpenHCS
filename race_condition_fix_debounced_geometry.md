# Race Condition Fix: Debounced Geometry Tracking

## Problem Description

When label text changes in the UI, it can cause adjacent widgets to reposition themselves. The original geometry tracking system would immediately invalidate the flash overlay cache when any size change was detected, but this created a race condition:

1. Label text changes → size change detected
2. Cache invalidated immediately  
3. Flash animation starts
4. BUT: Layout hasn't settled yet, adjacent widgets are still moving
5. Result: Flash renders at wrong position

## Solution: Debounced Invalidation

Added a 50ms debounce timer to the `WidgetSizeMonitor` class:

```python
# Debounce timer to let layout settle before invalidating cache
self._debounce_timer = QTimer()
self._debounce_timer.setSingleShot(True)
self._debounce_timer.timeout.connect(self._execute_debounced_callbacks)
```

### How It Works

1. **Size Change Detected**: Widget size changes are still detected immediately
2. **Timer Started**: Instead of immediately invalidating cache, a 50ms timer is started
3. **Layout Settles**: During these 50ms, the layout system has time to fully update all affected widget positions
4. **Cache Invalidation**: After the delay, the cache is invalidated when layout is stable

### Key Benefits

- **No More Race Conditions**: Layout has fully settled before flash overlay is rebuilt
- **Performance**: 50ms is imperceptible to users but gives layout system time to complete
- **Orthogonal**: Debouncing is implemented in the `WidgetSizeMonitor`, not scattered across the codebase
- **Generic**: This solution works for any system that needs to react to geometry changes

## Implementation Details

### WidgetSizeMonitor Changes

- Added `QTimer` import and debounce timer
- Added `_execute_debounced_callbacks()` method
- Modified `eventFilter` to use debouncing instead of immediate callback execution

### No Changes Required Elsewhere

The fix is completely orthogonal - it works transparently with existing `FlashGeometryTracker` and doesn't require any changes to the flash overlay system or other components.

## Testing

The fix ensures that when you:
1. Change label text that affects widget layout
2. See adjacent widgets reposition 
3. Flash overlay appears correctly positioned

Instead of the previous race condition where flash might appear in the wrong position due to timing issues between layout updates and cache invalidation.

## Technical Notes

- **50ms Delay**: This is a reasonable compromise between responsiveness and stability
- **Single-shot Timer**: Only the most recent size change triggers the timer (existing timer is reset)
- **No Performance Impact**: The delay is negligible for user experience
- **Orthogonal Design**: The debouncing is internal to `WidgetSizeMonitor` - other systems don't need to know about it