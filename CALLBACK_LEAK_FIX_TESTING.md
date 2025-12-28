# Callback Leak Fix - Testing Guide

## What Was Fixed

**Problem:** ParameterFormManager was leaking callbacks when StepEditor windows closed.

**Root Cause:** 
- When a PFM is created, it registers a callback with ObjectState: `state.on_resolved_changed(self._on_resolved_values_changed)`
- When the window closes, `unregister_from_cross_window_updates()` was called but did NOT unregister this callback
- Each closed window left a dead callback in `ObjectState._on_resolved_changed_callbacks`
- These dead callbacks were invoked on every value change, causing performance degradation

**Fix Applied:**
Added cleanup in `ParameterFormManager.unregister_from_cross_window_updates()`:
```python
if self._parent_manager is None:
    self.state.off_resolved_changed(self._on_resolved_values_changed)
```

## How to Test

### Test Scenario
1. Open PipelineConfig window for a plate
2. Add several steps to the pipeline
3. Open StepEditor windows for multiple steps (e.g., 3-5 windows)
4. Close some of the StepEditor windows
5. Make changes in remaining windows
6. Observe performance and check logs

### What to Look For in Logs

#### 🟢 GOOD (Fix Working)

When opening a StepEditor window:
```
🔔 CALLBACK_LEAK_DEBUG: Registered callback for FunctionStep, total callbacks on ObjectState: 1
```

When closing a StepEditor window:
```
🔔 CALLBACK_LEAK_DEBUG: Unregistered callback for FunctionStep, callbacks: 1 -> 0
```

When making changes (should only see callbacks for OPEN windows):
```
🔔 CALLBACK_LEAK_DEBUG: Notifying 1 callbacks for scope=..., changed_paths={...}
🔔 CALLBACK_LEAK_DEBUG: _on_resolved_values_changed invoked for FunctionStep, changed_paths={...}
```

#### 🔴 BAD (Leak Still Present)

If you see this, the leak is still happening:
```
🔴 CALLBACK_LEAK_DEBUG: Dead callback #0 detected! scope=..., error: wrapped C/C++ object has been deleted
```

Or if callback count doesn't decrease when closing windows:
```
🔔 CALLBACK_LEAK_DEBUG: Unregistered callback for FunctionStep, callbacks: 3 -> 3  # ❌ Should decrease!
```

### Performance Test

**Before Fix (Expected Behavior WITHOUT the fix):**
- Open 3 StepEditor windows → smooth
- Close all 3 windows → callbacks: 3 -> 3 (leak!)
- Open 3 more windows → callbacks: 6 -> 6 (accumulating!)
- Make a change → 6 callbacks fire (3 dead, 3 alive) → slow/errors

**After Fix (Expected Behavior WITH the fix):**
- Open 3 StepEditor windows → callbacks: 0 -> 1 -> 2 -> 3
- Close all 3 windows → callbacks: 3 -> 2 -> 1 -> 0 ✅
- Open 3 more windows → callbacks: 0 -> 1 -> 2 -> 3 ✅
- Make a change → 3 callbacks fire (all alive) → fast ✅

## Log Filtering

To see only the callback leak debug messages:
```bash
grep "CALLBACK_LEAK_DEBUG" openhcs.log
```

To see the full sequence for a specific scope:
```bash
grep "scope=your_scope_id" openhcs.log | grep "CALLBACK_LEAK_DEBUG"
```

## Expected Results

✅ **Success Indicators:**
1. Callback count decreases when windows close
2. No "Dead callback" warnings
3. Performance remains smooth after opening/closing multiple windows
4. Callback count matches number of open windows

❌ **Failure Indicators:**
1. Callback count stays the same or increases when windows close
2. "Dead callback" warnings appear
3. Performance degrades with each window opened
4. RuntimeError exceptions in logs

## Additional Notes

- The fix only applies to **root managers** (`_parent_manager is None`)
- Nested managers don't register callbacks, so they don't need cleanup
- The logging is at INFO level for visibility during testing
- After confirming the fix works, we can reduce logging to DEBUG level

