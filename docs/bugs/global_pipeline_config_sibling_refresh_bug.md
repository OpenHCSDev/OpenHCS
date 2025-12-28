# Bug: GlobalPipelineConfig Sibling Refresh on Reset

## Summary

In GlobalPipelineConfig window only, when resetting `well_filter_config.well_filter` to None, the sibling `step_well_filter_config.well_filter` still shows stale "Pipeline default: 2" until a SECOND reset.

## Reproduction

1. Open GlobalPipelineConfig window
2. Set `well_filter_config.well_filter` = "2"
3. Observe: `step_well_filter_config.well_filter` shows "Pipeline default: 2" (correct)
4. Reset `well_filter_config.well_filter` (right-click → Reset or backspace to clear)
5. Observe: `well_filter_config.well_filter` shows "None" placeholder (correct)
6. **BUG**: `step_well_filter_config.well_filter` STILL shows "Pipeline default: 2"
7. Reset `well_filter_config.well_filter` a SECOND time
8. NOW `step_well_filter_config.well_filter` correctly shows "None"

## Root Cause Analysis

### Data Model Structure

```
GlobalPipelineConfig (scope_id="")
├── well_filter_config: WellFilterConfig
│   └── well_filter: str (field being changed)
└── step_well_filter_config: StepWellFilterConfig  
    └── well_filter: str (INHERITED from WellFilterConfig - needs refresh)
```

`StepWellFilterConfig` inherits from `WellFilterConfig`, so they share the `well_filter` field.

### Flow on Reset

1. **PFM.reset_parameter()** → calls ParameterOpsService
2. **ParameterOpsService._reset_GenericInfo()** →
   - Calls `manager.state.reset_parameter(param_name)` 
   - This now delegates to `update_parameter(param_name, None)`
3. **ObjectState.update_parameter()** →
   - Sets `self.parameters['well_filter'] = None`
   - Adds 'well_filter' to `self._invalid_fields`
   - Calls `ObjectStateRegistry.invalidate_by_type_and_scope()` - **propagates to sibling ObjectStates**
   - Calls `ObjectStateRegistry.increment_token(notify=False)`
4. **ParameterOpsService** continues →
   - Calls `LiveContextService.increment_token()` (notify=True)
   - Refreshes placeholder for `well_filter_config.well_filter` only
5. **FieldChangeDispatcher.dispatch()** is called with reset event →
   - Loops through siblings looking for matching field
   - Calls `_refresh_single_field(sibling, 'well_filter')` for `step_well_filter_config`

### The Timing Bug

The issue is **ORDER OF OPERATIONS**:

```
A. ParameterOpsService._reset_GenericInfo():
   1. manager.state.reset_parameter('well_filter')  
      → ObjectState.update_parameter(None)
      → ObjectStateRegistry.invalidate_by_type_and_scope() ← INVALIDATES step_well_filter_config._invalid_fields
   2. LiveContextService.increment_token() ← but sibling hasn't resolved yet
   3. refresh_single_placeholder(manager, 'well_filter') ← only refreshes SOURCE, not siblings

B. PFM.reset_parameter() continues:
   4. FieldChangeDispatcher.dispatch(event)
      → _refresh_single_field(step_well_filter_config_manager, 'well_filter')
      → This calls get_resolved_value() which SHOULD see invalid field and recompute...
```

But there's a RACE: When `_refresh_single_field` calls `get_resolved_value()`, it might be using a CACHED resolved value that was computed BEFORE the invalidation propagated.

### Root Cause: DISPATCH CACHE

The bug is in the **dispatch_cycle cache** in `LiveContextService.collect()` (lines 147-152):

```python
dispatch_cache = get_dispatch_cache()
if dispatch_cache is not None:
    dispatch_cache_key = ('live_context',)
    if dispatch_cache_key in dispatch_cache:
        logger.debug("📦 collect_live_context: DISPATCH CACHE HIT")
        return dispatch_cache[dispatch_cache_key]  # ← STALE VALUE!
```

**The sequence**:
1. User resets `well_filter_config.well_filter`
2. `FieldChangeDispatcher.dispatch()` starts with `dispatch_cycle()` context
3. During sibling loop, code calls `LiveContextService.collect()` for some other purpose
4. This populates dispatch_cache with snapshot containing OLD `well_filter = "2"`
5. Token is incremented in `update_parameter()` (notify=False)
6. Sibling refresh triggers `get_resolved_value()` on `step_well_filter_config`
7. `_recompute_invalid_fields()` calls `LiveContextService.collect()`
8. **DISPATCH CACHE HIT** - returns snapshot with stale `well_filter = "2"`!
9. Sibling resolves to stale value

**Second reset works** because:
- The dispatch cache is cleared after each dispatch cycle ends
- On second reset, a NEW dispatch cycle starts with fresh cache
- This time the collect() sees the correct None value

## Relevant Files

| File | Role |
|------|------|
| `openhcs/config_framework/object_state.py` | ObjectState, ObjectStateRegistry, invalidate_by_type_and_scope |
| `openhcs/pyqt_gui/widgets/shared/services/field_change_dispatcher.py` | Sibling refresh logic |
| `openhcs/pyqt_gui/widgets/shared/services/parameter_ops_service.py` | Reset and placeholder refresh |
| `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` | reset_parameter entry point |
| `openhcs/config_framework/live_context_service.py` | Token management |

## Key Methods to Trace

1. `ObjectState.get_resolved_value()` - Does it check `_invalid_fields` for the specific field?
2. `ObjectState._ensure_live_resolved()` - Called by get_resolved_value, checks `_invalid_fields`
3. `FieldChangeDispatcher._refresh_single_field()` - How it refreshes sibling placeholders
4. `ParameterOpsService.refresh_single_placeholder()` - Uses get_resolved_value

## Fix Applied

**Removed dispatch cache entirely.**

The dispatch cache was a micro-optimization that bypassed the TokenCache invalidation mechanism.
The TokenCache in `LiveContextService.collect()` properly handles caching with token-based invalidation.

Files changed:
- `openhcs/config_framework/context_manager.py` - Removed `dispatch_cycle()`, `get_dispatch_cache()`, `_dispatch_cycle_cache`
- `openhcs/config_framework/live_context_service.py` - Removed dispatch cache check in `collect()`
- `openhcs/pyqt_gui/widgets/shared/services/field_change_dispatcher.py` - Removed `dispatch_cycle()` wrapper

