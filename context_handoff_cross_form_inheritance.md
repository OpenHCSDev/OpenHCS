# Context Handoff: Cross-Form Inheritance Issue

## Current Status: FAILING TEST - Cross-Form Inheritance Not Working

### Test Failure Details
- **Test**: `test_comprehensive_inheritance_chains` 
- **Expected**: `path_planning_config.well_filter` should show `'Pipeline default: test_value_1'`
- **Actual**: `path_planning_config.well_filter` shows `'Pipeline default: (none)'`
- **Root Cause**: Cross-form inheritance not working between `well_filter_config` → `path_planning_config`

### What's Working ✅
1. **Enhanced decorator events system infrastructure** - implemented correctly
2. **Context building** - `_build_context_from_current_form_values()` working
3. **Event emission/listening** - `ContextEventCoordinator` working
4. **Reset button updates placeholders** - user confirmed this works
5. **UI loads without crashes** - all infrastructure in place

### What's Broken ❌
1. **Cross-form inheritance**: When `well_filter_config.well_filter = 'test_value_1'` is set, `path_planning_config.well_filter` doesn't inherit this value
2. **Pipeline config placeholders**: Showing static defaults instead of thread-local defaults

## Inheritance Chains (from documentation)
```
well_filter_config.well_filter → path_planning_config.well_filter
step_well_filter_config.well_filter → step_materialization_config.well_filter
```

## Technical Implementation Status

### Enhanced Decorator Events System ✅
**Location**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py:220-228`
```python
# Register for automatic refresh events if global_config_type is provided
if self.global_config_type:
    from openhcs.core.lazy_config import _context_event_coordinator
    _context_event_coordinator.register_listener(self, self.global_config_type)
    
    # Connect parameter changes to emit context change events for cross-form updates
    self.parameter_changed.connect(
        lambda param_name, value: _context_event_coordinator.emit_context_change(self.global_config_type)
    )
```

### Context Event Coordinator ✅
**Location**: `openhcs/core/lazy_config.py:31-54`
- Implemented with weak references
- `register_listener()` and `emit_context_change()` working
- Called from `set_current_global_config()` in global_config.py

### Context Provider Setup ✅ FIXED
**Location**: `openhcs/pyqt_gui/windows/config_window.py:294-302`
```python
if is_lazy_dataclass:
    # For lazy configs: use thread-local context for proper inheritance
    # This ensures pipeline config forms show thread-local defaults in placeholders
    from openhcs.core.config import GlobalPipelineConfig
    context_provider = lambda: get_current_global_config(GlobalPipelineConfig)
```

## Issues Identified

### Issue 1: Cross-Form Inheritance Not Working
**Problem**: When `well_filter_config.well_filter` changes, `path_planning_config` doesn't inherit the value
**Expected Flow**:
1. User sets `well_filter_config.well_filter = 'test_value_1'`
2. `parameter_changed` signal emitted → `_context_event_coordinator.emit_context_change()`
3. All forms refresh → `path_planning_config` calls context provider
4. Context provider builds context with updated `well_filter_config.well_filter = 'test_value_1'`
5. `path_planning_config.well_filter` shows `'Pipeline default: test_value_1'`

**Current Behavior**: Step 4-5 failing - inheritance not working

### Issue 2: Pipeline Config Placeholders Wrong ✅ FIXED
**Problem**: Pipeline config forms showing static defaults instead of thread-local defaults
**Expected**: Lazy dataclass placeholders should show thread-local context values
**Actual**: Showing static default values
**Fix Applied**: Updated context provider for lazy configs to use thread-local context instead of current form values

## Key Files Modified

### Core Infrastructure
- `openhcs/core/lazy_config.py` - ContextEventCoordinator implementation
- `openhcs/core/context/global_config.py` - Simplified thread-local storage + event emission
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` - Enhanced with context providers

### UI Components  
- `openhcs/pyqt_gui/windows/config_window.py` - Context provider setup
- `openhcs/pyqt_gui/widgets/step_parameter_editor.py` - Context provider for orchestrator

### Manual Coordination Removed
- All `_refresh_all_parameter_form_placeholders()` calls removed
- Manual sibling coordination methods commented out

## Debug Evidence

### Test Output Shows Infrastructure Working
```
🔍 CONTEXT BUILD DEBUG: well_filter_config building context with exclude_field='None'
🔍 CONTEXT DEBUG: current_dataclass_instance=WellFilterConfig(well_filter=None, well_filter_mode=<WellFilterMode.INCLUDE: 'include'>)
```

### Reset Button Works (User Confirmed)
- When reset button clicked → placeholders update correctly
- Proves enhanced decorator events system infrastructure is working
- Proves context building and event emission/listening works

## Next Steps for Agent

### Priority 1: Fix Cross-Form Inheritance
1. **Debug parameter change flow**: Verify `parameter_changed` signal actually emitted when test sets value
2. **Debug context building**: Check if `_build_context_from_current_form_values()` includes updated values
3. **Debug inheritance resolution**: Check if `path_planning_config` can find `well_filter_config.well_filter` in context

### Priority 2: Fix Pipeline Config Placeholders  
1. **Check context provider**: Verify lazy dataclass forms use thread-local context correctly
2. **Debug placeholder resolution**: Check if thread-local defaults being used vs static defaults

### Investigation Commands
```bash
# Run the failing test with debug output
python -m pytest tests/pyqt_gui/integration/test_reset_placeholder_simplified.py::TestResetPlaceholderInheritance::test_comprehensive_inheritance_chains -v --tb=short

# Check if parameter_changed signal emitted
# Add debug prints in _emit_parameter_change method

# Check context building
# Add debug prints in _build_context_from_current_form_values method
```

## Plan Reference
**Original Plan**: `plans/ui/plan_02_enhanced_decorator_events.md`
- Plan successfully implemented through all 3 phases
- Infrastructure working correctly
- Issue is in the cross-form inheritance mechanism specifically

## User Feedback
- "the test is failing correctly" - test correctly identifies the broken functionality
- "when i click on the reset button the placeholder does update" - infrastructure confirmed working
- Two separate inheritance chains being tested, not one complex chain

---
**Status**: Ready for agent to debug cross-form inheritance mechanism and pipeline config placeholder resolution.
