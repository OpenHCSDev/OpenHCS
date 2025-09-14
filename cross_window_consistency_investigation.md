# Cross-Window Consistency Investigation

## What the Test is Testing

The test `test_comprehensive_inheritance_chains` is specifically testing **cross-window placeholder consistency** between:

1. **Pipeline Config Window**: Where users set concrete values for configuration fields
2. **Step Editor Window**: Where users edit individual step parameters

### Test Flow
```python
# 1. Set concrete values in pipeline config
target_configs = ['well_filter_config', 'step_well_filter_config']
for i, config in enumerate(target_configs):
    test_value = f'concrete_{i+1}'  # concrete_1, concrete_2
    run_test(context, ('edit', 'well_filter', test_value, config))

# 2. Capture placeholders from pipeline config
pipeline_placeholders = _capture_pipeline_placeholders(context)

# 3. Save and close pipeline config
context = _close_config_window(context)

# 4. Open step editor
step_editor_window, step_form_manager = _open_step_editor_and_get_form_manager(context)

# 5. Assert step editor shows same values as pipeline config
_assert_step_editor_placeholders_match(step_form_manager, pipeline_placeholders)
```

### Expected Behavior
- Pipeline config shows: `step_well_filter_config.well_filter = 'Pipeline default: concrete_2'`
- Step editor should show: `step_well_filter_config.well_filter = 'Pipeline default: concrete_2'`

### Actual Behavior (FAILING)
- Pipeline config shows: `step_well_filter_config.well_filter = 'Pipeline default: concrete_2'`
- Step editor shows: `step_well_filter_config.well_filter = 'Pipeline default: 1'` ❌

## Mental Model of Configuration Architecture

### Thread-Local Context System
```
┌─────────────────────────────────────────────────────────────┐
│                Thread-Local Context                        │
│  get_current_global_config(GlobalPipelineConfig)          │
│                                                            │
│  GlobalPipelineConfig(                                     │
│    well_filter_config=WellFilterConfig(...),              │
│    step_well_filter_config=StepWellFilterConfig(          │
│      well_filter='concrete_2'  ← Should be here           │
│    ),                                                      │
│    ...                                                     │
│  )                                                         │
└─────────────────────────────────────────────────────────────┘
                              ↑
                              │
                    set_current_global_config()
                              │
┌─────────────────────────────────────────────────────────────┐
│                Pipeline Config Window                      │
│                                                            │
│  User sets: step_well_filter_config.well_filter = 'concrete_2' │
│  Saves config → Updates thread-local context              │
└─────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────┐
│                Step Editor Window                          │
│                                                            │
│  Reads thread-local context for placeholder resolution    │
│  Should show: 'Pipeline default: concrete_2'              │
│  Actually shows: 'Pipeline default: 1' ❌                 │
└─────────────────────────────────────────────────────────────┘
```

### Configuration Flow (Expected)
1. **Pipeline Config**: User sets concrete values
2. **Save**: `set_current_global_config(GlobalPipelineConfig, new_config)`
3. **Thread-Local**: Context updated with concrete values
4. **Step Editor**: Reads thread-local context via `get_current_global_config()`
5. **Placeholder Resolution**: Shows concrete values from context

### Configuration Flow (Actual - Broken)
1. **Pipeline Config**: User sets concrete values ✅
2. **Save**: Context update happens ❓
3. **Thread-Local**: Still contains old values ❌
4. **Step Editor**: Reads stale context ❌
5. **Placeholder Resolution**: Shows old static defaults ❌

## What I've Tried

### Attempt 1: Add Missing `global_config_type` Parameter
**Theory**: PyQt ParameterFormManager was missing `global_config_type` parameter that Textual version had.

**Changes Made**:
```python
# Added to PyQt ParameterFormManager constructor
def __init__(self, ..., global_config_type: Optional[Type] = None):

# Updated step editor to pass GlobalPipelineConfig
self.form_manager = ParameterFormManager(
    ...,
    global_config_type=GlobalPipelineConfig
)
```

**Result**: ❌ Still failing with same error
- Expected: `'Pipeline default: concrete_2'`
- Got: `'Pipeline default: 1'`

**Analysis**: The parameter was added correctly, but the underlying issue persists.

## Current Hypothesis

The issue is **NOT** in the step editor's ability to read thread-local context. The issue is that the **pipeline config window is not properly updating the thread-local context** when concrete values are set.

### Evidence
From debug output:
```
🔍 LAZY RESOLUTION DEBUG: Context has step_well_filter_config.well_filter = '1'
```

This shows the thread-local context still contains the old value `'1'`, not the new concrete value `'concrete_2'`.

### Root Cause Theory
The test calls:
```python
run_test(context, ('edit', 'well_filter', 'concrete_2', 'step_well_filter_config'))
```

But this edit operation in the pipeline config window is **not updating the thread-local context**. The values are being set in the UI widgets, but they're not being saved to the global context that the step editor reads from.

## Next Investigation Steps

1. **Verify thread-local context updates**: Check if `set_current_global_config()` is being called when pipeline config values are edited
2. **Check save mechanism**: Verify that pipeline config save operation properly reconstructs and saves the complete configuration
3. **Debug context timing**: Ensure thread-local context is updated before step editor opens
4. **Trace value flow**: Follow the exact path from UI widget → form manager → config reconstruction → thread-local context

## Key Questions

1. **When is thread-local context updated?** 
   - On every field edit?
   - Only on save?
   - Never? (Bug)

2. **What triggers context updates?**
   - Form manager field changes?
   - Config window save button?
   - Automatic background updates?

3. **Is the test's edit operation actually saving?**
   - Does `run_test(('edit', ...))` trigger a save?
   - Or just UI widget updates?

## Test-Specific Details

The test uses `run_test()` which calls `edit_field()`:
```python
def edit_field(context, field_name, value, config_section):
    widget = find_widget(context, field_name, config_section)
    set_widget_value_enhanced(widget, value)
    # Does this trigger save/context update? ❓
```

**Critical Question**: Does setting widget values automatically update thread-local context, or does it require an explicit save operation?

## Detailed Error Analysis

### Test Failure Details
```
AssertionError: Placeholder mismatch for step_materialization_config.well_filter:
expected 'Pipeline default: concrete_2', got 'Pipeline default: 1'
```

### Debug Output Analysis
```
🔍 LAZY RESOLUTION DEBUG: Context has step_well_filter_config.well_filter = '1'
```

This debug line appears during pipeline config window operation, showing that even the pipeline config window is reading `'1'` from context, not `'concrete_2'`.

### Pipeline vs Step Editor Mismatch
- **Pipeline Config Captured**: `'Pipeline default: concrete_2'` ✅
- **Step Editor Shows**: `'Pipeline default: 1'` ❌

This suggests:
1. Pipeline config widgets show correct values (captured correctly)
2. But thread-local context is never updated with those values
3. Step editor reads stale thread-local context

### Widget vs Context Disconnect
The pipeline config window has two sources of truth:
1. **Widget Values**: What the user sees and edits (shows `concrete_2`)
2. **Thread-Local Context**: What lazy resolution reads (shows `1`)

The test captures from widget values but step editor reads from thread-local context.

## Architecture Problem

### Current (Broken) Flow
```
User Edit → Widget Value → [MISSING LINK] → Thread-Local Context
                ↓                              ↓
        Pipeline Capture                Step Editor Read
        (concrete_2) ✅                     (1) ❌
```

### Expected Flow
```
User Edit → Widget Value → Form Manager → Config Reconstruction → Thread-Local Context
                ↓                                                        ↓
        Pipeline Capture                                        Step Editor Read
        (concrete_2) ✅                                            (concrete_2) ✅
```

## Investigation Focus

The missing link is likely in the **Form Manager → Config Reconstruction → Thread-Local Context** chain.

### Key Components to Investigate
1. **ParameterFormManager.parameter_changed signal**: Does it trigger context updates?
2. **Config reconstruction**: Does form manager properly build updated config?
3. **Thread-local updates**: When/how is `set_current_global_config()` called?
4. **Test save mechanism**: Does the test actually save, or just edit widgets?

### Specific Code Paths to Trace
1. `edit_field()` → `set_widget_value_enhanced()` → ?
2. Widget change → `parameter_changed` signal → ?
3. Form manager → `get_current_values()` → config reconstruction → ?
4. Config save → `set_current_global_config()` → thread-local update
