# Bug Report: Direct Field Reset Placeholder Shows Wrong Value

## Summary
When resetting a direct field (like `materialization_results_path`) in the configuration UI, the placeholder shows the previously set concrete value instead of the actual global default value.

## Expected Behavior
1. User sets `materialization_results_path = "/custom/results/path"` (concrete value)
2. User clicks the reset button for `materialization_results_path`
3. Field should show `Pipeline default: <global_default>` (the actual global default) as placeholder

## Actual Behavior
1. User sets `materialization_results_path = "/custom/results/path"` (concrete value)
2. User clicks the reset button for `materialization_results_path`
3. **BUG**: Field shows `Pipeline default: /custom/results/path` (the previous concrete value) instead of the global default

## Root Cause
The reset functionality for direct fields is not properly reverting to the actual global default value. Instead of fetching and displaying the global default, it's retaining or showing the previously set concrete value.

## Affected Components
- **Direct fields** on `PipelineConfig` (like `materialization_results_path`, `output_dir_suffix`, etc.)
- **Reset button functionality** in `ParameterFormManager`
- **Placeholder logic** for direct fields after reset

## Not Affected
- **Nested dataclass inheritance** works correctly (step editor properly inherits from pipeline config)
- **Widget creation** is robust with proper fallback handling
- **String field placeholders** may work differently (need separate testing)

## Test to Reproduce

### Automated Test
Run the following pytest command to reproduce the bug:

```bash
cd /home/ts/code/projects/openhcs
python -m pytest tests/pyqt_gui/integration/test_end_to_end_workflow_foundation.py -k "reset_placeholder_bug_direct_field" -v -s
```

### Expected Test Output (Bug Present)
```
🔍 DIRECT FIELD materialization_results_path AFTER RESET:
  All text: 'Pipeline default: /custom/results/path Pipeline default: /custom/results/path'
  Individual texts: {'placeholder': 'Pipeline default: /custom/results/path', 'tooltip': 'Pipeline default: /custom/results/path', 'text': ''}
  Previously set concrete value: /custom/results/path
🚨 BUG: Direct field placeholder shows concrete value '/custom/results/path' instead of global default
```

### Expected Test Output (Bug Fixed)
```
🔍 DIRECT FIELD materialization_results_path AFTER RESET:
  All text: 'Pipeline default: <global_default> Pipeline default: <global_default>'
  Individual texts: {'placeholder': 'Pipeline default: <global_default>', 'tooltip': 'Pipeline default: <global_default>', 'text': ''}
  Previously set concrete value: /custom/results/path
✅ GOOD: Direct field placeholder shows global default (not concrete value '/custom/results/path')
```

### Manual Test Steps
1. Launch OpenHCS application
2. Open any plate and initialize it
3. Open Configuration window (Edit Config button)
4. Find the `materialization_results_path` field (should show default placeholder)
5. Change `materialization_results_path` to `/custom/results/path`
6. Save configuration
7. Click the reset button next to `materialization_results_path` field
8. **BUG**: Field shows `Pipeline default: /custom/results/path` instead of the actual global default

## Technical Details

### Test Scenario Configuration
```python
TestScenario(
    name="reset_placeholder_bug_direct_field",
    field_to_test=FieldModificationSpec(
        field_name="materialization_results_path",
        config_section="direct",
        modification_value="/custom/results/path"
    ),
    orchestrator_config={
        "materialization_results_path": "/custom/results/path",
        "output_dir_suffix": "_test",
        "sub_dir": "images",
        "well_filter": ["A01", "A02"]
    }
)
```

### Key Test Steps
1. **Set concrete value**: `materialization_results_path = "/custom/results/path"`
2. **Reset field**: Click reset button
3. **Reopen config window**: To see placeholder behavior
4. **Check placeholder**: Should show `Pipeline default: <global_default>`, not `Pipeline default: /custom/results/path`

## Investigation Areas

### Likely Issue Locations
1. **`ParameterFormManager.reset_parameter()`** - May not be getting correct global default
2. **`ParameterFormManager._get_reset_value()`** - May be returning wrong value for direct fields
3. **Placeholder application logic** - May be using cached/wrong value
4. **Global config resolution** - May not be properly accessing global defaults

### Widget Creation Status
✅ **Widget creation is working correctly** - The fallback system properly handles magicgui failures and creates appropriate widgets.

### Inheritance Status  
✅ **Nested dataclass inheritance works correctly** - Step editor properly shows `Pipeline default: _test` when inheriting from pipeline config.

## Priority
**High** - This affects core configuration functionality and user experience when resetting fields to defaults.
