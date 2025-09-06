# Non-Nested Field Reset Placeholder Bug

## Status: OPEN

## Summary
Non-nested fields don't reset their placeholder values properly when a config is saved and then reopened. When reopened, resetting a concrete non-nested field causes the placeholder to show the concrete value instead of the inherited value.

## Reproduction Steps
1. Open configuration UI
2. Set a concrete value in a non-nested field (e.g., `num_workers = 8`)
3. Save the configuration
4. Close and reopen the configuration UI
5. Click the reset button on the field that was set to a concrete value
6. **BUG**: Placeholder shows the concrete value (`8`) instead of the inherited/default value

## Expected Behavior
After reset, the placeholder should show the inherited/default value, not the concrete value that was previously set.

## Root Cause Analysis
This appears to be related to how the configuration cache system interacts with the reset functionality for non-nested fields. When a config is saved and reloaded, the concrete values become part of the cached context, and the reset logic may not be properly excluding them from the inheritance resolution.

## Difference from Fixed Bug
This bug affects **non-nested** fields, whereas the recently fixed bug affected **nested** form managers. The field naming and context building logic is different for non-nested fields, so they may have a separate code path that needs similar fixes.

## Investigation Needed
1. Check how non-nested field reset differs from nested field reset
2. Verify if the exclusion logic works correctly for non-nested fields
3. Examine how the configuration cache affects reset behavior
4. Test if the issue occurs only after save/reload or also in fresh sessions

## Priority
Medium - This affects user experience but has a workaround (users can manually clear the field and it will show the correct placeholder).

## Related Issues
- Fixed: Reset placeholder inheritance for nested form managers (commit dd1a9e7)
- The nested field fix may provide insights for fixing this non-nested field issue
