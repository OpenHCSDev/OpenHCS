# Thread-Local Global Config Architecture Analysis

## Current Architecture

### What is `thread_local_global`?

`thread_local_global` (returned by `get_base_global_config()`) is a **thread-local singleton** that stores the "base" GlobalPipelineConfig instance. It's stored in `_global_config_contexts` dict in `global_config.py`.

### When is it set?

1. **App startup** (`app.py` line 95):
   ```python
   set_global_config_for_editing(GlobalPipelineConfig, self.global_config)
   ```
   - Happens once when the GUI app initializes
   - Sets the cached/default GlobalPipelineConfig

2. **When user saves global config** (`main.py` line 584):
   ```python
   set_global_config_for_editing(GlobalPipelineConfig, new_config)
   ```
   - Updates the thread-local when user saves changes to GlobalPipelineConfig

### When is it used?

**GLOBAL_LIVE_VALUES layer** (`context_layer_builders.py` line 356-364):
```python
thread_local_global = get_base_global_config()
global_live_values = _reconstruct_nested_dataclasses(global_live_values, thread_local_global)
global_live_instance = dataclasses.replace(thread_local_global, **global_live_values)
```

**Purpose**: Merge live values from the GlobalPipelineConfig manager into the thread-local base config.

### The Problem

**`thread_local_global` is NEVER updated when nested managers change!**

Flow when you edit `well_filter_config.well_filter`:
1. User types "3" → `well_filter_config` manager updates
2. `thread_local_global` still has `WellFilterConfig(well_filter=None)` (default)
3. User backspaces → `well_filter_config.well_filter` becomes None
4. When building GLOBAL_LIVE_VALUES for siblings:
   - Gets `{'well_filter_config': (WellFilterConfig, {'well_filter': None})}`
   - Filters out None → empty dict
   - Doesn't update `well_filter_config` field
   - `thread_local_global` still has old `WellFilterConfig(well_filter=None)`
   - But wait - it should have `well_filter=3` from step 1!

**Actually, the issue is different**: `thread_local_global` is only updated when you **save** the GlobalPipelineConfig. So it has the LAST SAVED state, not the current editing state.

When you type "3" in `well_filter_config.well_filter`:
- The GlobalPipelineConfig manager's widgets show "3"
- But `thread_local_global` still has the old saved value (or default)
- When you backspace and we filter out None, we keep the stale value from `thread_local_global`

## Three Proposed Solutions

### Option 1: Update `thread_local_global` when nested managers change

**Approach**: Call `set_global_config_for_editing()` whenever a nested manager in GlobalPipelineConfig changes.

**Implementation**:
```python
# In parameter_form_manager.py, _on_nested_parameter_changed()
if self.config.is_global_config_editing and self.global_config_type is not None:
    # Rebuild GlobalPipelineConfig from current values
    current_values = self.get_current_values()
    new_global_config = self.global_config_type(**current_values)
    set_global_config_for_editing(self.global_config_type, new_global_config)
```

**Pros**:
- ✅ Keeps `thread_local_global` in sync with current editing state
- ✅ Minimal changes to context layer building logic
- ✅ Maintains existing architecture

**Cons**:
- ❌ **Violates the purpose of `thread_local_global`** - it's supposed to be the "saved" config, not the "currently editing" config
- ❌ **Performance**: Rebuilding GlobalPipelineConfig on every nested change is expensive
- ❌ **Semantic confusion**: `set_global_config_for_editing()` is documented as "ONLY for legitimate global config modifications" (saving, loading), not for every keystroke
- ❌ **Side effects**: Other parts of the system might rely on `thread_local_global` being the saved state

### Option 2: Don't use `thread_local_global` as base for GLOBAL_LIVE_VALUES

**Approach**: Build GLOBAL_LIVE_VALUES layer entirely from the GlobalPipelineConfig manager's current values, without merging into `thread_local_global`.

**Implementation**:
```python
# In context_layer_builders.py, GlobalLiveValuesBuilder.build()
global_live_values = _get_manager_values(global_manager, use_user_modified_only)

# Build fresh GlobalPipelineConfig from current manager values
# Don't use thread_local_global at all
global_live_instance = manager.global_config_type(**global_live_values)

return ContextLayer(layer_type=self._layer_type, instance=global_live_instance)
```

**Pros**:
- ✅ **Correct semantics**: GLOBAL_LIVE_VALUES truly reflects the current live state
- ✅ **No stale data**: Always uses current manager values
- ✅ **Simpler logic**: No need for `_reconstruct_nested_dataclasses()` merging
- ✅ **Preserves `thread_local_global` purpose**: It remains the "saved" config

**Cons**:
- ❌ **Incomplete data**: `get_current_values()` might not include all fields (only user-modified or visible fields)
- ❌ **Dataclass construction**: Can't construct GlobalPipelineConfig if required fields are missing
- ❌ **Loss of non-user-set fields**: Fields that weren't edited won't be in the layer

### Option 3: Track user-cleared fields separately and explicitly clear them

**Approach**: Add a new tracking set `_user_cleared_fields` to distinguish between "never set (None)" and "user cleared to None".

**Implementation**:
```python
# In parameter_form_manager.py
self._user_cleared_fields = set()  # New tracking

# When user backspaces to clear:
def _on_widget_value_changed(self, param_name, value):
    if value is None and param_name in self._user_set_fields:
        self._user_cleared_fields.add(param_name)
    # ...

# In _reconstruct_nested_dataclasses():
if field_name in user_cleared_fields:
    # User explicitly cleared this - mark for removal
    reconstructed[field_name] = CLEARED_SENTINEL
```

Then in context merging, handle `CLEARED_SENTINEL` specially to remove stale values.

**Pros**:
- ✅ **Precise semantics**: Distinguishes "never set" from "user cleared"
- ✅ **Correct behavior**: User-cleared fields properly override stale values
- ✅ **Preserves inheritance**: Non-cleared None values still inherit

**Cons**:
- ❌ **Complex**: Requires new tracking mechanism and sentinel values
- ❌ **Invasive**: Changes needed in multiple places (tracking, reconstruction, merging)
- ❌ **Maintenance burden**: More state to track and keep consistent
- ❌ **Edge cases**: What happens when user clears, then sets again, then clears?

## Recommendation

**Option 2** is the cleanest solution because:

1. **Semantic correctness**: GLOBAL_LIVE_VALUES should reflect the current live editing state, not the saved state
2. **Architectural clarity**: Separates "saved config" (`thread_local_global`) from "currently editing config" (manager values)
3. **Simplicity**: Removes the need for complex merging logic

However, we need to handle the "incomplete data" problem. The solution is to use `get_current_values()` (not `get_user_modified_values()`) which includes ALL fields, and reconstruct nested dataclasses from the nested managers' current values.

## Implementation Plan for Option 2

1. Modify `GlobalLiveValuesBuilder.build()` to build fresh GlobalPipelineConfig from manager's current values
2. Use `get_current_values()` to get ALL fields (not just user-modified)
3. Reconstruct nested dataclasses from nested managers' current values
4. Don't merge into `thread_local_global` at all
5. Keep filtering out None values in nested dataclasses to preserve inheritance

