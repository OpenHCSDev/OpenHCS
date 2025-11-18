# REVISED OpenHCS Reactive UI Performance Optimization Plan

**Status**: READY FOR PROFILING  
**Date**: 2025-11-18  
**Revision**: Based on reviewer feedback

---

## Executive Summary

**CRITICAL CHANGE**: The original plan had a fatal flaw in Phase 1 that would ADD O(n_steps) work instead of removing it. This revision:

1. **REMOVES Phase 1** (step-based caching) - it was worse than current implementation
2. **FIXES critical scope_filter bug** in Phase 2 (would break multi-plate scenarios)
3. **ADDS Step 0: PROFILE FIRST** - measure before optimizing
4. **SIMPLIFIES approach** - only optimize proven bottlenecks
5. **VERIFIES Phase 4 exists** ✅ (confirmed via git show)

---

## Step 0: PROFILE FIRST (NEW - MANDATORY)

**Goal**: Measure actual performance to identify real bottlenecks

### 0.1 Add Performance Instrumentation

**File**: `openhcs/pyqt_gui/widgets/config_preview_formatters.py`

Add timing decorators to key functions:

```python
import time
from functools import wraps

def profile_function(func):
    """Decorator to measure function execution time."""
    @wraps(func)
    def wrapper(*args, **kwargs):
        start = time.perf_counter()
        result = func(*args, **kwargs)
        elapsed = (time.perf_counter() - start) * 1000  # ms
        logger.info(f"⏱️ {func.__name__} took {elapsed:.2f}ms")
        return result
    return wrapper

# Apply to:
@profile_function
def check_step_has_unsaved_changes(...):
    ...

@profile_function
def check_config_has_unsaved_changes(...):
    ...
```

**File**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

Add call counter:

```python
# Class-level counters
_collect_live_context_calls = 0
_collect_live_context_cache_hits = 0

@classmethod
def collect_live_context(cls, ...):
    cls._collect_live_context_calls += 1
    # ... existing code ...
    logger.info(f"📊 collect_live_context called {cls._collect_live_context_calls} times (cache hits: {cls._collect_live_context_cache_hits})")
```

### 0.2 Run Profiling Scenarios

**Scenario 1: Single Keystroke**
```python
# Open GlobalPipelineConfig editor
# Type single character in well_filter field
# Measure:
#   - Time in check_step_has_unsaved_changes()
#   - Number of collect_live_context() calls
#   - Number of manager iterations in fast-path
```

**Scenario 2: Rapid Typing**
```python
# Type 10 characters rapidly
# Measure:
#   - Total time for all updates
#   - Number of cross-window signals
#   - Number of collect_live_context() calls
```

**Scenario 3: Multi-Plate**
```python
# Load 2 plates
# Edit config in plate 1
# Measure:
#   - Scope filtering correctness
#   - Cache behavior across plates
```

### 0.3 Analyze Results

**Decision Matrix**:

| Measurement | Threshold | Action if Exceeded |
|-------------|-----------|-------------------|
| Single keystroke > 16ms | Implement optimizations | |
| collect_live_context() > 1 call/keystroke | Implement Phase 2.2 | |
| Saved snapshot > 1 collection/update | Implement Phase 2.3 | |
| Cross-window signals > 1/debounce period | Implement Phase 3 | |

**If all measurements are below thresholds**: **STOP - No optimization needed!**

---

## Phase 1: REMOVED ❌

**Original Plan**: Step-based caching with `_steps_with_unsaved_changes`

**Why Removed**: Reviewer correctly identified that this adds O(n_listeners × n_steps) work on EVERY keystroke, which is worse than the current O(n_managers) fast-path with early exit.

**Alternative (if profiling shows need)**: Type-based caching (see Phase 1-ALT below)

---

## Phase 1-ALT: Type-Based Caching (CONDITIONAL)

**Only implement if profiling shows fast-path is a bottleneck**

**Goal**: O(1) lookup without O(n_steps) iteration overhead

### 1-ALT.1 Add Type-Based Cache

**File**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

```python
# Map: config type → set of changed field names
# Example: LazyWellFilterConfig → {'well_filter', 'well_filter_mode'}
_configs_with_unsaved_changes: Dict[Type, Set[str]] = {}

# Cache size limit to prevent unbounded growth
MAX_CONFIG_TYPE_CACHE_ENTRIES = 50  # Reasonable limit for typical pipelines
```

### 1-ALT.2 Populate on Change

**File**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

Add method to ParameterFormManager:

```python
def _mark_config_type_with_unsaved_changes(self, param_name: str, value: Any):
    """Mark config TYPE (not step) as having unsaved changes.

    Includes cache size monitoring to prevent unbounded growth.
    """
    # Extract config attribute from param_name
    config_attr = param_name.split('.')[0] if '.' in param_name else param_name

    # Get config type from context_obj or object_instance
    config = getattr(self.object_instance, config_attr, None)
    if config is None:
        config = getattr(self.context_obj, config_attr, None)

    if config is not None and dataclasses.is_dataclass(config):
        config_type = type(config)

        # PERFORMANCE: Monitor cache size to prevent unbounded growth
        if len(type(self)._configs_with_unsaved_changes) > type(self).MAX_CONFIG_TYPE_CACHE_ENTRIES:
            logger.warning(
                f"⚠️ Config type cache exceeded {type(self).MAX_CONFIG_TYPE_CACHE_ENTRIES} entries - clearing"
            )
            type(self)._configs_with_unsaved_changes.clear()

        if config_type not in type(self)._configs_with_unsaved_changes:
            type(self)._configs_with_unsaved_changes[config_type] = set()

        # Extract field name from param_name
        field_name = param_name.split('.')[-1] if '.' in param_name else param_name
        type(self)._configs_with_unsaved_changes[config_type].add(field_name)
```

**Call site** - Modify `_emit_cross_window_change()`:

```python
def _emit_cross_window_change(self, param_name: str, value: object):
    """Emit cross-window context change signal."""
    # Skip if blocked
    if getattr(self, '_block_cross_window_updates', False):
        logger.info(f"🚫 _emit_cross_window_change BLOCKED for {self.field_id}.{param_name}")
        return

    # PERFORMANCE: Mark config type with unsaved changes (Phase 1-ALT)
    self._mark_config_type_with_unsaved_changes(param_name, value)

    # ... rest of existing code (signal emission) ...
```

### 1-ALT.3 Use in Fast-Path

**File**: `openhcs/pyqt_gui/widgets/config_preview_formatters.py`

Replace lines 407-460 with:

```python
# PERFORMANCE: O(1) type-based cache lookup
has_any_relevant_changes = False
for config_attr, config in step_configs.items():
    config_type = type(config)
    if config_type in ParameterFormManager._configs_with_unsaved_changes:
        has_any_relevant_changes = True
        logger.debug(f"🔍 Type-based cache hit for {config_type.__name__}")
        break

if not has_any_relevant_changes:
    logger.debug(f"🔍 No relevant changes for step - skipping detailed check")
    return False
```

**Complexity**: O(n_configs) where n_configs = 5-7 (number of config attrs on step), NOT O(n_steps × n_managers)

---

## Phase 2: Batch Context Collection (REVISED WITH SCOPE_FILTER FIX)

**Goal**: Eliminate redundant `collect_live_context()` calls

### 2.1 Add Update Cycle Tracking (WITH SCOPE_FILTER)

**File**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

```python
# CRITICAL FIX: Cache key MUST include scope_filter for multi-plate correctness
# NOTE: scope_filter is a STRING (plate path like "plate1.yaml"), not a dict!
_update_cycle_context_cache: Dict[Tuple[int, Optional[str]], LiveContextSnapshot] = {}
```

### 2.2 Batch Context Collection (CONDITIONAL - ONLY IF PROFILING SHOWS NEED)

**File**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

```python
@classmethod
def collect_live_context(cls, scope_filter=None, ...):
    current_token = cls._live_context_token_counter

    # CRITICAL: Include scope_filter in cache key
    # scope_filter is a STRING (plate path), not a dict - it's already hashable
    cache_key = (current_token, scope_filter)
    
    # Check cache
    if cache_key in cls._update_cycle_context_cache:
        cls._collect_live_context_cache_hits += 1
        logger.debug(f"🚀 collect_live_context: Cache HIT (token={current_token}, scope={scope_key})")
        return cls._update_cycle_context_cache[cache_key]
    
    # ... existing collection logic ...
    
    # Cache result
    cls._update_cycle_context_cache[cache_key] = snapshot
    return snapshot
```

### 2.3 Clear Cache on Token Increment

```python
def _on_parameter_changed_root(self, ...):
    # ... existing code ...
    type(self)._live_context_token_counter += 1

    # Clear update cycle cache when token changes
    type(self)._update_cycle_context_cache.clear()
```

### 2.4 Batch Saved Context Snapshot ✅ ALREADY IMPLEMENTED

**Status**: This optimization is **already implemented** in `pipeline_editor.py:1535-1544`

**Evidence**:
```python
# openhcs/pyqt_gui/widgets/pipeline_editor.py lines 1535-1544
# PERFORMANCE: Collect saved context snapshot ONCE for ALL steps
saved_managers = ParameterFormManager._active_form_managers.copy()
saved_token = ParameterFormManager._live_context_token_counter

try:
    ParameterFormManager._active_form_managers.clear()
    ParameterFormManager._live_context_token_counter += 1
    saved_context_snapshot = ParameterFormManager.collect_live_context(scope_filter=self.current_plate)
finally:
    ParameterFormManager._active_form_managers[:] = saved_managers
    ParameterFormManager._live_context_token_counter = saved_token
```

The saved snapshot is collected **once** and passed to all steps via `saved_context_snapshot=saved_context_snapshot`.

**Action Required**: None - just verify this is working correctly during profiling

---

## Phase 3: Batch Cross-Window Updates (CONDITIONAL)

**Only implement if profiling shows excessive signal emissions**

**Goal**: Batch multiple rapid changes into single update

### 3.1 Add Batching Infrastructure

**File**: `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

```python
# Batching for cross-window updates
# Store manager reference to avoid fragile string matching
# Format: List[(manager, param_name, value, obj_instance, context_obj)]
_pending_cross_window_changes: List[Tuple['ParameterFormManager', str, Any, Any, Any]] = []
_cross_window_batch_timer: Optional['QTimer'] = None
```

### 3.2 Batch Changes

```python
def _emit_cross_window_change(self, param_name: str, value: object):
    """Batch cross-window changes for performance."""
    from PyQt6.QtCore import QTimer

    # Skip if blocked
    if getattr(self, '_block_cross_window_updates', False):
        return

    # PERFORMANCE: Store manager reference to avoid fragile string matching later
    # This is type-safe and avoids issues with overlapping field_id prefixes
    type(self)._pending_cross_window_changes.append(
        (self, param_name, value, self.object_instance, self.context_obj)
    )

    # Schedule batched emission
    if type(self)._cross_window_batch_timer is None:
        type(self)._cross_window_batch_timer = QTimer()
        type(self)._cross_window_batch_timer.setSingleShot(True)
        type(self)._cross_window_batch_timer.timeout.connect(
            lambda: type(self)._emit_batched_cross_window_changes()
        )

    # Restart timer (trailing debounce)
    type(self)._cross_window_batch_timer.start(self.CROSS_WINDOW_REFRESH_DELAY_MS)
```

### 3.3 Emit Batched Changes

```python
@classmethod
def _emit_batched_cross_window_changes(cls):
    """Emit all pending changes as individual signals (but only after batching period).

    Uses stored manager references instead of fragile string matching.
    """
    if not cls._pending_cross_window_changes:
        return

    logger.info(f"📦 Emitting {len(cls._pending_cross_window_changes)} batched cross-window changes")

    # Deduplicate: Keep only the latest value for each (manager, param_name) pair
    # This handles rapid typing where same field changes multiple times
    latest_changes = {}  # (manager_id, param_name) → (manager, value, obj_instance, context_obj)
    for manager, param_name, value, obj_instance, context_obj in cls._pending_cross_window_changes:
        key = (id(manager), param_name)
        latest_changes[key] = (manager, param_name, value, obj_instance, context_obj)

    # Emit each change using stored manager reference (type-safe, no string matching)
    for manager, param_name, value, obj_instance, context_obj in latest_changes.values():
        field_path = f"{manager.field_id}.{param_name}"
        manager.context_value_changed.emit(field_path, value, obj_instance, context_obj)

    # Clear pending changes
    cls._pending_cross_window_changes.clear()
```

---

## Phase 4: Verify Flash Detection Batching ✅

**Status**: VERIFIED - `_check_with_batch_resolution()` exists (commit fe62c409)

**Action**: No implementation needed, just verify it's being used correctly.

**File**: `openhcs/pyqt_gui/widgets/mixins/cross_window_preview_mixin.py`

Confirmed method exists and is used for batch resolution of flash detection.

---

## Cache Invalidation Rules (CRITICAL - ADDRESSES REVIEWER CONCERN)

### When to Clear Caches

**1. Form Close (ANY form)**
```python
# In unregister_from_cross_window_updates()
type(self)._configs_with_unsaved_changes.clear()  # Phase 1-ALT
type(self)._update_cycle_context_cache.clear()     # Phase 2
type(self)._pending_cross_window_changes.clear()   # Phase 3
```

**2. Token Increment (EVERY change)**
```python
# In _on_parameter_changed_root()
type(self)._live_context_token_counter += 1
type(self)._update_cycle_context_cache.clear()  # Phase 2 only
```

**3. Plate Switch**
```python
# In plate manager when switching plates
ParameterFormManager._update_cycle_context_cache.clear()
# Scope-specific caches are automatically invalidated by scope_filter in cache key
```

**4. Pipeline Reload**
```python
# In pipeline editor when reloading pipeline
ParameterFormManager._configs_with_unsaved_changes.clear()
ParameterFormManager._update_cycle_context_cache.clear()
```

**5. Save Operation**
```python
# In save handler
ParameterFormManager._configs_with_unsaved_changes.clear()
# Don't clear update_cycle_context_cache (still valid for current token)
```

---

## Testing Strategy (REVISED)

### Test 1: Scope Filtering Correctness (CRITICAL)

```python
# Load 2 plates
plate1 = load_plate("plate1")
plate2 = load_plate("plate2")

# Edit config in plate1
edit_global_config(plate1, well_filter=5)

# Verify:
# 1. Only plate1 steps show unsaved changes
# 2. Plate2 steps are unaffected
# 3. Cache keys include scope_filter
# 4. No cache pollution between plates
```

### Test 2: Cache Invalidation

```python
# Open config editor
# Make change → verify cache populated
# Close editor → verify cache cleared
# Reopen editor → verify cache empty (not stale)
```

### Test 3: Performance Benchmarks

**Only run AFTER profiling shows need for optimization**

| Scenario | Before | Target | Measurement |
|----------|--------|--------|-------------|
| Single keystroke | Baseline | <16ms | Time to UI update |
| Rapid typing (10 keys) | Baseline | 1 signal | Number of signals |
| collect_live_context() calls | Baseline | 1/update | Call count |
| Multi-plate editing | Baseline | No pollution | Scope correctness |

---

## Risk Assessment (REVISED)

### Low Risk ✅
- **Phase 2.2-2.4** (Context caching): Automatic invalidation on token change, scope_filter in cache key
- **Phase 4** (Verify batching): Already exists, just verification

### Medium Risk ⚠️
- **Phase 1-ALT** (Type-based caching): Need to ensure type matching is correct
- **Phase 3** (Batch cross-window): Need to ensure signal order is preserved

### High Risk ❌
- **Original Phase 1** (Step-based caching): REMOVED - would add O(n_steps) work

### Critical Bugs Fixed 🐛
- **scope_filter not in cache key**: Would break multi-plate scenarios
- **Cache invalidation unclear**: Now explicitly defined for all scenarios

---

## Implementation Checklist (REVISED)

### Step 0: PROFILE FIRST ✅ MANDATORY
- [ ] Add timing decorators to key functions
- [ ] Add call counters to collect_live_context()
- [ ] Run profiling scenarios (single keystroke, rapid typing, multi-plate)
- [ ] Analyze results and decide which phases to implement
- [ ] **STOP if all measurements are below thresholds**

### Phase 1-ALT: Type-Based Caching (CONDITIONAL)
- [ ] **ONLY implement if profiling shows fast-path is bottleneck**
- [ ] Add `_configs_with_unsaved_changes` cache
- [ ] Implement `_mark_config_type_with_unsaved_changes()`
- [ ] Replace fast-path with type-based lookup
- [ ] Test: Verify unsaved changes markers work correctly
- [ ] Test: Verify multi-plate scenarios don't pollute cache

### Phase 2: Batch Context Collection (CONDITIONAL)
- [ ] **ONLY implement if profiling shows multiple calls with same token**
- [ ] Add `_update_cycle_context_cache` with scope_filter in key
- [ ] Add caching logic to `collect_live_context()`
- [ ] Clear cache on token increment
- [ ] Test: Verify scope filtering correctness (CRITICAL)
- [ ] Test: Verify cache invalidation on plate switch
- [ ] Implement Phase 2.4 (saved snapshot batching) if profiling shows need

### Phase 3: Batch Cross-Window Updates (CONDITIONAL)
- [ ] **ONLY implement if profiling shows excessive signals**
- [ ] Add `_pending_cross_window_changes` and timer
- [ ] Implement batching in `_emit_cross_window_change()`
- [ ] Implement `_emit_batched_cross_window_changes()`
- [ ] Test: Verify signal order is preserved
- [ ] Test: Verify all listeners receive updates

### Phase 4: Verify Flash Detection ✅
- [x] Verified `_check_with_batch_resolution()` exists
- [ ] Verify it's being used correctly
- [ ] Test: Verify flash detection still works

---

## Summary of Changes from Original Plan

| Original Plan | Revised Plan | Reason |
|---------------|--------------|--------|
| Phase 1: Step-based caching | REMOVED | Adds O(n_steps) work - worse than current |
| Phase 2: Context caching | FIXED scope_filter bug | Critical for multi-plate correctness |
| Phase 3: Batch cross-window | CONDITIONAL | Only if profiling shows need |
| Phase 4: Verify batching | ✅ VERIFIED | Confirmed exists |
| No profiling step | **Step 0: PROFILE FIRST** | Measure before optimizing |
| Unclear cache invalidation | **Explicit rules** | All scenarios covered |

**Key Takeaway**: The reviewer was **mostly correct**. The revised plan:
1. Profiles first (no premature optimization)
2. Fixes critical scope_filter bug
3. Removes harmful Phase 1
4. Makes all optimizations conditional on profiling results
5. Adds explicit cache invalidation rules


