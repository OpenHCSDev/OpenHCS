# Bug Analysis: Cross-Window Placeholder Consistency

## Problem Statement
The cross-window consistency test is failing because `step_well_filter_config.well_filter` shows `'Pipeline default: 1'` instead of the expected `'Pipeline default: concrete_2'`.

## What The Test Is Actually Doing

**THE TEST IS CORRECT.** This is NOT about live cross-window updates. The test flow is:

1. **Pipeline Config Window**: User opens pipeline config and sets `step_well_filter_config.well_filter = 'concrete_2'`
2. **Save and Close**: Pipeline config is saved to thread-local context and window is closed
3. **Step Editor Opens**: Step editor opens and uses the saved context from the orchestrator
4. **Cross-Window Consistency Check**: Step editor placeholders should reflect the saved pipeline config values

**Expected Behavior**: When step editor opens, it should read the saved context and show:
- `step_well_filter_config.well_filter` → `'Pipeline default: concrete_2'` (the saved concrete value)
- `step_materialization_config.well_filter` → `'Pipeline default: concrete_2'` (inherits from saved `step_well_filter_config`)
- `napari_streaming_config.well_filter` → `'Pipeline default: concrete_2'` (inherits from saved `step_well_filter_config`)

## The Critical Paradox (Cannot Be Ignored)

**✅ Components that inherit FROM StepWellFilterConfig work correctly:**
- `StepMaterializationConfig.well_filter` → `'Pipeline default: concrete_2'` ✅
- `NapariStreamingConfig.well_filter` → `'Pipeline default: concrete_2'` ✅
- `FijiStreamingConfig.well_filter` → `'Pipeline default: concrete_2'` ✅

**❌ StepWellFilterConfig itself fails:**
- `StepWellFilterConfig.well_filter` → `'Pipeline default: 1'` ❌ (should be `'Pipeline default: concrete_2'`)

**This paradox proves the bug:** If child configs can successfully find `step_well_filter_config.well_filter = 'concrete_2'` in the saved context, then `StepWellFilterConfig` itself must also be able to find its own saved value in the same context.

## Debug Evidence

**Working case (StepMaterializationConfig reading saved context):**
```
🔍 LAZY RESOLUTION DEBUG: Resolving StepMaterializationConfig.well_filter
🔍 LAZY RESOLUTION DEBUG: Context has step_well_filter_config.well_filter = 'concrete_2'
🔍 MRO DEBUG: StepMaterializationConfig MRO types: ['StepWellFilterConfig', 'PathPlanningConfig', 'WellFilterConfig']
🔍 MRO DEBUG: Checking StepWellFilterConfig at path 'step_well_filter_config' -> instance: LazyStepWellFilterConfig(well_filter='concrete_2', well_filter_mode=<WellFilterMode.INCLUDE: 'include'>)
🔍 MRO DEBUG: Found step_well_filter_config.well_filter = 'concrete_2' (class: StepWellFilterConfig)
```

**Failing case (StepWellFilterConfig reading same saved context):**
```
🔍 LAZY RESOLUTION DEBUG: Resolving StepWellFilterConfig.well_filter
🔍 USER OVERRIDE DEBUG: Looking for StepWellFilterConfig paths: ['step_well_filter_config']
🔍 USER OVERRIDE DEBUG: Path 'step_well_filter_config' -> instance: StepWellFilterConfig(well_filter=None, well_filter_mode=<WellFilterMode.INCLUDE: 'include'>)
🔍 USER OVERRIDE DEBUG: Found step_well_filter_config.well_filter = 'None'
🔍 CONCRETE OVERRIDE: StepWellFilterConfig.well_filter = 1 (no user-set values found)
```

## Root Cause Analysis

**The Issue**: When the step editor opens and resolves `StepWellFilterConfig.well_filter` placeholder, my USER OVERRIDE logic finds `step_well_filter_config.well_filter = None` in the context instead of the saved value `'concrete_2'`.

**But the paradox proves this is wrong**: Other components successfully find `step_well_filter_config.well_filter = 'concrete_2'` in the exact same context.

**The Real Problem**: My USER OVERRIDE logic in `lazy_placeholder.py` is not correctly navigating to the saved context instance. When resolving `StepWellFilterConfig.well_filter`, it should find the same `LazyStepWellFilterConfig(well_filter='concrete_2', ...)` instance that `StepMaterializationConfig` finds, but instead it's finding a different instance with `well_filter=None`.

## Context Analysis

**What should happen**: When step editor opens, both `StepWellFilterConfig` and `StepMaterializationConfig` should use the same saved context:
```
GlobalPipelineConfig(
    step_well_filter_config=LazyStepWellFilterConfig(well_filter='concrete_2', ...),
    step_materialization_config=LazyStepMaterializationConfig(well_filter=None, ...),
    ...
)
```

**What's actually happening**: 
- `StepMaterializationConfig` finds the correct context instance with `well_filter='concrete_2'`
- `StepWellFilterConfig` finds a different context instance with `well_filter=None`

## The Fix Required

The bug is in my USER OVERRIDE logic in `lazy_placeholder.py`. When resolving `StepWellFilterConfig.well_filter`, it needs to find the same saved context instance that other components successfully find.

The issue is likely in the `FieldPathNavigator.navigate_to_instance()` call or the context being passed to the placeholder resolution.
