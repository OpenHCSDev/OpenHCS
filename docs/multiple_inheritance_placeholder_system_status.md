# Multiple Inheritance Placeholder System - Implementation Status

**Date**: 2025-09-05  
**Status**: TACTICAL IMPLEMENTATION COMPLETE - STRATEGIC REFACTOR NEEDED

## Summary

Multiple inheritance placeholder live updates are now implemented in `parameter_form_manager.py` using Python's natural MRO precedence. The system works but has critical bugs that require a strategic architectural refactor.

## ✅ IMPLEMENTED FEATURES

### 1. MRO-Based Inheritance Precedence
- **Fixed inheritance order**: `StepMaterializationConfig(StepWellFilterConfig, PathPlanningConfig)`
- **Replaced custom logic** with Python's natural `__mro__` precedence detection
- **Field conflict resolution** using highest precedence parent detection
- **Precedence enforcement**: Only highest precedence parent can trigger placeholder updates

### 2. Streamlined Config Architecture
- **StreamingConfig.well_filter = None** enables lazy resolution from `StepWellFilterConfig`
- **Removed redundant overrides** from `NapariStreamingConfig`/`FijiStreamingConfig`
- **Proper inheritance chain**: Concrete streamers inherit None, resolve to parent values

### 3. Dynamic Config Name Resolution
- **Replaced hardcoded mapping** with `_camel_to_snake()` function
- **Coupled with field injection system** for consistency
- **Automatic support** for future config classes

### 4. Working Multiple Inheritance
- **`well_filter` field**: Only `StepWellFilterConfig` can trigger updates (highest precedence)
- **`global_output_folder` field**: Only `PathPlanningConfig` can trigger updates (only definer)
- **Streaming configs**: Now inherit from `StepWellFilterConfig` correctly

## ❌ CRITICAL BUGS REMAINING

### 1. Placeholder Updates Destroy User Values
**Problem**: When placeholders update, they incorrectly remove concrete user-set values and replace with None.

**Impact**: Users lose their explicit configuration choices when parent contexts change.

**Root Cause**: Placeholder update logic doesn't distinguish between user-set values and inherited placeholders.

### 2. Reset Shows Wrong Inheritance Context
**Problem**: Reset functionality shows saved form values instead of current inheritance-resolved placeholders.

**Expected**: Reset should remove user value but show placeholder resolved against current form state.

**Current**: Reset shows placeholder resolved against saved/cached form state.

### 3. Single Inheritance Field Override Issues
**Problem**: `StepWellFilterConfig` incorrectly inherits from `WellFilterConfig` in overridden fields during single inheritance.

**Impact**: Field precedence rules aren't consistently applied across single vs multiple inheritance scenarios.

**Scope**: This affects more than just multiple inheritance - single inheritance has the same architectural issues.

## 🏗️ ARCHITECTURAL ASSESSMENT

### Current Implementation: Tactical
- **Complex inheritance detection** in `_field_inherits_from_dataclass()`
- **MRO traversal logic** mixed with field conflict resolution
- **Placeholder update logic** scattered across multiple methods
- **Edge case handling** through increasingly complex conditionals

### Required: Strategic Refactor
The current implementation is a **tactical solution** that works but is not maintainable. A strategic architectural redesign is needed to:

1. **Separate concerns**: Inheritance detection vs. placeholder resolution vs. user value preservation
2. **Centralize logic**: Single source of truth for inheritance rules
3. **Simplify edge cases**: Elegant handling of field conflicts and precedence
4. **Unify single/multiple inheritance**: Consistent behavior across all inheritance scenarios

## 📋 NEXT STEPS

### Phase 1: Bug Fixes (Immediate)
1. **Fix placeholder update value preservation**: Ensure user-set values are never overwritten by placeholder updates
2. **Fix reset inheritance context**: Reset should show placeholders resolved against current form state
3. **Fix single inheritance field overrides**: Apply consistent precedence rules

### Phase 2: Strategic Refactor (Architecture)
1. **Design inheritance resolution service**: Clean separation of concerns
2. **Implement placeholder state management**: Clear distinction between user values and inherited placeholders  
3. **Unify inheritance logic**: Single system for both single and multiple inheritance
4. **Create comprehensive test suite**: Ensure all edge cases are covered

## 🔧 TECHNICAL DETAILS

### Key Files Modified
- `openhcs/core/config.py`: Fixed inheritance order, streamlined streaming configs
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`: MRO-based inheritance logic
- Multiple inheritance detection in `_field_inherits_from_dataclass()`
- Placeholder update logic in `refresh_placeholder_text_with_context()`

### Architecture Changes
- **Inheritance Order**: `StepMaterializationConfig(StepWellFilterConfig, PathPlanningConfig)`
- **MRO Precedence**: Uses `target_base_class.__mro__` for precedence detection
- **Field Conflict Resolution**: Only highest precedence parent can trigger updates
- **Dynamic Naming**: `_camel_to_snake()` replaces hardcoded config name mappings

### Current Logic Flow
1. **Change detected** in parent config
2. **MRO traversal** finds highest precedence field definer
3. **Inheritance check** allows/blocks update based on precedence
4. **Placeholder update** (❌ currently overwrites user values)

## 🎯 SUCCESS CRITERIA

### Bug Fixes Complete When:
- [ ] User-set values are never overwritten by placeholder updates
- [ ] Reset shows inheritance-resolved placeholders based on current form state
- [ ] Single inheritance respects field override precedence consistently
- [ ] All inheritance scenarios work predictably

### Strategic Refactor Complete When:
- [ ] Inheritance logic is centralized and maintainable
- [ ] Clear separation between user values and inherited placeholders
- [ ] Unified behavior across single and multiple inheritance
- [ ] Comprehensive test coverage for all inheritance scenarios
- [ ] Code is elegant and follows OpenHCS architectural principles

---

**Note**: The multiple inheritance system now works functionally, but the implementation is tactical and needs strategic architectural improvement to be maintainable and handle all edge cases correctly.
