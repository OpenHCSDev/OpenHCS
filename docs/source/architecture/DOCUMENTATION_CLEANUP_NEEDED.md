# Configuration System Documentation Cleanup

**Status**: Documentation audit for lazy_refactor → main merge
**Date**: 2025-01-01
**Context**: First time in OpenHCS history that placeholders are completely synchronized with lazy decorator system across all 3 context levels

## Current State

The configuration system has evolved significantly, but documentation still references outdated concepts:

### ❌ Outdated Concepts (Remove/Update)
- **Frame injection** - Replaced by Python's contextvars
- **Stack introspection** - Replaced by contextvars context stack
- **Field path detection** - Simplified/removed in favor of direct field access
- **Composition detection** - Removed, replaced by simpler patterns
- **Thread-local storage** - Partially replaced by contextvars (still used for GlobalPipelineConfig)

### ✅ Current Implementation (Document Accurately)
- **contextvars-based context management** - `config_context()` using Python's contextvars
- **Dual-axis resolver** - X-axis (context hierarchy) + Y-axis (sibling inheritance)
- **Live placeholder updates** - Real-time placeholder refresh on field changes
- **Raw value extraction** - `object.__getattribute__()` to preserve None values
- **Deferred live updates** - `_initial_load_complete` flag to prevent pollution

## Files Requiring Updates

### High Priority (Inaccurate Technical Details)

#### 1. `docs/source/architecture/context_management_system.rst`
**Issues**:
- Lines 1-340: Entire file describes frame injection system that no longer exists
- References `ContextInjector` and `ContextDiscovery` classes that are obsolete
- Describes stack introspection that has been replaced by contextvars

**Action**: Complete rewrite to describe contextvars-based system

**Key Points to Cover**:
- `config_context()` context manager using Python's contextvars
- Context stack maintained by contextvars, not frame injection
- Thread-local GlobalPipelineConfig still used as base context
- No more frame manipulation or stack introspection

#### 2. `docs/source/architecture/configuration_resolution.rst`
**Issues**:
- Lines 147-174: Describes frame injection for context discovery
- References obsolete `ContextInjector` and `ContextDiscovery`
- Mixes thread-local and frame injection concepts incorrectly

**Action**: Update to clarify current hybrid approach

**Key Points to Cover**:
- Thread-local GlobalPipelineConfig (still used)
- contextvars for PipelineConfig and Step contexts
- `config_context()` as the primary API
- No frame injection or stack introspection

#### 3. `docs/source/architecture/configuration_system_architecture.rst`
**Issues**:
- Lines 64-106: Describes "Enhanced Frame Injection (2024 Update)" that doesn't exist
- References stack introspection for context discovery
- Troubleshooting section mentions `__*_context__` naming pattern (obsolete)

**Action**: Update context discovery section

**Key Points to Cover**:
- contextvars-based context discovery
- No special variable naming patterns
- Context stack managed by Python's contextvars module

### Medium Priority (Partially Accurate)

#### 4. `docs/source/architecture/lazy_class_system.rst`
**Issues**:
- Generally accurate but doesn't mention live placeholder updates
- Doesn't explain raw value extraction with `object.__getattribute__()`
- Missing information about `to_base_config()` preservation of None values

**Action**: Add sections on:
- Live placeholder system integration
- Raw value extraction for context merging
- `to_base_config()` implementation details

#### 5. `docs/source/architecture/placeholder_resolution_system.rst`
**Issues**:
- Describes placeholder resolution but doesn't mention live updates
- Doesn't explain parent overlay injection
- Missing information about `_initial_load_complete` flag

**Action**: Add sections on:
- Live placeholder updates
- Parent overlay injection mechanism
- Deferred activation to prevent pollution

### Low Priority (Mostly Accurate, Needs Minor Updates)

#### 6. `docs/source/concepts/lazy_configuration_mental_model.rst`
**Issues**:
- High-level mental model is still accurate
- Could mention live placeholder updates as a benefit
- Examples could be updated to show real-time feedback

**Action**: Minor additions about live updates

### Files to Remove

#### 1. `docs/configuration_documentation_update_summary.md`
**Reason**: Outdated summary from previous documentation update, no longer relevant

#### 2. `docs/source/architecture/field_path_detection.rst` (if it exists)
**Reason**: Field path detection has been simplified/removed

#### 3. `docs/source/architecture/composition_detection_system.rst` (if it exists)
**Reason**: Composition detection has been removed

## New Documentation Needed

### 1. ✅ `docs/source/architecture/live_placeholder_system.rst` (CREATED)
**Status**: Complete
**Content**: Comprehensive documentation of live placeholder updates

### 2. `docs/source/architecture/contextvars_context_system.rst` (NEEDED)
**Purpose**: Explain how contextvars replaced frame injection
**Key Topics**:
- `config_context()` context manager
- Context stack management
- Integration with dual-axis resolver
- Thread-local GlobalPipelineConfig as base

### 3. `docs/source/architecture/raw_value_extraction.rst` (NEEDED)
**Purpose**: Explain why and how raw value extraction works
**Key Topics**:
- `object.__getattribute__()` vs normal attribute access
- Lazy resolution pollution problem
- `to_base_config()` implementation
- `get_user_modified_values()` raw extraction

## Verification Checklist

Before merging lazy_refactor → main, verify:

- [ ] No documentation mentions "frame injection"
- [ ] No documentation mentions "stack introspection"
- [ ] No documentation mentions `ContextInjector` or `ContextDiscovery`
- [ ] No documentation mentions `__*_context__` variable naming pattern
- [ ] All documentation accurately describes contextvars-based system
- [ ] Live placeholder system is documented
- [ ] Raw value extraction is explained
- [ ] Three-level context hierarchy is clearly described (Global → Pipeline → Step)
- [ ] Dual-axis inheritance (X-axis context, Y-axis sibling) is explained
- [ ] `_initial_load_complete` flag and deferred activation is documented

## Implementation Plan

### Phase 1: Remove Inaccurate Content
1. Rewrite `context_management_system.rst` to describe contextvars
2. Update `configuration_resolution.rst` to remove frame injection references
3. Update `configuration_system_architecture.rst` context discovery section

### Phase 2: Add Missing Content
1. Create `contextvars_context_system.rst`
2. Create `raw_value_extraction.rst`
3. Update `lazy_class_system.rst` with live placeholder integration

### Phase 3: Polish and Verify
1. Update `lazy_configuration_mental_model.rst` with live update benefits
2. Update `placeholder_resolution_system.rst` with live update mechanism
3. Run verification checklist
4. Remove obsolete files

## Notes

**Critical**: The documentation must accurately reflect that:
1. **contextvars** is the primary context management mechanism (not frame injection)
2. **Thread-local** is still used for GlobalPipelineConfig (hybrid approach)
3. **Live placeholders** are a new feature that required careful timing (`_initial_load_complete`)
4. **Raw value extraction** is critical to prevent lazy resolution pollution
5. **Three context levels** (Global → Pipeline → Step) are the foundation
6. **Dual-axis inheritance** (X-axis context + Y-axis sibling) is the resolution model

**Achievement**: This is the first time in OpenHCS history that placeholders are completely synchronized with the lazy decorator system across all three context levels. This deserves prominent documentation.

