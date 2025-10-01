# Documentation Cleanup Progress

**Date**: 2025-01-01
**Status**: IN PROGRESS
**Goal**: Clean up all configuration system documentation before merging lazy_refactor → main

## Completed

### ✅ New Documentation Created

1. **`docs/source/architecture/live_placeholder_system.rst`** (COMPLETE)
   - Comprehensive documentation of live placeholder updates
   - Explains `_initial_load_complete` flag
   - Documents parent overlay injection
   - Describes raw value extraction
   - 300 lines of accurate, detailed documentation

2. **`docs/source/architecture/DOCUMENTATION_CLEANUP_NEEDED.md`** (COMPLETE)
   - Audit document identifying all outdated content
   - Lists files requiring updates
   - Provides verification checklist
   - Outlines implementation plan

### ✅ Documentation Rewritten

1. **`docs/source/architecture/context_management_system.rst`** (IN PROGRESS - 168/300 lines)
   - ✅ Removed all frame injection references
   - ✅ Removed all stack introspection references
   - ✅ Added contextvars-based system documentation
   - ✅ Added config extraction and merging documentation
   - ⏳ NEEDS: Integration with dual-axis resolution section
   - ⏳ NEEDS: Thread-local GlobalPipelineConfig section
   - ⏳ NEEDS: Context lifecycle section
   - ⏳ NEEDS: Debugging section

## In Progress

### ⏳ Files Being Updated

1. **`docs/source/architecture/context_management_system.rst`**
   - Current: 168 lines (56% complete)
   - Remaining sections to add:
     - Integration with Dual-Axis Resolution
     - Thread-Local GlobalPipelineConfig
     - Context Lifecycle
     - Debugging Context Resolution

## Pending

### 📋 High Priority Files (Inaccurate Technical Details)

2. **`docs/source/architecture/configuration_resolution.rst`**
   - Lines 147-174: Describes frame injection for context discovery
   - References obsolete `ContextInjector` and `ContextDiscovery`
   - Mixes thread-local and frame injection concepts incorrectly
   - **Action**: Update to clarify current hybrid approach (thread-local + contextvars)

3. **`docs/source/architecture/configuration_system_architecture.rst`**
   - Lines 64-106: Describes "Enhanced Frame Injection (2024 Update)" that doesn't exist
   - References stack introspection for context discovery
   - Troubleshooting section mentions `__*_context__` naming pattern (obsolete)
   - **Action**: Update context discovery section to describe contextvars

### 📋 Medium Priority Files (Partially Accurate)

4. **`docs/source/architecture/lazy_class_system.rst`**
   - Generally accurate but doesn't mention live placeholder updates
   - Doesn't explain raw value extraction with `object.__getattribute__()`
   - Missing information about `to_base_config()` preservation of None values
   - **Action**: Add sections on live placeholder integration and raw value extraction

5. **`docs/source/architecture/placeholder_resolution_system.rst`**
   - Describes placeholder resolution but doesn't mention live updates
   - Doesn't explain parent overlay injection
   - Missing information about `_initial_load_complete` flag
   - **Action**: Add sections on live placeholder updates and parent overlay injection

### 📋 Low Priority Files (Mostly Accurate, Needs Minor Updates)

6. **`docs/source/concepts/lazy_configuration_mental_model.rst`**
   - High-level mental model is still accurate
   - Could mention live placeholder updates as a benefit
   - Examples could be updated to show real-time feedback
   - **Action**: Minor additions about live updates

### 📋 New Documentation Needed

7. **`docs/source/architecture/contextvars_context_system.rst`** (NEW FILE NEEDED)
   - **Purpose**: Explain how contextvars replaced frame injection
   - **Key Topics**:
     - `config_context()` context manager
     - Context stack management
     - Integration with dual-axis resolver
     - Thread-local GlobalPipelineConfig as base

8. **`docs/source/architecture/raw_value_extraction.rst`** (NEW FILE NEEDED)
   - **Purpose**: Explain why and how raw value extraction works
   - **Key Topics**:
     - `object.__getattribute__()` vs normal attribute access
     - Lazy resolution pollution problem
     - `to_base_config()` implementation
     - `get_user_modified_values()` raw extraction

### 📋 Files to Remove

9. **`docs/configuration_documentation_update_summary.md`**
   - **Reason**: Outdated summary from previous documentation update, no longer relevant
   - **Action**: Delete

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

## Next Steps

### Option 1: Complete Documentation Cleanup First
Continue updating all documentation files before moving to code reorganization.

**Pros**:
- Documentation will be 100% accurate for PR
- Easier to review documentation changes separately
- Clear separation of concerns

**Cons**:
- More work before seeing code reorganization
- Documentation and code changes in separate commits

**Estimated Time**: 2-3 hours to complete all documentation updates

### Option 2: Code Reorganization First, Documentation Later
Move configuration framework to `openhcs/config_framework/` module, then update documentation.

**Pros**:
- Code reorganization might reveal documentation needs
- Can update documentation to reference new module structure
- Faster path to reusable framework

**Cons**:
- Documentation will be partially outdated during reorganization
- Might need to update documentation twice (once for accuracy, once for new structure)

**Estimated Time**: 1-2 hours for code reorganization, then 2-3 hours for documentation

### Option 3: Parallel Approach
Update high-priority documentation files while planning code reorganization.

**Pros**:
- Makes progress on both fronts
- Can identify dependencies between tasks
- Flexible approach

**Cons**:
- More context switching
- Harder to track progress

## Recommendation

I recommend **Option 2: Code Reorganization First** because:

1. **Structural clarity**: Moving code to `openhcs/config_framework/` will make it clear what's part of the framework vs OpenHCS-specific
2. **Documentation accuracy**: We can update documentation to reference the new module structure directly
3. **Reusability goal**: The primary goal is to make the framework reusable, so code reorganization is the critical path
4. **Single update**: Documentation only needs to be updated once, with correct module paths

After code reorganization, we can:
1. Update all documentation to reference new module paths
2. Add any missing documentation revealed by reorganization
3. Run verification checklist
4. Commit everything together for PR

## Current Task Status

- [/] Documentation Cleanup - Phase 1: Remove Inaccurate Content (IN PROGRESS)
  - ✅ `context_management_system.rst` - Partially rewritten (168/300 lines)
  - ⏳ `configuration_resolution.rst` - Not started
  - ⏳ `configuration_system_architecture.rst` - Not started

- [ ] Documentation Cleanup - Phase 2: Add Missing Content (NOT STARTED)
  - ⏳ Create `contextvars_context_system.rst`
  - ⏳ Create `raw_value_extraction.rst`
  - ⏳ Update `lazy_class_system.rst`

- [ ] Documentation Cleanup - Phase 3: Polish and Verify (NOT STARTED)
  - ⏳ Update `lazy_configuration_mental_model.rst`
  - ⏳ Update `placeholder_resolution_system.rst`
  - ⏳ Run verification checklist
  - ⏳ Remove obsolete files

- [ ] Code Reorganization - Create Configuration Framework Module (NOT STARTED)
  - ⏳ Create `openhcs/config_framework/` module
  - ⏳ Move core files to framework
  - ⏳ Update imports throughout codebase
  - ⏳ Add framework README and documentation

