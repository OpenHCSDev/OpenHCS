# Changelog: v0.4.4 to HEAD

**Period**: December 2024 - January 2025  
**Commits**: 17  
**Files Changed**: 50 files (+4,765 insertions, -907 deletions)

---

## 🎯 Major Features

### 1. Code Editor System Refactoring
**Commits**: `3394f6d5`, `8808cb23`

Complete overhaul of the code editor infrastructure with shared utilities and enhanced context management.

**New Infrastructure**:
- **`CodeEditorFormUpdater`** - Shared utility class eliminating ~200 lines of duplicate code across editors
  - Centralized lazy constructor patching for `exec()` operations
  - Consolidated explicit field extraction and form update logic
  - Supports both dataclass and regular object instances
  - Standard integration pattern for all code editors

**GlobalPipelineConfig Context Management**:
- Thread-local context synchronization with live form edits
- Per-field context sync via `_on_global_config_field_changed()`
- Cancel restoration: original config snapshot restored on dialog rejection
- Optimized bulk updates: suppress per-field sync during code editor saves

**Enhanced Code Generation**:
- Nested dataclass placeholder expansion in non-clean mode
- Shows full nested structure even when fields are `None`
- Better visibility of configuration hierarchy

**Performance Optimization**:
- QTimer-based debouncing for function editor synchronization
- Batches rapid parameter changes into single sync operation
- **80-90% reduction in UI lag** during rapid editing
- Reduced log verbosity for routine operations

**Documentation**:
- Comprehensive user guide updates (`code_ui_editing.rst`)
- Architecture documentation (`code_ui_interconversion.rst`, `configuration_framework.rst`)
- Development patterns guide (`ui-patterns.rst`)

---

### 2. Global Event Bus for Cross-Window Synchronization
**Commits**: `6f359544`, `e5074bc1`, `1ea360ce`

Centralized event dispatcher replacing N×M manual signal connections with N connections to single event bus.

**Architecture**:
- `GlobalEventBus` in `ServiceAdapter` for `pipeline_changed`, `config_changed`, `step_changed` events
- `BaseFormDialog` auto-registration: all config windows automatically register/unregister
- Broadcasting helpers: `_broadcast_pipeline_changed()`, `_broadcast_config_changed()`

**Benefits**:
- **Before**: N windows × M windows = N×M manual connections
- **After**: N windows × 1 event bus = N connections
- Eliminates scattered manual connections between window pairs
- One emit reaches ALL windows simultaneously

**Safety**:
- `_is_manager_valid()` checks prevent crashes during widget lifecycle
- Skip managers during construction (widgets not yet created)
- Skip managers after deletion (widgets already destroyed)

---

### 3. Step Editor Code Button with Bidirectional Sync
**Commits**: `dbab467f`, `5c7293cb`

Added "Code" button to step parameter editor enabling complete `FunctionStep` editing (params + func) as Python code.

**Features**:
- Generates complete step code including function pattern
- Reads live `func` from parent dual editor's function list editor
- Saves update function list editor with new func pattern
- Follows same pattern as config window code editor
- Integrated with cross-window live context system

---

### 4. Cross-Window Live Context for Lazy Dataclass Inheritance
**Commit**: `6acfb17b`

**CRITICAL FIX**: Nested managers now properly collect live context from other open windows.

**Root Cause**:
- Nested managers (e.g., `well_filter` inside Step editor) were calling `_refresh_with_live_context()` on themselves
- But `_refresh_with_live_context()` only collects live context if `_parent_manager is None` (root managers)
- Result: Placeholders showed saved values instead of live values from open windows

**Solution**:
- Nested managers now find root manager and trigger refresh on it
- Root manager collects live context and passes to all nested managers
- Reset operations show live inherited values and trigger cross-window updates
- Added `emit_signal` parameter to prevent infinite ping-pong loops

**Impact**:
- New windows immediately show live unsaved values from already-open windows
- Reset operations show live inherited values
- Optional dataclass enabled styling updates correctly after reset
- No more infinite cross-window refresh loops

---

### 5. Code Editor Nested Dataclass Updates
**Commits**: `9131af5e`, `65d5e6b3`

Fixed bug where changing `None` to concrete value in code editor didn't update form.

**Solution**:
- Created shared `CodeEditorFormUpdater` utility for parsing and updating forms
- Only updates fields explicitly set in code, preserving `None` for unspecified fields
- Recursive nested dataclass update logic
- `_block_cross_window_updates` optimization prevents expensive refreshes during bulk updates

---

## 🐛 Bug Fixes

### Code Editor Autocomplete Crashes
**Commit**: `9721241a`

- Disabled autocomplete entirely to prevent Qt event loop crashes from widget deletion
- Changed code editor from `.exec()` to `.show()` to prevent focus stealing
- Made config window tree panel collapsible (minimum width 0)
- Added double-click on splitter handle to toggle tree visibility

### ZMQ Completion Poller Cleanup
**Commit**: `65d5e6b3`

- Fixed ZMQ completion poller to stop gracefully when client disconnects
- Prevents `'NoneType' get_status` errors

### Step Editor Tree Minimum Width
**Commit**: `b3c6a46b`

- Removed hardcoded `minimum_width` override in step editor tree
- Use default `minimum_width=0` from `ConfigHierarchyTreeHelper`
- Ensures single source of truth for tree minimum width

---

## 🔧 Refactoring & Code Quality

### Shared Collapsible Splitter Helper
**Commit**: `b6b577e4`

- Created `CollapsibleSplitterHelper` for shared double-click toggle logic
- Applied to both `ConfigWindow` and `StepParameterEditor`
- Double-click splitter handle to collapse/expand tree panel
- Remembers last size when collapsed and restores on expand

### Config Hierarchy Tree Helper
**New File**: `openhcs/pyqt_gui/widgets/shared/config_hierarchy_tree.py`

- Centralized tree widget creation and configuration
- Shared styling and behavior across config windows

---

## 📊 CI/CD Improvements

### Combined Coverage from All Integration Test Jobs
**Commit**: `b811f68e`

**Problem**:
- `coverage-pages.yml` ran its own isolated test suite
- Coverage % only reflected that single job, not the full test matrix
- Wasted CI time running duplicate tests

**Solution**:
- All 29 integration test jobs now upload `.coverage` artifacts
- `coverage-pages.yml` downloads and combines all artifacts using `coverage combine`
- Final report shows combined coverage from:
  - Python boundary tests (3.11, 3.13) × 3 OSes = 6 jobs
  - Backend/microscope matrix (disk, zarr × ImageXpress, OperaPhenix) × 3 OSes = 12 jobs
  - OMERO tests (Linux, Python 3.11-3.12) = 2 jobs
  - PyPI installation tests = 6 jobs
  - Wheel integration test = 1 job
  - Code quality checks = 1 job

**Impact**:
- Coverage % now accurately reflects total test coverage across all platforms/configs
- No duplicate test execution
- Single source of truth for project coverage metrics

---

## 📝 Documentation

### README Tone Adjustments
**Commits**: `be4b8d86`, `fbcf39cc`

- Softened opening description from "novel architectural patterns" to "architecture that emphasizes early error detection"
- Changed section title from "What Makes OpenHCS Different" to "Key Features"
- Removed comparison table (inherently confrontational)
- Simplified impact statements and feature descriptions
- More modest presentation while preserving technical substance

### Performance Optimization Documentation
**Commit**: `9f711e03`

- Documented parameter form performance optimizations
- Added metrics and implementation details

---

## 🧪 Test Files Added

Multiple test files added for debugging and verification:
- `test_check_enabled.py`
- `test_check_sys_modules.py`
- `test_code_editor_bug_fixed.py`
- `test_create_virtual_modules_debug.py`
- `test_disabled_function_special_outputs.py`
- `test_enabled_simple.py`
- `test_import_after_override.py`
- `test_metadata_module_name.py`
- `test_registry_modules.py`
- `test_sys_modules_check.py`
- `test_sys_modules_check2.py`
- `test_sys_modules_directly.py`
- `test_virtual_modules.py`
- `test_wrapped_func_details.py`

**Removed**:
- `test_nested_enabled_styling_fix.py` (replaced by better implementation)

---

## 📄 New Documentation Files

Context engine evaluation and setup documentation:
- `CONTEXT_ENGINE_QUICK_REFERENCE.md`
- `CONTEXT_ENGINE_SETUP.md`
- `CONTEXT_ENGINE_STATUS.txt`
- `CONTEXT_ENGINE_TEST_RESULTS.md`
- `CONTEXT_ENGINE_VS_AUGMENT_COMPARISON.md`
- `INPUT_CONVERSION_SOLUTIONS.md`
- `debug_code_editor_bug.md`

---

## 🔑 Key Technical Improvements

### Cross-Window Synchronization
- **Live inheritance preview**: Multiple windows open simultaneously showing inherited values
- **Real-time updates**: Changes in one window instantly update placeholders in all other windows
- **Hierarchical context**: Global → Pipeline → Step with proper inheritance chain
- **None vs concrete distinction**: Semantic difference between "not set" and "explicitly set to default"

### Code/GUI Bidirectionality
- **True round-trip editing**: GUI → code → GUI → code with full fidelity
- **Explicit field extraction**: Parse code to identify which fields were explicitly set
- **Lazy constructor patching**: Ensure `exec()`-created instances preserve `None` vs concrete values
- **Clean mode toggle**: Generate code with or without default values

### Performance
- **Debouncing**: QTimer-based batching for rapid parameter changes (60ms delay)
- **Async widget creation**: Progressive widget instantiation for large forms
- **Placeholder caching**: Track only parameters that resolve to `None`
- **Signature-based skipping**: Skip placeholder updates when values haven't changed

---

## 📈 Statistics

- **17 commits** since v0.4.4
- **50 files changed**
- **+4,765 insertions**
- **-907 deletions**
- **Net: +3,858 lines**

### Major File Changes
- `parameter_form_manager.py`: Extensive refactoring for cross-window context
- `config_window.py`: GlobalPipelineConfig context management
- `dual_editor_window.py`: Event bus integration and debouncing
- `step_parameter_editor.py`: Code button and live context integration
- `code_editor_form_updater.py`: **New shared utility** (258 lines)
- `collapsible_splitter_helper.py`: **New shared helper** (92 lines)
- `config_hierarchy_tree.py`: **New shared helper** (219 lines)

---

## 🎓 Architectural Patterns Established

1. **Centralized Event Bus**: Single source of truth for cross-window updates
2. **Shared Utilities**: `CodeEditorFormUpdater` eliminates code duplication
3. **Live Context Collection**: Root managers collect context from all open windows
4. **Debounced Updates**: Batch rapid changes to prevent UI lag
5. **Lazy Constructor Patching**: Preserve semantic distinction between `None` and defaults
6. **Auto-Registration**: Windows automatically register/unregister with event bus

---

## 🚀 Next Steps

This release establishes the foundation for:
- Universal code editing across all configuration types
- Seamless cross-window synchronization
- Live inheritance preview for all hierarchical configs
- Consistent UI patterns across all editors

The infrastructure is now in place for adding code editing capabilities to any new configuration types with minimal effort.

