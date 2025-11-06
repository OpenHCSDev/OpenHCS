# Changelog: v0.4.2 to HEAD

**Generated:** 2025-11-05  
**Commits:** 31 commits since v0.4.2  
**Commit Range:** v0.4.2..7c2b4233

---

## 🔥 Critical Bug Fixes

### **Fix critical nested enabled field styling bug** (7c2b4233)
**Impact:** HIGH - Affects all forms with nested dataclasses that have enabled fields

Fixed three related issues with enabled field styling in nested dataclass forms:

1. **Signal Pollution Prevention**: Added `_propagating_nested_enabled` flag to prevent nested forms' enabled changes from triggering parent form styling updates
   - When a nested dataclass's `enabled` field was toggled, it incorrectly caused styling changes in parent and sibling forms
   - Now only the specific nested form that changed updates its styling

2. **Intelligent Widget Restoration**: When parent form is re-enabled, now checks each nested form's state:
   - Skips Optional dataclasses with `None` value (keeps dimmed)
   - Skips nested forms with `enabled=False` (keeps dimmed)
   - Fully restores other nested forms including reset buttons
   - Previously all widgets were unconditionally restored, ignoring individual states

3. **Selective Sibling Refresh**: Only refreshes sibling styling when specifically needed for enabled field changes
   - Prevents unnecessary cascade effects

**Files Modified:**
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

**Files Added:**
- `NESTED_ENABLED_STYLING_FIX.md` (detailed fix documentation)
- `test_nested_enabled_styling_fix.py` (test script - all tests pass ✓)

**Bug Symptoms (Now Fixed):**
- ❌ Toggling nested dataclass enabled field caused parent/sibling styling changes
- ❌ Re-enabling parent form didn't properly restore nested widgets
- ❌ Reset buttons in nested forms remained dimmed incorrectly

---

### **Fix code editor parameter preservation bugs** (d9b884ad)
**Impact:** CRITICAL - Affects code editor round-trip functionality

Fixed two bugs preventing parameter preservation during UI → Code → UI round trips:

1. **`enabled` parameter completely lost**
   - **Root Cause**: Registry wrapped functions but didn't override them in their modules
   - **Fix**: Import modules in `_create_virtual_modules()` before overriding functions with `setattr()`
   - Now `enabled` parameter is preserved across code editor round trips ✓

2. **`dtype_conversion` type hint treated as `Any` instead of enum dropdown**
   - **Root Cause**: Decorators set `__signature__` but not `__annotations__`, so `get_type_hints()` didn't find the parameter
   - **Fix**: Fall back to signature annotation when parameter not in `type_hints`
   - Now `dtype_conversion` shows as dropdown instead of text input ✓

**Files Modified:**
- `openhcs/processing/func_registry.py`
- `openhcs/processing/backends/lib_registry/openhcs_registry.py`
- `openhcs/introspection/signature_analyzer.py`

**Files Added:**
- `debug_code_editor_bug.md` (investigation notes)
- Multiple test files for verification

---

## 🎯 Feature Additions

### **Global Component Tracker for ROI/Image Alignment** (bdebd75e)
**Impact:** MEDIUM - Improves cross-module consistency

Implemented global component tracker for consistent ROI/image alignment across all UI windows:
- Ensures ProcessingConfig changes are reflected everywhere
- Prevents stale component display in viewer windows
- Adds central state management for imaging components

**Files Modified:**
- `openhcs/constants/constants.py`
- `openhcs/core/context/processing_context.py`
- Multiple viewer/editor files

---

### **Add Manual Consolidation Button** (a05a69dc)
**Impact:** LOW - UI improvement

Added manual consolidation button to plate viewer window for easier access to consolidation functionality.

---

### **Add 'type' and 'size' Fields to Image Metadata** (4c9add40)
**Impact:** LOW - Metadata enhancement

Added consistency fields to image metadata for better tracking and debugging.

---

## 🐛 Bug Fixes

### **Napari ROI Alignment with Image Stack Indices** (54d618a7)
**Impact:** MEDIUM

Fixed ROI display alignment issues when viewing image stacks in Napari viewer.

---

### **Plate Manager Status Marquee Duplicate Text** (70655496)
**Impact:** LOW - UI polish

Fixed duplicate text display in the plate manager status marquee.

---

### **Experimental Analysis Fixes** (Multiple commits)
**Impact:** MEDIUM - Analysis pipeline reliability

Series of fixes to experimental analysis script:
- **e2b6da15**: Fixed empty results handling and enhanced pipeline migration
- **1b975c23**: Fixed handling of multiple plates in same CSV
- **ae71c822**: Added Opera Phenix well ID conversion
- **e606d6e9**: Handle empty conditions properly
- **b89892b2**: Skip wells not in config during analysis

---

### **Consolidation Workflow Fixes** (Multiple commits)
**Impact:** MEDIUM - Data consolidation reliability

Major improvements to consolidation functionality:
- **e4c9e8aa**: Fixed CSV writer to handle pre-formatted CSV strings
- **6bbc2608**: Made well ID substring matching case-insensitive
- **bceac75d**: Extract well IDs from CSV filenames instead of image files
- **e5c6acd2**: Made consolidation continue on errors with detailed results
- **b6f05798**: Fixed well ID extraction from CSV filenames
- **ea2ee9d7**: Fixed to use global config from config_framework
- **83c21df1**: Fixed to use results_dir field from metadata
- **5bc971ce**: Fixed to use subdirectory keys directly from metadata
- **763ade68**: Fixed to find results dirs from metadata subdirectories
- **1e05ec4e**: Fixed to use orchestrator.pipeline_config pattern
- **59f10ee1**: Fixed to find results directory from compiled contexts
- **e5e6e8d8**: Fixed get_image_files to return files from all subdirectories

---

### **Signature and Backend Fixes** (Multiple commits)
**Impact:** LOW-MEDIUM

- **553209f6**: Fixed materialize_axon_analysis and materialize_skeleton_visualizations signatures
- **2968f4a6**: Fixed CSV path generation in materialize_mtm_match_results
- **dbb707dc**: Fixed materialize_mtm_match_results signature to match multi-backend pattern
- **1462d84b**: Fixed num_workers resolution from GlobalPipelineConfig

---

## ♻️ Refactoring

### **WellFilterConfig Refactor** (b676b6fd)
**Impact:** LOW - Code quality improvement

Refactored WellFilterConfig to apply INCLUDE/EXCLUDE mode automatically for cleaner API.

---

### **OMEROMetadataHandler Enhancement** (57c1b7d1, 42387e67)
**Impact:** LOW

Added `all_subdirs` parameter to `get_image_files()` for toggleable subdirectory traversal behavior.

---

## 📊 Summary Statistics

- **Total Commits**: 31
- **Critical Bugs Fixed**: 2
- **Major Features Added**: 1
- **Bug Fixes**: 20+
- **Refactorings**: 3

### **Files Changed by Category:**

**UI/Forms:**
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` (Critical styling fix)

**Registry/Introspection:**
- `openhcs/processing/func_registry.py`
- `openhcs/processing/backends/lib_registry/openhcs_registry.py`
- `openhcs/introspection/signature_analyzer.py`

**Consolidation:**
- Multiple consolidation workflow files

**Metadata/Context:**
- `openhcs/constants/constants.py`
- `openhcs/core/context/processing_context.py`

**Analysis:**
- Experimental analysis script
- Multiple backend signature files

---

## 🔍 Review Summary

### **Highest Impact Changes:**

1. ✅ **Nested Enabled Field Styling Fix** - Fixes critical UI bug affecting all nested forms
2. ✅ **Code Editor Parameter Preservation** - Restores critical round-trip functionality
3. ✅ **Global Component Tracker** - Improves cross-module consistency

### **Most Active Areas:**

1. **Consolidation Workflow** - 13 commits focused on making consolidation robust
2. **UI Forms/Styling** - 2 commits fixing critical form behavior
3. **Experimental Analysis** - 5 commits improving analysis pipeline reliability

### **Testing:**

- ✅ Nested enabled field styling fix verified with unit tests
- ✅ Code editor parameter preservation verified with test scripts
- ⚠️ Consolidation fixes should be integration tested with real data

### **Recommendations:**

1. **Tag v0.4.3** - Both critical bugs are fixed and tested
2. **Document** - Update main README if consolidation workflow changed significantly
3. **Monitor** - Watch for any regressions in form styling behavior
4. **Test** - Run full integration tests on consolidation workflow

---

## 🎉 Conclusion

This release contains **two critical bug fixes** that significantly improve the user experience:

1. **Form styling now works correctly** for nested dataclasses with enabled fields
2. **Code editor round trips now preserve all parameters** including `enabled` and typed parameters

Along with **20+ other bug fixes** focused on consolidation workflow and experimental analysis reliability.

**Recommendation:** Tag as **v0.4.3** and deploy.
