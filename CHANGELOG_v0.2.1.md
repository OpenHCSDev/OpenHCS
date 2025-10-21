# Changelog for v0.2.1

## Release Date
2025-10-21

## Overview
Major architectural refactoring to eliminate framework coupling and create reusable introspection utilities. This release introduces two new framework-agnostic packages (`openhcs/introspection/` and `openhcs/ui/shared/`) and completely separates PyQt GUI from Textual TUI dependencies.

## Breaking Changes

### Dependency Changes
- **Removed `plotext` from `[gui]` extra dependencies**
  - PyQt GUI now uses `pyqtgraph` for system monitor visualization
  - `plotext` is now only required for Textual TUI (deprecated)
  - Users installing with `pip install openhcs[gui]` will no longer get `plotext`
  - **Migration**: No action needed for PyQt GUI users. Textual TUI users should install plotext separately if needed.

- **Moved `psutil` to core dependencies**
  - `psutil>=7.0.0` is now a core dependency (previously gui-only)
  - Required by `ui/shared/system_monitor_core.py` which is imported by `config_framework`
  - **Migration**: No action needed - psutil will be installed automatically with openhcs

### Import Path Changes
- **Moved `signature_analyzer.py` from `openhcs/ui/shared/` to `openhcs/introspection/`**
  - Old: `from openhcs.ui.shared.signature_analyzer import SignatureAnalyzer`
  - New: `from openhcs.introspection.signature_analyzer import SignatureAnalyzer`
  - **Migration**: Update import statements in external code that directly imports from `openhcs.ui.shared`

- **Moved `unified_parameter_analyzer.py` from `openhcs/ui/shared/` to `openhcs/introspection/`**
  - Old: `from openhcs.ui.shared.unified_parameter_analyzer import UnifiedParameterAnalyzer`
  - New: `from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer`
  - **Migration**: Update import statements in external code

## New Features

### New Package: `openhcs/introspection/`
Framework-agnostic Python reflection and introspection utilities for analyzing functions, methods, and dataclasses.

**Components:**
- `SignatureAnalyzer` - Extract parameter info from functions/dataclasses with docstring parsing
- `UnifiedParameterAnalyzer` - Unified interface for all parameter sources
- `ParameterInfo` - Named tuple for parameter information
- `DocstringInfo` - Named tuple for docstring information
- `DocstringExtractor` - Extract structured information from docstrings

**Key Features:**
- Pure Python reflection with minimal dependencies
- Lazy-loads OpenHCS-specific modules to avoid circular imports
- Can be used by any part of OpenHCS or extracted for other projects
- Supports type hint resolution with forward references
- AST-based and regex-based docstring parsing

**Usage:**
```python
from openhcs.introspection import SignatureAnalyzer, UnifiedParameterAnalyzer

# Analyze function signature
param_info = SignatureAnalyzer.analyze(my_function)

# Unified analysis for any callable or dataclass
unified_info = UnifiedParameterAnalyzer.analyze(my_object)
```

### New Package: `openhcs/ui/shared/`
Framework-agnostic UI utilities and services that can be used across different UI frameworks (PyQt, Textual, etc.).

**Components:**
- `PatternDataManager` - Pure data operations for function patterns (List↔Dict conversions, cloning, validation)
- `PatternFileService` - Async-safe file I/O for .func files using dill/pickle
- `SystemMonitorCore` - Pure metrics collection (CPU, RAM, GPU, VRAM) using psutil/GPUtil

**Key Features:**
- 100% framework-agnostic (no PyQt or Textual dependencies)
- Eliminates code duplication between PyQt and Textual
- Async-safe file operations with proper error handling
- System monitoring without visualization dependencies

**Usage:**
```python
from openhcs.ui.shared import PatternDataManager, PatternFileService, SystemMonitorCore

# Pattern data operations
manager = PatternDataManager()
cloned = manager.clone_pattern(my_pattern)

# File I/O
service = PatternFileService()
pattern = await service.load_pattern_from_file(path)

# System monitoring
monitor = SystemMonitorCore(history_length=60)
monitor.update_metrics()
metrics = monitor.get_metrics_dict()
```

## Improvements

### Architecture

#### Complete PyQt/Textual Separation
- **PyQt GUI now has ZERO imports from `textual_tui/` package**
- PyQt GUI can function completely independently of Textual TUI
- Textual TUI can be removed without breaking PyQt GUI
- Both frameworks share common utilities via `ui/shared/` and `introspection/`

#### Circular Import Resolution
- **Before**: `ui/shared/__init__.py` → `signature_analyzer` → `config_framework` → `cache_warming` → `signature_analyzer` (CIRCULAR!)
- **After**: `introspection/signature_analyzer` lazy-loads `config_framework` only when needed (NO CIRCULAR!)
- Added `_get_openhcs_modules()` helper function for lazy module loading
- Prevents import-time circular dependencies while maintaining functionality

#### Dependency Isolation
- **plotext dependency isolated to `textual_tui/services/system_monitor.py` only**
- PyQt GUI uses `pyqtgraph` for system monitor visualization
- No more crashes when plotext is not installed for PyQt GUI users

#### Code Duplication Elimination
- **Before**: PatternDataManager, SystemMonitor logic duplicated or tightly coupled to Textual
- **After**: Core logic in `ui/shared/`, framework-specific extensions in respective packages
- Textual TUI services now extend core classes and only add framework-specific features

### Refactored Services

#### `textual_tui/services/pattern_file_service.py`
- **Reduced from 235 lines to 66 lines** (72% reduction)
- Now extends `PatternFileServiceCore` from `ui/shared/`
- Only adds TUI-specific external editor integration (prompt_toolkit)
- Core file I/O operations inherited from framework-agnostic base

#### `textual_tui/services/system_monitor.py`
- **Reduced from 127 lines to 27 lines** (79% reduction)
- Now extends `SystemMonitorCore` from `ui/shared/`
- Only adds plotext visualization (TUI-specific)
- Core metrics collection inherited from framework-agnostic base

### Updated Import Paths (27 files)

**Config Framework & Processing (2 files):**
- `openhcs/config_framework/cache_warming.py`
- `openhcs/processing/backends/lib_registry/unified_registry.py`

**PyQt GUI (11 files):**
- `openhcs/pyqt_gui/services/async_service_bridge.py`
- `openhcs/pyqt_gui/widgets/enhanced_path_widget.py`
- `openhcs/pyqt_gui/widgets/function_list_editor.py`
- `openhcs/pyqt_gui/widgets/function_pane.py`
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`
- `openhcs/pyqt_gui/widgets/step_parameter_editor.py`
- `openhcs/pyqt_gui/widgets/system_monitor.py`
- `openhcs/pyqt_gui/windows/dual_editor_window.py`
- `openhcs/pyqt_gui/windows/help_windows.py`

**Textual TUI (12 files):**
- `openhcs/textual_tui/widgets/config_form.py`
- `openhcs/textual_tui/widgets/function_list_editor.py`
- `openhcs/textual_tui/widgets/function_pane.py`
- `openhcs/textual_tui/widgets/plate_manager.py`
- `openhcs/textual_tui/widgets/shared/__init__.py`
- `openhcs/textual_tui/widgets/step_parameter_editor.py`
- `openhcs/textual_tui/windows/config_window.py`
- `openhcs/textual_tui/windows/dual_editor_window.py`
- `openhcs/textual_tui/windows/help_windows.py`
- `openhcs/textual_tui/windows/multi_orchestrator_config_window.py`

**UI Shared (2 files):**
- `openhcs/ui/shared/parameter_form_service.py`
- `openhcs/ui/shared/__init__.py` (new)

## Dependency Graph (After Refactoring)

```
openhcs/introspection/  (pure Python + lazy OpenHCS imports)
    ↑
    ├── config_framework/  (uses for cache warming)
    ├── processing/backends/  (uses for annotation enhancement)
    ├── ui/shared/  (uses for parameter analysis)
    │   ↑
    │   ├── pyqt_gui/  (uses shared utilities + pyqtgraph)
    │   └── textual_tui/  (uses shared utilities + plotext)
    └── pyqt_gui/  (direct use for signature analysis)
    └── textual_tui/  (direct use for signature analysis)
```

**Key Properties:**
- ✅ No circular dependencies
- ✅ PyQt and Textual are siblings, not parent/child
- ✅ Shared code lives in framework-agnostic packages
- ✅ Framework-specific code (plotext, pyqtgraph) isolated to respective packages

## Statistics

- **Files Created**: 5 new files
- **Files Moved**: 2 files
- **Files Modified**: 28 files (27 + pyproject.toml)
- **Lines Added**: 794 insertions(+)
- **Lines Deleted**: 344 deletions(-)
- **Net Change**: +450 lines

## Benefits

1. ✅ **No circular dependencies** - Lazy loading prevents import-time circular imports
2. ✅ **PyQt GUI independent of Textual TUI** - Complete separation of concerns
3. ✅ **Framework-agnostic introspection utilities** - Reusable across projects
4. ✅ **Shared UI components eliminate duplication** - DRY principle applied
5. ✅ **plotext no longer required for PyQt GUI users** - Reduced dependency footprint
6. ✅ **Textual TUI can be removed without breaking PyQt GUI** - Modular architecture
7. ✅ **psutil now in core** - System monitoring available to all components

## Migration Guide

### For End Users (PyQt GUI)
No action required. The changes are transparent for PyQt GUI users.

### For End Users (Textual TUI)
No action required. Textual TUI continues to work as before.

### For Developers/External Code
If you import from `openhcs.ui.shared.signature_analyzer` or `openhcs.ui.shared.unified_parameter_analyzer`:

**Before:**
```python
from openhcs.ui.shared.signature_analyzer import SignatureAnalyzer
from openhcs.ui.shared.unified_parameter_analyzer import UnifiedParameterAnalyzer
```

**After:**
```python
from openhcs.introspection.signature_analyzer import SignatureAnalyzer
from openhcs.introspection.unified_parameter_analyzer import UnifiedParameterAnalyzer
```

### For Package Maintainers
If you maintain packages that depend on OpenHCS and use the `[gui]` extra:
- `plotext` is no longer included in `[gui]` extra
- If you need plotext for other purposes, install it separately: `pip install plotext>=5.2.8`

## Bug Fixes
- Fixed `ModuleNotFoundError: No module named 'psutil'` when importing config_framework without gui extras installed

## Known Issues
None.

## Contributors
- Tristan Simas (@trissim)

## Commit Hashes
- 2a0e508 - Main refactoring
- 6d073e5 - Add changelog
- dc13ae4 - Fix psutil dependency

