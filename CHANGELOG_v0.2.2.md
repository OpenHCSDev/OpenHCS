# Changelog for v0.2.2

## Release Date
2025-10-21

## Overview
Bug fixes and architectural improvements for Windows compatibility and ZMQ execution stability. This release fixes critical import errors on Windows, resolves ZMQ + Fiji hanging issues, and improves the synthetic plate generator workflow.

## Bug Fixes

### Windows Compatibility
- **Fixed Windows import error in PyQt GUI**
  - Issue: PyQt GUI failed to import on Windows due to hard textual dependency in `openhcs/ui/shared/textual_widget_strategies.py`
  - Fix: Made textual imports lazy (inside functions) to avoid requiring textual when only PyQt GUI is used
  - Impact: PyQt GUI now works on Windows without requiring textual to be installed

### ZMQ Execution Server
- **Fixed ZMQ + Fiji executor shutdown hang**
  - Issue: `executor.shutdown(wait=True)` hung indefinitely when Fiji streaming was used with ZMQ execution server
  - Root Cause: `FijiStreamingBackend` was missing `__del__` method, so `cleanup()` was never called when worker processes exited
  - Fix: Added `__del__` method to `FijiStreamingBackend` that calls `cleanup()`, matching the pattern in `NapariStreamingBackend`
  - Impact: ZMQ tests with Fiji now complete successfully without hanging

- **Fixed resource tracker warnings**
  - Issue: 274 leaked shared memory objects from Fiji streaming caused cleanup warnings
  - Fix: Call `resource_tracker.unregister()` in `openhcs/io/streaming.py` after closing shared memory handles
  - Impact: Clean shutdown without resource warnings

### Code Organization
- **Moved textual-specific code to correct module**
  - Issue: `textual_widget_strategies.py` was in `openhcs/ui/shared/` but is textual-specific
  - Fix: Moved to `openhcs/textual_tui/widgets/shared/` where it belongs
  - Impact: Cleaner architecture - `openhcs/ui/shared/` now only contains framework-agnostic utilities

## New Features

### Synthetic Plate Generator
- **Auto-load test pipeline when generating synthetic plates**
  - Added `openhcs/tests/test_pipeline.py` to git repo (multi-step test pipeline)
  - Synthetic plate generator now automatically loads `test_pipeline.py` when a plate is generated
  - Provides complete test workflow: generate plate → auto-load pipeline → ready to run
  - Signal now emits both output directory and pipeline path for better integration

## Technical Details

### Files Changed
- `openhcs/__init__.py` - Version bump to 0.2.2
- `openhcs/io/fiji_stream.py` - Added `__del__` method for cleanup
- `openhcs/io/streaming.py` - Added resource tracker unregister calls
- `openhcs/ui/shared/widget_creation_registry.py` - Updated import path for textual strategies
- `openhcs/textual_tui/widgets/shared/textual_widget_strategies.py` - Moved from `openhcs/ui/shared/`
- `openhcs/pyqt_gui/windows/synthetic_plate_generator_window.py` - Auto-load test pipeline
- `openhcs/pyqt_gui/main.py` - Handle pipeline path from synthetic plate generator
- `openhcs/tests/test_pipeline.py` - Added to git repo

### Commits
1. Fix ZMQ + Fiji hang by adding `__del__` cleanup to FijiStreamingBackend
2. Fix Windows import error: make textual imports lazy in widget strategies
3. Move textual_widget_strategies.py to textual_tui module
4. Add test_pipeline.py and auto-load it when generating synthetic plates

## Migration Guide

### For Users
- No breaking changes
- Windows users can now use PyQt GUI without installing textual
- ZMQ + Fiji tests now work reliably

### For Developers
- If you import from `openhcs.ui.shared.textual_widget_strategies`, update to `openhcs.textual_tui.widgets.shared.textual_widget_strategies`
- If you connect to `SyntheticPlateGeneratorWindow.plate_generated` signal, update slot to accept two parameters: `(output_dir: str, pipeline_path: str)`

## Known Issues
- Textual TUI is deprecated and may have import errors (expected)

## Testing
- All integration tests pass on Linux
- PyQt GUI imports successfully on Windows without textual
- ZMQ + Fiji tests complete in ~48 seconds without hanging

