# Documentation Audit: Off-Topic Content in External Modules

## Summary
Found and fixed several documentation files in `external/pyqt-reactor/` that documented ObjectState instead of pyqt-reactor. These were copy-pasted from the ObjectState module and have been completely rewritten.

## Issues Found & Fixed

### ✅ 1. `external/pyqt-reactor/docs/api/modules.rst`
**Was**: Documents ObjectState modules
**Now**: Documents pyqt-reactor modules (core, protocols, services, forms, widgets, theming, animation, windows, dialogs)

### ✅ 2. `external/pyqt-reactor/docs/state_management.rst`
**Was**: Described ObjectState internals (ObjectState class, ObjectStateRegistry)
**Now**: Describes form state management and ObjectState integration patterns

### ✅ 3. `external/pyqt-reactor/docs/undo_redo.rst`
**Was**: Described ObjectState DAG history system
**Now**: Describes undo/redo integration with forms

### ✅ 4. `external/pyqt-reactor/docs/examples/ui.rst`
**Was**: ObjectState examples (LazyDataclassFactory, config_context, etc.)
**Now**: pyqt-reactor form examples:
- Basic form generation from dataclasses
- ObjectState integration with inherited values
- Reactive field updates with FieldChangeDispatcher
- Theming and styling
- Flash animations

### ✅ 5. `external/pyqt-reactor/docs/examples/index.rst`
**Was**: References ObjectState examples (basic, dual_axis, ui, atomic_operations)
**Now**: References pyqt-reactor examples (ui)

## Additional Fixes

✅ `.gitmodules` - Updated submodule name and URL
✅ `openhcs/pyqt_gui/services/` - Renamed `formgen_providers.py` → `reactor_providers.py`
✅ `external/uneval/paper.bib` - Updated citation key `@pyqtformgen` → `@pyqtreactor`

## Commits

1. **openhcs**:
   - `02958ff6` - Renamed formgen_providers to reactor_providers
   - `d197b0a4` - Updated .gitmodules
   - `6cbfde6e` - Documented audit findings
   - `0f4a66ae` - Updated pyqt-reactor submodule

2. **pyqt-reactor**:
   - `5570cdd` - Fixed all off-topic ObjectState content in docs

3. **uneval**:
   - `f7acfe5` - Updated citation key to pyqtreactor

