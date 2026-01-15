# Documentation Audit: Off-Topic Content in External Modules

## Summary
Found several documentation files in `external/pyqt-reactor/` that document ObjectState instead of pyqt-reactor. These appear to be copy-pasted from the ObjectState module and need to be rewritten.

## Critical Issues

### 1. `external/pyqt-reactor/docs/api/modules.rst`
**Problem**: Documents ObjectState modules, not pyqt-reactor
- Lists: `objectstate.config`, `objectstate.lazy_factory`, `objectstate.context_manager`, etc.
- Should document: `pyqt_reactor.forms`, `pyqt_reactor.widgets`, `pyqt_reactor.theming`, `pyqt_reactor.protocols`, etc.

### 2. `external/pyqt-reactor/docs/state_management.rst`
**Problem**: Documents ObjectState class, not pyqt-reactor
- Describes `objectstate.object_state.ObjectState` and `ObjectStateRegistry`
- Should describe: pyqt-reactor's form management, widget lifecycle, state binding

### 3. `external/pyqt-reactor/docs/undo_redo.rst`
**Problem**: Documents ObjectState undo/redo system
- Describes git-like DAG snapshots from ObjectState
- Should describe: pyqt-reactor's undo/redo integration (if any)

### 4. `external/pyqt-reactor/docs/examples/ui.rst`
**Problem**: ObjectState UI examples, not pyqt-reactor
- Shows `LazyDataclassFactory`, `config_context`, `extract_all_configs`
- Should show: pyqt-reactor form creation, widget binding, reactive updates

### 5. `external/pyqt-reactor/docs/examples/index.rst`
**Problem**: References objectstate examples
- Lists: `basic`, `dual_axis`, `ui`, `atomic_operations`
- Should list: pyqt-reactor-specific examples

## Fixed Issues

✅ `.gitmodules` - Updated submodule name and URL
✅ `openhcs/pyqt_gui/services/` - Renamed `formgen_providers.py` → `reactor_providers.py`
✅ `external/uneval/paper.bib` - Updated citation key `@pyqtformgen` → `@pyqtreactor`

## Recommendation

The pyqt-reactor docs need a complete rewrite to document:
- Form generation from dataclasses
- Widget protocols and adapters
- Theming system
- Flash animations
- Window management
- Integration with ObjectState (as a dependency, not the main topic)

