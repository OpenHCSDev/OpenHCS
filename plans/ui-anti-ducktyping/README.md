# UI Anti-Duck-Typing Refactor

**Status:** Planning Phase  
**Goal:** Eliminate all duck typing from OpenHCS UI layer  
**Target Reduction:** 70%+ code reduction (2654 → ~800 lines in ParameterFormManager)

## Problem Statement

The OpenHCS UI layer extensively uses duck typing (hasattr checks, getattr with defaults, attribute-based dispatch) which contradicts the architectural discipline present in the core systems (memory, IO backends, unified registry).

**Duck Typing Smells:**
- `hasattr(widget, 'method_name')` checks everywhere
- `getattr(widget, 'attr', default)` fallback patterns
- Attribute-based dispatch tables: `[('set_value', lambda w, v: w.set_value(v)), ...]`
- Try-except AttributeError patterns
- Method presence testing instead of explicit contracts

**Why This Is Bad:**
1. **No explicit contracts** - relies on "if it quacks like a duck"
2. **Silent failures** - hasattr hides missing implementations
3. **Undiscoverable** - can't find all widgets implementing a protocol
4. **No compile-time safety** - typos fail at runtime
5. **Violates OpenHCS fail-loud principle**

## Solution Architecture

Replace duck typing with **protocol-based architecture** using patterns from OpenHCS's elegant existing systems:

### Elegant Patterns to Emulate

1. **StorageBackendMeta** (IO backends):
   - Metaclass auto-registration
   - Explicit type attributes
   - Fail-loud on missing implementations
   - Discoverable via registry

2. **MemoryTypeConverter** (memory system):
   - ABC with enforced interface
   - Adapter pattern for inconsistent APIs
   - Type-safe dispatch
   - Auto-generated implementations

3. **LibraryRegistryBase** (unified registry):
   - Centralized operations in base class
   - Enforced abstract attributes
   - Enum-driven polymorphic dispatch
   - 70% code reduction achieved

## Implementation Plans

### Plan 01: Widget Protocol System
**File:** `plan_01_widget_protocol_system.md`

Create explicit widget protocol ABCs and metaclass auto-registration:
- `ValueGettable` / `ValueSettable` protocols
- `PlaceholderCapable` / `RangeConfigurable` protocols
- `WidgetMeta` metaclass for auto-registration
- `WidgetDispatcher` for protocol-based dispatch
- Global `WIDGET_IMPLEMENTATIONS` registry

**Replaces:** hasattr checks, attribute-based dispatch

### Plan 02: Widget Adapter Pattern
**File:** `plan_02_widget_adapter_pattern.md`

Create adapter classes wrapping Qt widgets to implement protocols:
- `LineEditAdapter` / `SpinBoxAdapter` / `ComboBoxAdapter`
- Normalize Qt's inconsistent APIs (`.text()` vs `.value()` vs `.currentData()`)
- `WidgetFactory` with type-based dispatch
- Auto-registration via `WidgetMeta`

**Replaces:** Duck typing dispatch tables, method presence testing

### Plan 03: ParameterFormManager Simplification
**File:** `plan_03_parameter_form_simplification.md`

Massive simplification using widget protocols:
- Delete `WIDGET_UPDATE_DISPATCH` / `WIDGET_GET_DISPATCH`
- Delete `ALL_INPUT_WIDGET_TYPES` hardcoded tuple
- Create `WidgetOperations` service
- Reduce from 2654 lines to ~800 lines (70% reduction)

**Replaces:** Scattered duck typing, dispatch table iterations

### Plan 04: Signal Connection Registry
**File:** `plan_04_signal_connection_registry.md`

Eliminate duck typing from signal connections:
- `ChangeSignalEmitter` protocol
- Explicit signal connection in adapters
- Protocol-based signal dispatch
- Consistent callback signatures

**Replaces:** hasattr signal detection, inconsistent callbacks

### Plan 05: Migration and Validation
**File:** `plan_05_migration_and_validation.md`

Migration strategy and validation framework:
- 3-phase migration plan
- AST-based duck typing detection tests
- Protocol implementation validation
- Performance benchmarks
- Documentation updates

**Ensures:** No duck typing creeps back in

## Expected Benefits

### Code Reduction
| Component | Before | After | Reduction |
|-----------|--------|-------|-----------|
| ParameterFormManager | 2654 lines | ~800 lines | 70% |
| Widget dispatch tables | ~100 lines | 0 lines | 100% |
| Duck typing helpers | ~200 lines | 0 lines | 100% |
| Widget creation logic | ~300 lines | ~50 lines | 83% |
| **TOTAL** | **~3254 lines** | **~850 lines** | **74%** |

### Architectural Improvements

1. **Explicit Contracts:**
   - ABCs declare what widgets must implement
   - `isinstance()` checks instead of `hasattr()`
   - Fail-loud on protocol violations

2. **Discoverability:**
   - `WIDGET_IMPLEMENTATIONS` registry shows all widgets
   - `WIDGET_CAPABILITIES` shows which protocols each widget implements
   - IDE autocomplete works correctly

3. **Type Safety:**
   - Compile-time checking via protocols
   - Refactoring is safe (rename method = compiler error)
   - No runtime surprises from typos

4. **Maintainability:**
   - Single source of truth for widget operations
   - Adding new widget: implement protocols + set `_widget_id`
   - No hunting for scattered hasattr checks

5. **Consistency:**
   - All widgets use same interface (`.get_value()`, `.set_value()`)
   - All signal connections use same pattern
   - All placeholder handling uses same protocol

## Migration Path

### Phase 1: Foundation (Plans 01-02)
**Dependencies:** None  
**Deliverables:**
- Widget protocol ABCs
- Widget registry metaclass
- Widget adapters for Qt widgets
- Widget factory and dispatcher

**Validation:**
- All adapters auto-register
- All adapters implement protocols
- Factory creates correct widgets
- Dispatcher fails loud on violations

### Phase 2: Operations Layer (Plans 03-04)
**Dependencies:** Phase 1 complete  
**Deliverables:**
- Widget operations service
- Signal connection protocols
- ParameterFormManager simplification
- Delete duck typing dispatch tables

**Validation:**
- All operations use protocol dispatch
- No hasattr checks remain
- No dispatch tables remain
- All signals use protocols

### Phase 3: Cleanup and Validation (Plan 05)
**Dependencies:** Phase 2 complete  
**Deliverables:**
- Delete obsolete duck typing code
- Add architectural validation tests
- Update documentation
- Performance benchmarks

**Validation:**
- Zero duck typing patterns in codebase
- All tests pass
- Performance equal or better

## Validation Framework

### Static Analysis
```python
# AST-based duck typing detection
test_no_duck_typing_in_ui_layer()
test_no_dispatch_tables_in_ui()
```

### Runtime Validation
```python
# Protocol implementation verification
test_all_widgets_implement_protocols()
test_widget_auto_registration()
```

### Performance Benchmarks
```python
# Ensure protocol dispatch is fast
test_protocol_dispatch_performance()
```

## Files to Create

**New Files:**
1. `openhcs/ui/shared/widget_protocols.py` - Protocol ABCs
2. `openhcs/ui/shared/widget_registry.py` - Metaclass and registries
3. `openhcs/ui/shared/widget_adapters.py` - Qt widget adapters
4. `openhcs/ui/shared/widget_factory.py` - Type-based widget factory
5. `openhcs/ui/shared/widget_dispatcher.py` - Protocol-based dispatcher
6. `openhcs/ui/shared/widget_operations.py` - Centralized operations
7. `tests/architecture/test_no_duck_typing.py` - Validation tests
8. `tests/performance/test_widget_protocol_performance.py` - Benchmarks

**Files to Modify:**
1. `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` - Massive simplification
2. `openhcs/pyqt_gui/widgets/shared/widget_strategies.py` - Remove duck typing
3. `openhcs/ui/shared/parameter_type_utils.py` - Remove hasattr checks

**Files to Delete (or gut):**
- Duck typing dispatch tables
- Attribute-based fallback chains
- hasattr helper functions

## Success Criteria

✅ **Zero duck typing patterns** in UI layer (verified by AST tests)  
✅ **70%+ code reduction** in ParameterFormManager  
✅ **All widgets implement protocols** (verified by runtime tests)  
✅ **Performance equal or better** than duck typing approach  
✅ **All existing tests pass** with new architecture  
✅ **Documentation updated** to reflect new patterns  

## Next Steps

1. **Review plans** - Get approval on architectural approach
2. **Implement Phase 1** - Foundation (protocols, adapters, registry)
3. **Implement Phase 2** - Operations layer and simplification
4. **Implement Phase 3** - Cleanup and validation
5. **Run validation suite** - Ensure no duck typing remains
6. **Performance benchmarks** - Verify no regression
7. **Update documentation** - Document new architecture

---

**Architectural Principle:**  
*"Explicit contracts over implicit duck typing. Fail-loud over fail-silent. Discoverable over scattered."*

