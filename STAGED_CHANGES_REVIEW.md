# Staged Changes Review - WIP

**Total diff lines**: 6558
**Review progress**: 100% (6558/6558 lines) ✅ COMPLETE

---

## Review Process

Reviewing in chunks of ~300 lines, updating this file every ~1300 lines (20% progress).

---

## Files Changed (29 total)

### Config Framework (2 files)
- `openhcs/config_framework/lazy_factory.py` - LazyDataclass base class
- `openhcs/config_framework/placeholder.py` - Deprecated has_lazy_resolution()

### UI Shared (3 files)
- `openhcs/ui/shared/parameter_info_types.py` - NEW: Discriminated unions
- `openhcs/ui/shared/parameter_form_service.py` - Updated to use discriminated unions
- `openhcs/utils/string_case.py` - NEW: String case utilities

### PyQt GUI Services (17 files - NEW)
- `parameter_service_abc.py` - ABC with auto-discovery dispatch
- `parameter_reset_service.py` - Type-safe reset handlers
- `nested_value_collection_service.py` - Type-safe collection handlers
- `widget_finder_service.py` - Widget lookup utilities
- `widget_update_service.py` - Widget value updates
- `widget_styling_service.py` - Widget styling logic
- `signal_blocking_service.py` - Signal blocking context manager
- `signal_connection_service.py` - Signal connection utilities
- `enabled_field_styling_service.py` - Enabled field styling
- `placeholder_refresh_service.py` - Placeholder refresh logic
- `form_build_orchestrator.py` - Form building orchestration
- `initialization_services.py` - Initialization logic
- `initialization_step_factory.py` - Initialization step factory
- `initial_refresh_strategy.py` - Initial refresh strategy
- `enum_dispatch_service.py` - Enum-based dispatch
- `flag_context_manager.py` - Flag context manager
- `dataclass_unpacker.py` - Dataclass unpacking
- `cross_window_registration.py` - Cross-window registration
- `RESET_CONSOLIDATION_ANALYSIS.md` - Documentation
- `RESET_STRATEGY_DEBUG.md` - Documentation

### PyQt GUI Widgets (3 files)
- `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` - MASSIVE refactor (999 deletions, 232 additions)
- `openhcs/pyqt_gui/widgets/shared/widget_creation_config.py` - Updated
- `openhcs/pyqt_gui/widgets/plate_manager.py` - Updated

### Textual TUI (1 file)
- `openhcs/textual_tui/widgets/shared/parameter_form_manager.py` - Updated

---

## Review Starting...

### CHUNK 1-3: Config Framework - LazyDataclass Base Class (lines 1-900)

**Files**: `lazy_factory.py`, `placeholder.py`, `plate_manager.py`

#### lazy_factory.py Changes:
1. **NEW: `LazyDataclass` base class** (lines 84-100)
   - Empty marker class for isinstance() checks
   - Eliminates duck typing (hasattr checks)
   - All lazy dataclasses inherit from this
   - Works with both instances and types
   - Naturally handles Optional without unwrapping

2. **NEW: `is_lazy_dataclass()` function** (lines 38-70)
   - Type-safe check using isinstance/issubclass
   - Replaces hasattr() duck typing smell
   - Works with Optional types without unwrapping
   - Comprehensive docstring with examples

3. **REFACTOR: Eliminated if-elif duplication** (lines 400-417)
   - OLD: Duplicated make_dataclass() call in if-elif branches
   - NEW: Extract bases tuple, single make_dataclass() call
   - Bases always include LazyDataclass
   - Optionally include base_class if no metaclass conflict

**Assessment**: ✅ EXCELLENT - Eliminates duck typing, reduces duplication

#### placeholder.py Changes:
1. **DEPRECATED: `has_lazy_resolution()`** (lines 31-40)
   - Now delegates to is_lazy_dataclass()
   - Marked as deprecated in docstring
   - Removed unwrapping logic (no longer needed)
   - Removed hasattr() duck typing

**Assessment**: ✅ GOOD - Proper deprecation path

#### plate_manager.py Changes (lines 150-600):
1. **REMOVED: Internal completion signals** (lines 74-77)
   - Deleted _execution_complete_signal
   - Deleted _execution_error_signal
   - Simplified async execution flow

2. **REFACTOR: ZMQ execution from submit→execute** (lines 980-1050)
   - Changed from submit_pipeline() to execute_pipeline()
   - Removed background polling thread
   - Removed _start_completion_poller()
   - Removed _on_execution_complete()
   - Removed _on_execution_error()
   - Now uses synchronous execute in executor (non-blocking UI)
   - Handles cancellation inline

3. **REFACTOR: Stop execution simplified** (lines 1078-1140)
   - Removed "Force Kill" two-click pattern
   - Removed force_kill_ready state
   - Now uses single graceful kill (same as Quit button)
   - Cleaner error handling

4. **REMOVED: _find_main_window()** (line 1726)
   - Dead code elimination

**Assessment**: ✅ GOOD - Simplifies async execution, removes complexity

---

### CHUNK 4-6: ParameterFormManager Massive Refactor (lines 900-1800)

**File**: `parameter_form_manager.py`

#### Major Changes:

1. **NEW: FormManagerConfig dataclass** (lines 90-108)
   - Consolidates 8 optional __init__ parameters
   - Reduces signature from 10→3 parameters (70% reduction)
   - Follows OpenHCS dataclass config pattern

2. **REFACTOR: __init__ using metaprogramming** (lines 200-320)
   - OLD: 150+ lines of manual initialization
   - NEW: 10 steps using service delegation + auto-unpacking
   - Uses `unpack_to_self()` metaprogramming helper
   - Each step is a service that returns a dataclass
   - Auto-unpacks fields to self

   **Steps**:
   - STEP 1: Extract parameters (ParameterExtractionService)
   - STEP 2: Build config (ConfigBuilderService)
   - STEP 3: Extract defaults (UnifiedParameterAnalyzer)
   - STEP 4: Initialize tracking attributes (consolidated)
   - STEP 5: Initialize services (ServiceFactoryService)
   - STEP 6: Setup UI
   - STEP 7: Connect signals (SignalConnectionService)
   - STEP 8: Detect user-set fields
   - STEP 9: Mark initial load complete
   - STEP 10: Execute initial refresh (InitialRefreshStrategy)

3. **DELETED: Manual parameter extraction** (lines 330-380)
   - Removed _extract_parameters_from_object()
   - Removed _auto_detect_global_config_type()
   - Removed _extract_parameter_defaults()
   - Removed _is_lazy_dataclass()
   - All delegated to services

4. **REFACTOR: build_form() using orchestrator** (lines 463-490)
   - OLD: 200+ lines of async/sync duplication
   - NEW: 10 lines delegating to FormBuildOrchestrator
   - Orchestrator handles async/sync decision
   - Eliminates all duplication

5. **REFACTOR: _create_widget_for_param() using discriminated unions** (lines 483-505)
   - OLD: if-elif checking is_optional and is_nested flags
   - NEW: isinstance() checks on ParameterInfo types
   - Type-safe dispatch to parametric widget creation
   - OptionalDataclassInfo → OPTIONAL_NESTED
   - DirectDataclassInfo → NESTED
   - GenericInfo → REGULAR

6. **DELETED: _create_optional_dataclass_widget()** (lines 540-650)
   - Moved to parametric dispatch in widget_creation_config.py
   - 110+ lines eliminated from manager

**Assessment**: ✅ EXCELLENT - 70% code reduction, metaprogramming, service delegation

---

### CHUNK 7-9: Cross-Window Event Handling (lines 1800-2700)

**File**: `parameter_form_manager.py` (continued)

1. **REFACTOR: Unified cross-window event handler** (lines 2000-2030)
   - OLD: _on_cross_window_context_changed() and _on_cross_window_context_refreshed() with duplicate logic
   - NEW: Single _on_cross_window_event() method
   - Aliases for signal connections (Qt signature matching)
   - Eliminates 30+ lines of duplication

2. **REFACTOR: Inlined _do_cross_window_refresh()** (lines 2043-2055)
   - Single-use method inlined into lambda
   - Reduces indirection
   - Clearer control flow

3. **DELETED: Helper methods** (lines 2058-2080)
   - Removed _find_live_values_for_type() (delegated)
   - Removed _collect_live_context_from_other_windows() (delegated)
   - All logic moved to PlaceholderRefreshService

**Assessment**: ✅ GOOD - Eliminates duplication, reduces indirection

---

### CHUNK 10-15: New Service Files (lines 2700-4500)

**17 NEW service files created** in `openhcs/pyqt_gui/widgets/shared/services/`

#### Core Service Infrastructure:

1. **parameter_service_abc.py** (207 lines)
   - ABC for all parameter services
   - Auto-discovery of handler methods via naming convention
   - Type-safe dispatch using ParameterInfo class names
   - Eliminates if-elif-else chains
   - Pattern: `_reset_OptionalDataclassInfo()`, `_reset_DirectDataclassInfo()`, etc.

2. **parameter_reset_service.py** (210 lines)
   - Inherits from ParameterServiceABC
   - Three handlers: _reset_OptionalDataclassInfo, _reset_DirectDataclassInfo, _reset_GenericInfo
   - Eliminates 80+ lines of type-checking logic
   - Type-safe dispatch via discriminated unions

3. **nested_value_collection_service.py** (171 lines)
   - Inherits from ParameterServiceABC
   - Handles checkbox state logic for Optional[Dataclass]
   - Dataclass reconstruction from nested values
   - Eliminates type-checking smells

#### Widget Services:

4. **widget_finder_service.py** (263 lines)
   - Centralized widget finding logic
   - Methods: find_optional_checkbox(), find_group_box(), get_widget_safe(), etc.
   - Eliminates duplicate findChild() calls
   - Type-safe widget retrieval

5. **widget_update_service.py** (163 lines)
   - Widget value updates
   - Delegates to WidgetOperations ABC
   - Handles None-aware widgets

6. **widget_styling_service.py** (238 lines)
   - Read-only styling
   - Dimming/undimming
   - Color scheme aware
   - Type-specific styling logic

7. **signal_blocking_service.py** (189 lines)
   - Context manager for blocking signals
   - Batch signal blocking
   - Automatic restoration

8. **signal_connection_service.py** (99 lines)
   - Wires all signals during initialization
   - Parameter change → placeholder refresh
   - Enabled field → styling updates
   - Cross-window registration

9. **enabled_field_styling_service.py** (326 lines)
   - Universal enabled field behavior
   - Handles nested config dimming
   - Ancestor-aware styling (if parent disabled, child stays dimmed)
   - Comprehensive logging for debugging

#### Form Building Services:

10. **form_build_orchestrator.py** (214 lines)
    - Orchestrates async/sync widget creation
    - Eliminates 200+ lines of duplication
    - Handles completion callbacks
    - Manages nested manager tracking

11. **initialization_services.py** (231 lines)
    - Metaprogrammed initialization
    - Auto-generates service classes from builder functions
    - Decorator-based registry
    - Services: ParameterExtractionService, ConfigBuilderService, ServiceFactoryService

12. **initialization_step_factory.py** (85 lines)
    - Factory for initialization steps
    - Auto-discovery pattern

13. **initial_refresh_strategy.py** (103 lines)
    - Enum-driven dispatch for initial placeholder refresh
    - Two modes: ROOT_GLOBAL_CONFIG, OTHER_WINDOW
    - Eliminates complex boolean logic

#### Utility Services:

14. **enum_dispatch_service.py** (162 lines)
    - ABC for enum-based dispatch
    - Generic pattern for strategy dispatch
    - Used by NestedValueCollectionService, InitialRefreshStrategy

15. **flag_context_manager.py** (224 lines)
    - Context manager for boolean flags
    - Automatic restoration
    - Supports nested contexts

16. **dataclass_unpacker.py** (12 lines)
    - Metaprogramming helper
    - Auto-unpacks dataclass fields to self
    - Supports field renaming and prefixes

17. **cross_window_registration.py** (61 lines)
    - Context manager for cross-window registration
    - Ensures cleanup on dialog close
    - Replaces manual registration in __init__

18. **placeholder_refresh_service.py** (214 lines)
    - Placeholder refresh logic
    - Live context collection
    - Sibling inheritance

#### Documentation Files:

19. **RESET_CONSOLIDATION_ANALYSIS.md** (286 lines)
    - Analysis of reset method consolidation
    - Explains why three separate methods are needed
    - Domain semantics documentation

20. **RESET_STRATEGY_DEBUG.md** (108 lines)
    - Debugging notes for reset strategy
    - Type-driven dispatch explanation

**Assessment**: ✅ EXCELLENT - Massive service layer extraction, eliminates 1000+ lines of duplication

---

### CHUNK 16-18: UI Shared Changes (lines 4500-5500)

**Files**: `parameter_info_types.py`, `parameter_form_service.py`, `string_case.py`

#### parameter_info_types.py (NEW - 252 lines):
1. **ParameterInfoMeta metaclass**
   - Auto-registration of ParameterInfo subclasses
   - Zero boilerplate for new types

2. **Three ParameterInfo types**:
   - OptionalDataclassInfo: Optional[Dataclass] with checkbox
   - DirectDataclassInfo: Direct Dataclass (always exists)
   - GenericInfo: Generic parameters (fallback)

3. **create_parameter_info() factory**
   - Auto-selects correct type via matches() predicates
   - Type-safe dispatch
   - Eliminates if-elif-else chains

**Assessment**: ✅ EXCELLENT - React-style discriminated unions, zero boilerplate

#### parameter_form_service.py Changes:
1. **Removed old ParameterInfo dataclass**
   - Replaced with discriminated union types
   - Updated imports

2. **Updated FormStructure**
   - Added get_parameter_info() method
   - Type-safe parameter info retrieval

3. **Updated _create_parameter_info()**
   - Uses create_parameter_info() factory
   - Eliminates flag-based logic

**Assessment**: ✅ GOOD - Integrates discriminated unions

#### string_case.py (NEW - 14 lines):
- String case conversion utilities
- snake_case, camelCase, PascalCase conversions

**Assessment**: ✅ GOOD - Utility extraction

---

### CHUNK 19-20: Widget Creation Config (lines 5500-6000)

**File**: `widget_creation_config.py`

1. **REFACTOR: Parametric widget creation**
   - WidgetCreationType enum (REGULAR, NESTED, OPTIONAL_NESTED)
   - create_widget_parametric() function
   - Eliminates three separate widget creation methods

2. **NEW: Optional dataclass widget creation**
   - Moved from parameter_form_manager.py
   - 110+ lines extracted to config file
   - Checkbox + GroupBox + nested form pattern

3. **Widget creation configuration**
   - Centralized widget creation logic
   - Type-driven dispatch

**Assessment**: ✅ GOOD - Consolidates widget creation patterns

---

### CHUNK 21-22: Textual TUI Updates (lines 6000-6558)

**File**: `textual_tui/widgets/shared/parameter_form_manager.py`

1. **Updated to use discriminated unions**
   - isinstance() checks instead of flag checks
   - Matches PyQt6 refactoring

2. **Import updates**
   - Uses parameter_info_types module
   - Type-safe dispatch

**Assessment**: ✅ GOOD - Maintains consistency with PyQt6

---

## OVERALL ASSESSMENT

### Code Metrics:
- **Total files changed**: 29
- **New files**: 20 (17 services + 3 shared)
- **Lines added**: 4468
- **Lines deleted**: 1284
- **Net change**: +3184 lines
- **parameter_form_manager.py**: -767 lines (999 deletions, 232 additions) = **77% reduction**

### Architecture Improvements:

1. **✅ ANTI-DUCK-TYPING**:
   - LazyDataclass base class eliminates hasattr() checks
   - isinstance() checks throughout
   - Type-safe dispatch via discriminated unions

2. **✅ SERVICE LAYER EXTRACTION**:
   - 17 new service classes
   - Single responsibility principle
   - Testable, reusable components

3. **✅ METAPROGRAMMING**:
   - Auto-discovery via metaclasses
   - Decorator-based registration
   - unpack_to_self() helper
   - Eliminates boilerplate

4. **✅ DISCRIMINATED UNIONS**:
   - React-style pattern
   - Type-safe dispatch
   - Zero boilerplate for new types

5. **✅ CODE REDUCTION**:
   - parameter_form_manager.py: 77% reduction
   - Eliminated 200+ lines of async/sync duplication
   - Eliminated 110+ lines of widget creation duplication
   - Eliminated 80+ lines of reset logic duplication

### Concerns:

1. **⚠️ COMPLEXITY SHIFT**:
   - Logic moved from one file to 17 services
   - Harder to trace execution flow
   - More indirection

2. **⚠️ DOCUMENTATION FILES IN CODE**:
   - RESET_CONSOLIDATION_ANALYSIS.md (286 lines)
   - RESET_STRATEGY_DEBUG.md (108 lines)
   - Should these be in docs/ instead?

3. **⚠️ METAPROGRAMMING OVERHEAD**:
   - initialization_services.py uses heavy metaprogramming
   - May be harder to debug
   - Auto-generation via introspection

4. **⚠️ MIXED CONCERNS**:
   - LazyDataclass changes mixed with UI refactoring
   - ZMQ execution changes mixed with service extraction
   - Should be separate commits

### Recommendations:

1. **SPLIT INTO MULTIPLE COMMITS**:
   - Commit 1: LazyDataclass base class (lazy_factory.py, placeholder.py)
   - Commit 2: Discriminated unions (parameter_info_types.py, parameter_service_abc.py)
   - Commit 3: Service layer extraction (17 service files)
   - Commit 4: ParameterFormManager refactor (parameter_form_manager.py)
   - Commit 5: ZMQ execution simplification (plate_manager.py)
   - Commit 6: Widget creation config (widget_creation_config.py)
   - Commit 7: Textual TUI updates

2. **MOVE DOCUMENTATION**:
   - Move .md files to docs/ or remove from commit

3. **ADD TESTS**:
   - Test discriminated union dispatch
   - Test service layer components
   - Test LazyDataclass isinstance() checks

---

## FINAL VERDICT

**This is a MASSIVE refactoring** that fundamentally changes the architecture of the UI system.

**Positives**:
- ✅ Eliminates duck typing
- ✅ 77% code reduction in main file
- ✅ Service layer extraction
- ✅ Type-safe dispatch
- ✅ Metaprogramming patterns

**Negatives**:
- ⚠️ Too many changes in one commit
- ⚠️ Complexity shifted to many files
- ⚠️ Documentation files in code directory
- ⚠️ Mixed concerns (LazyDataclass + UI + ZMQ)

**Recommendation**: SPLIT INTO 7 SEPARATE COMMITS as outlined above.

---

## DETAILED FILE-BY-FILE REVIEW FOR SPHINX DOCUMENTATION

### NEW FILES REQUIRING SPHINX DOCUMENTATION (27 files)

---

### 1. Config Framework Changes (2 files)

#### `openhcs/config_framework/lazy_factory.py` (MODIFIED)
**What changed**:
- Added `LazyDataclass` base class (empty marker class)
- Added `is_lazy_dataclass(obj_or_type)` function
- Refactored `_create_lazy_dataclass_unified()` to eliminate duplication

**Sphinx documentation needed**:
- Document LazyDataclass base class in architecture docs
- Document is_lazy_dataclass() in API reference
- Update lazy configuration system docs to mention isinstance() checks
- Add migration guide from has_lazy_resolution() to is_lazy_dataclass()

**Key concepts**:
- Anti-duck-typing: isinstance() instead of hasattr()
- Works with Optional types without unwrapping
- All lazy dataclasses inherit from LazyDataclass

---

#### `openhcs/config_framework/placeholder.py` (MODIFIED)
**What changed**:
- Deprecated `has_lazy_resolution()` method
- Now delegates to `is_lazy_dataclass()`

**Sphinx documentation needed**:
- Mark has_lazy_resolution() as deprecated in API docs
- Add deprecation warning with migration path

---

### 2. UI Shared - Discriminated Unions (1 NEW file)

#### `openhcs/ui/shared/parameter_info_types.py` (NEW - 252 lines)
**Purpose**: React-style discriminated unions for type-safe parameter handling

**Key components**:
- `ParameterInfoMeta` - Metaclass for auto-registration
- `OptionalDataclassInfo` - Optional[Dataclass] parameters
- `DirectDataclassInfo` - Direct Dataclass parameters
- `GenericInfo` - Generic parameters (fallback)
- `create_parameter_info()` - Factory function

**Sphinx documentation needed**:
- New architecture doc: "Discriminated Unions in OpenHCS UI"
- Explain React-style pattern and why it's used
- Document each ParameterInfo type with examples
- Document the metaclass auto-registration pattern
- Add tutorial: "Adding a New ParameterInfo Type"
- API reference for all classes and factory function

**Key concepts**:
- Type-safe dispatch without if-elif-else
- Metaclass auto-registration (zero boilerplate)
- Type predicates via matches() static methods
- Union type for type hints

---

### 3. UI Shared - Other Changes (2 files)

#### `openhcs/ui/shared/parameter_form_service.py` (MODIFIED)
**What changed**:
- Removed old ParameterInfo dataclass
- Updated to use discriminated union types
- Added get_parameter_info() to FormStructure

**Sphinx documentation needed**:
- Update API docs to reflect new ParameterInfo types
- Document FormStructure.get_parameter_info()

---

#### `openhcs/utils/string_case.py` (NEW - 14 lines)
**Purpose**: String case conversion utilities

**Sphinx documentation needed**:
- Add to utilities API reference
- Document each conversion function

---

### 4. PyQt GUI Services - Core Service Infrastructure (3 NEW files)

#### `openhcs/pyqt_gui/widgets/shared/services/parameter_service_abc.py` (NEW - 207 lines)
**Purpose**: ABC for all parameter services with auto-discovery dispatch

**Key components**:
- `ParameterServiceABC` - Base class for parameter services
- Auto-discovery of handler methods via naming convention
- Type-safe dispatch using ParameterInfo class names
- `dispatch()` method for automatic routing

**Sphinx documentation needed**:
- New architecture doc: "Parameter Service Pattern"
- Explain auto-discovery mechanism
- Document naming convention for handlers
- Tutorial: "Creating a New Parameter Service"
- API reference with examples
- Diagram showing dispatch flow

**Key concepts**:
- Handler prefix pattern (e.g., `_reset_`, `_collect_`)
- Auto-discovery via dir() introspection
- Type-safe dispatch via __class__.__name__
- No if-elif-else chains needed

---

#### `openhcs/pyqt_gui/widgets/shared/services/parameter_reset_service.py` (NEW - 210 lines)
**Purpose**: Type-safe parameter reset with discriminated union dispatch

**Key components**:
- Inherits from ParameterServiceABC
- Three handlers: `_reset_OptionalDataclassInfo`, `_reset_DirectDataclassInfo`, `_reset_GenericInfo`
- `reset_parameter()` public method

**Sphinx documentation needed**:
- Document reset semantics for each parameter type
- Explain checkbox-controlled optional dataclasses
- Explain in-place recursive reset for direct dataclasses
- Explain lazy inheritance tracking for generic fields
- API reference with examples

**Key concepts**:
- Three fundamentally different reset behaviors
- Checkbox state management
- Object identity preservation
- Reset field tracking

---

#### `openhcs/pyqt_gui/widgets/shared/services/nested_value_collection_service.py` (NEW - 171 lines)
**Purpose**: Type-safe nested value collection with discriminated union dispatch

**Key components**:
- Inherits from ParameterServiceABC
- Three handlers for collecting nested values
- Checkbox state logic for Optional[Dataclass]
- Dataclass reconstruction

**Sphinx documentation needed**:
- Document value collection semantics
- Explain checkbox state handling
- Explain dataclass reconstruction
- API reference with examples

---

### 5. PyQt GUI Services - Widget Services (6 NEW files)

#### `openhcs/pyqt_gui/widgets/shared/services/widget_finder_service.py` (NEW - 263 lines)
**Purpose**: Centralized widget finding logic

**Key methods**:
- `find_optional_checkbox()` - Find checkbox for Optional[Dataclass]
- `find_group_box()` - Find GroupBox container
- `get_widget_safe()` - Safe widget retrieval
- `find_all_input_widgets()` - Find all input widgets
- `find_nested_checkbox()` - Find checkbox within optional dataclass
- `find_reset_button()` - Find reset button
- `has_widget()` - Check widget existence

**Sphinx documentation needed**:
- Document each method with examples
- Explain widget naming conventions
- Explain field ID generation
- API reference

---

#### `openhcs/pyqt_gui/widgets/shared/services/widget_update_service.py` (NEW - 163 lines)
**Purpose**: Widget value updates

**Sphinx documentation needed**:
- Document widget update patterns
- Explain delegation to WidgetOperations ABC
- API reference

---

#### `openhcs/pyqt_gui/widgets/shared/services/widget_styling_service.py` (NEW - 238 lines)
**Purpose**: Widget styling operations

**Key methods**:
- `make_readonly()` - Apply read-only styling
- `apply_dimming()` - Dim widgets
- `remove_dimming()` - Remove dimming

**Sphinx documentation needed**:
- Document styling patterns
- Explain color scheme integration
- Document type-specific styling
- API reference

---

#### `openhcs/pyqt_gui/widgets/shared/services/signal_blocking_service.py` (NEW - 189 lines)
**Purpose**: Context manager for blocking signals

**Key components**:
- `block_signals()` context manager
- Batch signal blocking
- Automatic restoration

**Sphinx documentation needed**:
- Document context manager pattern
- Explain use cases (preventing recursive updates)
- API reference with examples

---

#### `openhcs/pyqt_gui/widgets/shared/services/signal_connection_service.py` (NEW - 99 lines)
**Purpose**: Signal wiring during initialization

**Key methods**:
- `connect_all_signals()` - Wire all signals
- `register_cross_window_signals()` - Cross-window registration

**Sphinx documentation needed**:
- Document signal wiring patterns
- Explain cross-window update mechanism
- API reference

---

#### `openhcs/pyqt_gui/widgets/shared/services/enabled_field_styling_service.py` (NEW - 326 lines)
**Purpose**: Universal enabled field behavior

**Key components**:
- Handles nested config dimming
- Ancestor-aware styling
- Comprehensive logging

**Sphinx documentation needed**:
- Document enabled field semantics
- Explain nested config dimming rules
- Explain ancestor propagation
- API reference with examples

**Key concepts**:
- enabled=False → visual dimming WITHOUT blocking input
- Nested configs inherit parent's disabled state
- Separate from Optional[Dataclass] None state

---

### 6. PyQt GUI Services - Form Building (4 NEW files)

#### `openhcs/pyqt_gui/widgets/shared/services/form_build_orchestrator.py` (NEW - 214 lines)
**Purpose**: Orchestrates async/sync widget creation

**Key components**:
- `build_widgets()` - Main orchestration method
- Async/sync decision logic
- Completion callback management
- Nested manager tracking

**Sphinx documentation needed**:
- Document async widget creation pattern
- Explain sync vs async decision criteria
- Explain completion callback flow
- Document nested manager coordination
- API reference

**Key concepts**:
- Hybrid sync/async for large forms
- Initial sync widgets for fast render
- Async remaining widgets
- Callback orchestration

---

#### `openhcs/pyqt_gui/widgets/shared/services/initialization_services.py` (NEW - 231 lines)
**Purpose**: Metaprogrammed initialization services

**Key components**:
- `ExtractedParameters` dataclass
- `ParameterFormConfig` dataclass
- `ManagerServices` dataclass (auto-generated via metaclass)
- Builder registry pattern
- Auto-unpacking via dataclass introspection

**Sphinx documentation needed**:
- New architecture doc: "Metaprogrammed Initialization Pattern"
- Explain builder registry
- Explain auto-unpacking mechanism
- Document ServiceRegistryMeta metaclass
- Tutorial: "Adding a New Initialization Step"
- API reference

**Key concepts**:
- Decorator-based builder registration
- Metaclass auto-discovery of services
- Dataclass field metadata for computed values
- unpack_to_self() pattern

---

#### `openhcs/pyqt_gui/widgets/shared/services/initialization_step_factory.py` (NEW - 85 lines)
**Purpose**: Factory for initialization steps

**Sphinx documentation needed**:
- Document factory pattern
- API reference

---

#### `openhcs/pyqt_gui/widgets/shared/services/initial_refresh_strategy.py` (NEW - 103 lines)
**Purpose**: Enum-driven dispatch for initial placeholder refresh

**Key components**:
- `RefreshMode` enum (ROOT_GLOBAL_CONFIG, OTHER_WINDOW)
- Inherits from EnumDispatchService
- Two refresh strategies

**Sphinx documentation needed**:
- Document refresh modes
- Explain root global config vs other window semantics
- API reference

---

### 7. PyQt GUI Services - Utility Services (4 NEW files)

#### `openhcs/pyqt_gui/widgets/shared/services/enum_dispatch_service.py` (NEW - 162 lines)
**Purpose**: ABC for enum-based dispatch

**Key components**:
- Generic EnumDispatchService[T] base class
- `_determine_strategy()` abstract method
- `dispatch()` method
- Handler registration pattern

**Sphinx documentation needed**:
- New architecture doc: "Enum Dispatch Pattern"
- Explain generic type parameter
- Document handler registration
- Tutorial: "Creating an Enum Dispatch Service"
- API reference with examples

**Key concepts**:
- Strategy pattern via enums
- Type-safe dispatch
- Generic base class

---

#### `openhcs/pyqt_gui/widgets/shared/services/flag_context_manager.py` (NEW - 224 lines)
**Purpose**: Context manager for boolean flags

**Key components**:
- `FlagContextManager` class
- `ManagerFlag` enum
- Automatic flag restoration
- Nested context support

**Sphinx documentation needed**:
- Document flag management pattern
- Explain use cases (blocking updates during operations)
- API reference with examples

---

#### `openhcs/pyqt_gui/widgets/shared/services/dataclass_unpacker.py` (NEW - 12 lines)
**Purpose**: Metaprogramming helper for auto-unpacking dataclass fields

**Key function**:
- `unpack_to_self()` - Auto-unpack dataclass fields to object

**Sphinx documentation needed**:
- Document unpacking pattern
- Explain field renaming
- Explain prefix support
- API reference with examples

**Key concepts**:
- Metaprogramming via dataclass introspection
- Field mapping via dict
- Prefix support for service unpacking

---

#### `openhcs/pyqt_gui/widgets/shared/services/cross_window_registration.py` (NEW - 61 lines)
**Purpose**: Context manager for cross-window registration

**Key components**:
- `cross_window_registration()` context manager
- Automatic cleanup on dialog close

**Sphinx documentation needed**:
- Document cross-window update mechanism
- Explain registration/unregistration
- API reference with examples

---

#### `openhcs/pyqt_gui/widgets/shared/services/placeholder_refresh_service.py` (NEW - 214 lines)
**Purpose**: Placeholder refresh logic

**Key methods**:
- `refresh_all_placeholders()` - Refresh all placeholders
- `collect_live_context_from_other_windows()` - Collect live context
- Sibling inheritance logic

**Sphinx documentation needed**:
- Document placeholder refresh mechanism
- Explain live context collection
- Explain sibling inheritance
- API reference

---

### 8. Documentation Files (2 NEW files - SHOULD NOT BE IN CODE)

#### `openhcs/pyqt_gui/widgets/shared/services/RESET_CONSOLIDATION_ANALYSIS.md` (286 lines)
**Issue**: Documentation file in code directory

**Recommendation**:
- Move to `docs/source/architecture/` or `docs/development/`
- Or remove from commit entirely (keep in local notes)

---

#### `openhcs/pyqt_gui/widgets/shared/services/RESET_STRATEGY_DEBUG.md` (108 lines)
**Issue**: Debug notes in code directory

**Recommendation**:
- Remove from commit (debugging notes, not production docs)
- Or move to docs/development/ if valuable

---

### 9. Other Modified Files (3 files)

#### `openhcs/pyqt_gui/widgets/plate_manager.py` (MODIFIED)
**What changed**:
- ZMQ execution: submit→execute pattern
- Removed background polling
- Simplified stop execution (no Force Kill)

**Sphinx documentation needed**:
- Update ZMQ execution docs
- Document new execution flow

---

#### `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py` (MODIFIED - MASSIVE)
**What changed**:
- 77% code reduction (999 deletions, 232 additions)
- FormManagerConfig dataclass
- 10-step metaprogrammed initialization
- Service delegation throughout
- Discriminated union dispatch

**Sphinx documentation needed**:
- Major update to ParameterFormManager docs
- Document new initialization flow
- Document service delegation pattern
- Update all examples to use new patterns

---

#### `openhcs/pyqt_gui/widgets/shared/widget_creation_config.py` (MODIFIED)
**What changed**:
- Added parametric widget creation
- Moved optional dataclass widget creation here

**Sphinx documentation needed**:
- Document parametric widget creation pattern
- Document WidgetCreationType enum

---

#### `openhcs/textual_tui/widgets/shared/parameter_form_manager.py` (MODIFIED)
**What changed**:
- Updated to use discriminated unions
- isinstance() checks instead of flags

**Sphinx documentation needed**:
- Update Textual TUI docs to match PyQt6 changes

---

## SPHINX DOCUMENTATION PLAN

### New Architecture Documents Needed:

1. **`docs/source/architecture/discriminated_unions.rst`**
   - React-style discriminated unions
   - ParameterInfo types
   - Type-safe dispatch pattern

2. **`docs/source/architecture/parameter_service_pattern.rst`**
   - ParameterServiceABC
   - Auto-discovery mechanism
   - Handler naming conventions

3. **`docs/source/architecture/enum_dispatch_pattern.rst`**
   - EnumDispatchService
   - Strategy pattern via enums
   - Generic type parameters

4. **`docs/source/architecture/metaprogrammed_initialization.rst`**
   - Builder registry pattern
   - Auto-unpacking mechanism
   - ServiceRegistryMeta metaclass

5. **`docs/source/architecture/lazy_dataclass_system.rst`** (UPDATE EXISTING)
   - Add LazyDataclass base class
   - Add is_lazy_dataclass() function
   - Migration guide from duck typing

### New API Reference Sections Needed:

1. **`docs/source/api/ui/parameter_info_types.rst`**
   - All ParameterInfo classes
   - create_parameter_info() factory
   - ParameterInfoMeta metaclass

2. **`docs/source/api/ui/services/index.rst`**
   - Overview of all services
   - Service categories

3. **`docs/source/api/ui/services/parameter_services.rst`**
   - ParameterServiceABC
   - ParameterResetService
   - NestedValueCollectionService

4. **`docs/source/api/ui/services/widget_services.rst`**
   - WidgetFinderService
   - WidgetUpdateService
   - WidgetStylingService
   - SignalBlockingService
   - SignalConnectionService
   - EnabledFieldStylingService

5. **`docs/source/api/ui/services/form_building_services.rst`**
   - FormBuildOrchestrator
   - InitializationServices
   - InitialRefreshStrategy

6. **`docs/source/api/ui/services/utility_services.rst`**
   - EnumDispatchService
   - FlagContextManager
   - dataclass_unpacker
   - cross_window_registration
   - PlaceholderRefreshService

### Tutorials Needed:

1. **`docs/source/tutorials/adding_parameter_info_type.rst`**
   - How to add a new ParameterInfo type
   - Metaclass auto-registration
   - Writing matches() predicates

2. **`docs/source/tutorials/creating_parameter_service.rst`**
   - How to create a new parameter service
   - Handler naming conventions
   - Using ParameterServiceABC

3. **`docs/source/tutorials/enum_dispatch_service.rst`**
   - How to use EnumDispatchService
   - Defining strategy enums
   - Implementing handlers

---

## ACTION ITEMS FOR COMMIT

1. **REMOVE** documentation files from code directory:
   - `RESET_CONSOLIDATION_ANALYSIS.md`
   - `RESET_STRATEGY_DEBUG.md`

2. **COMMIT** all service files with detailed message

3. **CREATE FOLLOW-UP TASK** to write Sphinx documentation for all new components

4. **VERIFY** all imports work and no circular dependencies


