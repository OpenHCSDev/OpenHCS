# plan_07_aggressive_abstraction.md
## Component: ParameterFormManager Aggressive Abstraction

### Objective
Aggressively abstract all low-level widget operations and boilerplate from ParameterFormManager to achieve the original 70% reduction target (2668 → ~800 lines). Current state is 2348 lines (12% reduction) - need additional 58% reduction (~1500 more lines).

### Current State Analysis

**File:** `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`
**Lines:** 2348 (down from 2668)
**Reduction so far:** 320 lines (12%)
**Target:** ~800 lines (70% total reduction)
**Remaining work:** ~1500 lines to remove

### Identified Boilerplate Categories

#### 1. Low-Level Widget Operations (~200 lines)

**Current Pattern:**
```python
def update_widget_value(self, widget: QWidget, value: Any, param_name: str = None, skip_context_behavior: bool = False, exclude_field: str = None) -> None:
    """Mathematical simplification: Unified widget update using shared dispatch."""
    self._execute_with_signal_blocking(widget, lambda: self._dispatch_widget_update(widget, value))
    
    # Only apply context behavior if not explicitly skipped (e.g., during reset operations)
    if not skip_context_behavior:
        self._apply_context_behavior(widget, value, param_name, exclude_field)

def _execute_with_signal_blocking(self, widget: QWidget, operation: callable) -> None:
    """Execute operation with widget signals blocked."""
    widget.blockSignals(True)
    operation()
    widget.blockSignals(False)

def _dispatch_widget_update(self, widget: QWidget, value: Any) -> None:
    """Dispatch widget update using ABC-based operations."""
    self._widget_ops.set_value(widget, value)

def _apply_context_behavior(self, widget: QWidget, value: Any, param_name: str, exclude_field: str = None) -> None:
    """CONSOLIDATED: Apply placeholder behavior using single resolution path."""
    if not param_name or not self.dataclass_type:
        return
    
    # ... 30 more lines of placeholder logic
```

**Problem:** These are all low-level operations that should be in a service class, not in the form manager.

**Solution:** Create `WidgetUpdateService` that handles all widget value updates, signal blocking, and placeholder application.

---

#### 2. Async Widget Creation Boilerplate (~150 lines)

**Current Pattern:**
```python
def build_form(self) -> QWidget:
    # ... 100+ lines of async/sync widget creation logic
    if self.should_use_async(param_count):
        # Track pending nested managers
        if is_root:
            self._pending_nested_managers = {}
        
        # Split parameters
        sync_params = self.form_structure.parameters[:self.INITIAL_SYNC_WIDGETS]
        async_params = self.form_structure.parameters[self.INITIAL_SYNC_WIDGETS:]
        
        # Create initial widgets synchronously
        if sync_params:
            for param_info in sync_params:
                widget = self._create_widget_for_param(param_info)
                content_layout.addWidget(widget)
        
        def on_async_complete():
            # ... 40 lines of completion logic
        
        if async_params:
            self._create_widgets_async(content_layout, async_params, on_complete=on_async_complete)
        else:
            on_async_complete()
    else:
        # Sync widget creation
        for param_info in self.form_structure.parameters:
            widget = self._create_widget_for_param(param_info)
            content_layout.addWidget(widget)
        
        # ... 30 lines of styling/placeholder refresh logic
```

**Problem:** Massive duplication between async and sync paths. Complex state management for async completion.

**Solution:** Create `FormBuildOrchestrator` that handles all async/sync logic, completion callbacks, and placeholder refresh orchestration.

---

#### 3. Optional Dataclass Widget Creation (~180 lines)

**Current Pattern:**
```python
def _create_optional_dataclass_widget(self, param_info) -> QWidget:
    # ... 180 lines of GroupBox creation, checkbox handling, nested form creation, styling callbacks
```

**Problem:** This is the largest single method in the file. It's doing too much:
- Creating GroupBox with custom title
- Creating checkbox + title label + help button + reset button
- Creating nested form
- Connecting checkbox to enable/disable logic
- Managing None state dimming vs enabled field dimming
- Registering styling callbacks

**Solution:** Break into smaller composable pieces:
- `OptionalDataclassWidgetBuilder` class with builder pattern
- Separate methods for title widget, checkbox logic, nested form creation
- Move styling logic to service classes

---

#### 4. Enabled Field Styling Logic (~200 lines)

**Current Pattern:**
```python
def _apply_initial_enabled_styling(self) -> None:
    # ... 50 lines of logic to find enabled checkbox and apply styling

def _refresh_enabled_styling(self) -> None:
    # ... 80 lines of logic to refresh enabled styling

def _on_enabled_field_changed_universal(self, param_name: str, value: Any) -> None:
    # ... 70 lines of logic to handle enabled field changes
```

**Problem:** Enabled field styling is scattered across multiple methods with complex logic for:
- Finding the enabled checkbox widget
- Determining if this is a nested config or top-level form
- Applying dimming to direct widgets vs nested configs
- Handling GroupBox vs regular widgets

**Solution:** Create `EnabledFieldStylingService` that encapsulates all enabled field logic.

---

#### 5. Placeholder Refresh Logic (~150 lines)

**Current Pattern:**
```python
def _refresh_with_live_context(self) -> None:
    # ... 20 lines to collect live context and refresh

def _refresh_all_placeholders(self, live_context: dict = None) -> None:
    # ... 30 lines to refresh placeholders for all widgets

def _collect_live_context_from_other_windows(self) -> dict:
    # ... 50 lines to collect live context from other windows

def _find_live_values_for_type(self, target_type: Type, live_context: dict) -> Optional[dict]:
    # ... 30 lines to find live values for a specific type

def _reconstruct_nested_dataclasses(self, values_dict: dict, template_instance: Any) -> dict:
    # ... 20 lines to reconstruct nested dataclasses from tuple format
```

**Problem:** Placeholder refresh logic is scattered across multiple methods. Complex logic for collecting live context from other windows.

**Solution:** Create `PlaceholderRefreshService` that handles all placeholder refresh logic.

---

#### 6. Cross-Window Update Logic (~200 lines)

**Current Pattern:**
```python
def _emit_cross_window_change(self, param_name: str, value: Any) -> None:
    # ... 40 lines to emit cross-window changes

def _on_cross_window_context_changed(self, field_path: str, new_value: object, editing_object: object, context_object: object):
    # ... 50 lines to handle cross-window context changes

def _is_affected_by_context_change(self, editing_object: object, context_object: object) -> bool:
    # ... 60 lines to determine if affected by context change

def _schedule_cross_window_refresh(self) -> None:
    # ... 20 lines to debounce cross-window refresh

def _on_cross_window_context_refreshed(self, editing_object: object) -> None:
    # ... 30 lines to handle cross-window context refresh
```

**Problem:** Cross-window update logic is complex and scattered. Lots of boilerplate for signal emission, debouncing, and determining affected forms.

**Solution:** Create `CrossWindowUpdateCoordinator` that handles all cross-window update logic.

---

#### 7. Nested Manager Operations (~100 lines)

**Current Pattern:**
```python
def _apply_to_nested_managers(self, operation_func: callable) -> None:
    """Apply operation to all nested managers."""
    for param_name, nested_manager in self.nested_managers.items():
        operation_func(param_name, nested_manager)

def _collect_from_nested_managers(self, collection_func: callable) -> dict:
    """Collect values from all nested managers."""
    results = {}
    for param_name, nested_manager in self.nested_managers.items():
        results[param_name] = collection_func(param_name, nested_manager)
    return results

def _find_nested_manager_by_field_id(self, field_id: str) -> Optional['ParameterFormManager']:
    """Find nested manager by field_id (recursive search)."""
    # ... 20 lines of recursive search logic

def _on_nested_manager_complete(self, nested_manager: 'ParameterFormManager') -> None:
    # ... 30 lines of async completion tracking

def _create_nested_form_inline(self, param_name: str, param_type: Type, current_value: Any) -> 'ParameterFormManager':
    # ... 40 lines of nested form creation
```

**Problem:** Lots of boilerplate for managing nested managers. Pattern 2 from Plan 06 was supposed to address this but wasn't implemented.

**Solution:** Implement Pattern 2 (Recursive Operations) from Plan 06 - auto-generate these methods using metaprogramming.

---

#### 8. Form Structure and Initialization (~150 lines)

**Current Pattern:**
```python
def __init__(self, ...):
    # ... 150 lines of initialization logic
    # - Parameter extraction
    # - Service initialization
    # - Signal connections
    # - Cross-window registration
    # - Callback registration
```

**Problem:** Massive __init__ method doing too much. Should delegate to builder or factory.

**Solution:** Create `ParameterFormManagerBuilder` that handles all initialization logic.

---

### Proposed Abstraction Strategy

#### Phase 1: Service Extraction (~400 lines saved)

Create service classes to handle low-level operations:

1. **WidgetUpdateService** (~100 lines)
   - `update_widget_value(widget, value, param_name, skip_context_behavior)`
   - `_execute_with_signal_blocking(widget, operation)`
   - `_dispatch_widget_update(widget, value)`
   - `_apply_context_behavior(widget, value, param_name)`

2. **PlaceholderRefreshService** (~150 lines)
   - `refresh_with_live_context(manager)`
   - `refresh_all_placeholders(manager, live_context)`
   - `collect_live_context_from_other_windows(manager)`
   - `find_live_values_for_type(target_type, live_context)`
   - `reconstruct_nested_dataclasses(values_dict, template_instance)`

3. **EnabledFieldStylingService** (~150 lines)
   - `apply_initial_enabled_styling(manager)`
   - `refresh_enabled_styling(manager)`
   - `on_enabled_field_changed(manager, param_name, value)`

#### Phase 2: Orchestrator Extraction (~300 lines saved)

Create orchestrator classes to handle complex workflows:

1. **FormBuildOrchestrator** (~150 lines)
   - `build_form(manager, form_structure)`
   - `_build_async(manager, form_structure, content_layout)`
   - `_build_sync(manager, form_structure, content_layout)`
   - `_on_async_complete(manager)`

2. **CrossWindowUpdateCoordinator** (~150 lines)
   - `emit_cross_window_change(manager, param_name, value)`
   - `on_cross_window_context_changed(manager, field_path, new_value, editing_object, context_object)`
   - `is_affected_by_context_change(manager, editing_object, context_object)`
   - `schedule_cross_window_refresh(manager)`

#### Phase 3: Builder Pattern for Complex Widgets (~200 lines saved)

1. **OptionalDataclassWidgetBuilder** (~180 lines)
   - `build(param_info) -> QWidget`
   - `_create_title_widget(param_info) -> QWidget`
   - `_create_checkbox(param_info) -> QCheckBox`
   - `_create_nested_form(param_info) -> QWidget`
   - `_connect_checkbox_logic(checkbox, nested_form, param_info)`

#### Phase 4: Metaprogramming for Recursive Operations (~100 lines saved)

Implement Pattern 2 from Plan 06:
- Auto-generate `_apply_to_nested_managers`, `_collect_from_nested_managers`, `_find_nested_manager_by_field_id`

#### Phase 5: Initialization Builder (~150 lines saved)

1. **ParameterFormManagerBuilder** (~150 lines)
   - `build(object_instance, field_id, ...) -> ParameterFormManager`
   - `_extract_parameters(object_instance)`
   - `_initialize_services()`
   - `_connect_signals()`
   - `_register_cross_window_updates()`

---

### Expected Impact

| Phase | Lines Saved | Cumulative Reduction |
|-------|-------------|---------------------|
| Current State | 320 | 12% (2668 → 2348) |
| Phase 1: Service Extraction | 400 | 27% (2348 → 1948) |
| Phase 2: Orchestrator Extraction | 300 | 38% (1948 → 1648) |
| Phase 3: Builder Pattern | 200 | 46% (1648 → 1448) |
| Phase 4: Metaprogramming | 100 | 50% (1448 → 1348) |
| Phase 5: Initialization Builder | 150 | 56% (1348 → 1198) |
| **Additional cleanup** | 400 | **70% (1198 → 800)** |

### Implementation Priority

1. **Phase 1: Service Extraction** (highest impact, lowest risk)
2. **Phase 4: Metaprogramming** (Pattern 2 from Plan 06 - already designed)
3. **Phase 2: Orchestrator Extraction** (medium impact, medium risk)
4. **Phase 3: Builder Pattern** (medium impact, low risk)
5. **Phase 5: Initialization Builder** (lowest priority - can be done last)

---

## Implementation Status

### Phase 1: Service Extraction ✅ COMPLETE

**Created Service Classes:**

1. **WidgetUpdateService** (165 lines)
   - `openhcs/pyqt_gui/widgets/shared/services/widget_update_service.py`
   - Methods:
     - `update_widget_value(widget, value, param_name, skip_context_behavior, manager)`
     - `_execute_with_signal_blocking(widget, operation)`
     - `_dispatch_widget_update(widget, value)`
     - `_apply_context_behavior(widget, value, param_name, manager)`
     - `clear_widget_to_default_state(widget)`
     - `update_combo_box(widget, value)`
     - `update_checkbox_group(widget, value)`
     - `get_widget_value(widget)`

2. **PlaceholderRefreshService** (217 lines)
   - `openhcs/pyqt_gui/widgets/shared/services/placeholder_refresh_service.py`
   - Methods:
     - `refresh_with_live_context(manager, live_context)`
     - `refresh_all_placeholders(manager, live_context)`
     - `collect_live_context_from_other_windows(manager)`
     - `find_live_values_for_type(ctx_type, live_context)`
     - `reconstruct_nested_dataclasses(live_values, base_instance)`

3. **EnabledFieldStylingService** (325 lines)
   - `openhcs/pyqt_gui/widgets/shared/services/enabled_field_styling_service.py`
   - Methods:
     - `apply_initial_enabled_styling(manager)`
     - `refresh_enabled_styling(manager)`
     - `on_enabled_field_changed(manager, param_name, value)`
     - `_should_skip_optional_dataclass_styling(manager, log_prefix)`
     - `_get_direct_widgets(manager)`
     - `_is_any_ancestor_disabled(manager)`
     - `_apply_nested_config_styling(manager, resolved_value)`
     - `_apply_top_level_styling(manager, resolved_value, direct_widgets)`

**Methods Replaced in ParameterFormManager:**
- `update_widget_value()` → `_widget_update_service.update_widget_value()`
- `_clear_widget_to_default_state()` → `_widget_update_service.clear_widget_to_default_state()`
- `_update_combo_box()` → `_widget_update_service.update_combo_box()`
- `_update_checkbox_group()` → `_widget_update_service.update_checkbox_group()`
- `get_widget_value()` → `_widget_update_service.get_widget_value()`
- `_refresh_with_live_context()` → `_placeholder_refresh_service.refresh_with_live_context()`
- `_refresh_all_placeholders()` → `_placeholder_refresh_service.refresh_all_placeholders()`
- `_collect_live_context_from_other_windows()` → `_placeholder_refresh_service.collect_live_context_from_other_windows()`
- `_find_live_values_for_type()` → `_placeholder_refresh_service.find_live_values_for_type()`
- `_reconstruct_nested_dataclasses()` → `_placeholder_refresh_service.reconstruct_nested_dataclasses()`
- `_apply_initial_enabled_styling()` → `_enabled_styling_service.apply_initial_enabled_styling()`
- `_refresh_enabled_styling()` → `_enabled_styling_service.refresh_enabled_styling()`
- `_on_enabled_field_changed_universal()` → `_enabled_styling_service.on_enabled_field_changed()`
- `_is_any_ancestor_disabled()` → `_enabled_styling_service._is_any_ancestor_disabled()`

**Impact:**
- **Before:** 2348 lines
- **After:** 1831 lines
- **Saved:** 517 lines (22.0% reduction)
- **Cumulative reduction from original 2668:** 837 lines (31.4% reduction)

