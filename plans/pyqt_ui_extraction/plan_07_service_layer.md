# plan_07_service_layer.md
## Component: Service Layer

### Objective
Extract reusable services from `openhcs/pyqt_gui/widgets/shared/services/` into `pyqt_formgen/services/`. These provide cross-cutting concerns for form management.

### Plan

1. **Extract SignalService** (`signal_service.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/services/signal_service.py`
   - Target: `pyqt_formgen/services/signal_service.py`
   - Features:
     - `block_signals()` context manager
     - `connect_all_signals()` for form wiring
     - `cross_window_registration()` context manager
   - Changes:
     - TYPE_CHECKING import of ParameterFormManager → use Protocol instead
   - Dependencies: Only PyQt6

2. **Extract WidgetService** (`widget_service.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/services/widget_service.py`
   - Target: `pyqt_formgen/services/widget_service.py`
   - Features:
     - Widget finding by name
     - Widget styling (dimming, read-only)
     - Widget value updates with signal blocking
   - Changes: None expected - already generic
   - Dependencies: Only PyQt6

3. **Extract ValueCollectionService** (`value_collection_service.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/services/value_collection_service.py`
   - Target: `pyqt_formgen/services/value_collection_service.py`
   - Features:
     - Collecting values from form widgets
     - Nested form traversal
   - Dependencies: protocols layer for ValueGettable

4. **Extract FlagContextManager** (`flag_context_manager.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/services/flag_context_manager.py`
   - Target: `pyqt_formgen/services/flag_context_manager.py`
   - Features:
     - Context manager for boolean flags
     - Prevents reentrant operations
   - Dependencies: None (pure Python)

5. **Extract FieldChangeDispatcher** (`field_change_dispatcher.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/services/field_change_dispatcher.py`
   - Target: `pyqt_formgen/services/field_change_dispatcher.py`
   - Features:
     - `FieldChangeEvent` dataclass
     - Dispatcher for field change events
   - Changes:
     - Review for ObjectState dependencies
   - Dependencies: May need ObjectState for state updates

6. **Update services/__init__.py**:
   ```python
   from .signal_service import SignalService
   from .widget_service import WidgetService
   from .value_collection_service import ValueCollectionService
   from .flag_context_manager import FlagContextManager
   from .field_change_dispatcher import FieldChangeDispatcher, FieldChangeEvent
   ```

7. **Delete original files from OpenHCS**:
   - Delete `openhcs/pyqt_gui/widgets/shared/services/signal_service.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/services/widget_service.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/services/value_collection_service.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/services/flag_context_manager.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/services/field_change_dispatcher.py`

8. **Update all imports in OpenHCS**:
   - Replace `from openhcs.pyqt_gui.widgets.shared.services.signal_service import SignalService`
   - With `from pyqt_formgen.services import SignalService`

9. **Write tests** in `tests/test_services.py`:
   - Test SignalService.block_signals context manager
   - Test WidgetService widget finding
   - Test FlagContextManager reentrant prevention

### Findings

**signal_service.py**: 
- Uses TYPE_CHECKING for ParameterFormManager reference
- Can use Protocol instead for decoupling

**widget_service.py**:
- Pure PyQt6 widget operations
- FULLY GENERIC

**Services NOT to extract** (OpenHCS-specific):
- `scope_color_service.py` - Provenance/scope coloring
- `scope_token_service.py` - Scope token management
- `zmq_execution_service.py` - ZMQ communication
- `enum_dispatch_service.py` - May be extractable, review needed

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

