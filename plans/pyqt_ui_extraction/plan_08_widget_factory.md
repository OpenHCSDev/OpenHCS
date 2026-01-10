# plan_08_widget_factory.md
## Component: Widget Factory Layer

### Objective
Extract the widget creation infrastructure from `openhcs/ui/shared/` into `pyqt_formgen/forms/`. This provides type-based widget instantiation.

### Plan

1. **Extract WidgetRegistry** (`widget_registry.py`):
   - Source: `openhcs/ui/shared/widget_registry.py`
   - Target: `pyqt_formgen/forms/widget_registry.py`
   - Features:
     - `WidgetMeta` metaclass for auto-registration
     - Type → Widget class mapping
     - Extensible registry pattern
   - Dependencies: protocols layer

2. **Extract WidgetFactory** (`widget_factory.py`):
   - Source: `openhcs/ui/shared/widget_factory.py`
   - Target: `pyqt_formgen/forms/widget_factory.py`
   - Features:
     - Create widgets from type annotations
     - Handle Optional, Union, Enum types
     - Integrate with magicgui for complex types
   - Dependencies: widget_registry, protocols

3. **Extract WidgetOperations** (`widget_operations.py`):
   - Source: `openhcs/ui/shared/widget_operations.py`
   - Target: `pyqt_formgen/forms/widget_operations.py`
   - Features:
     - Common widget operations (show/hide, enable/disable)
     - Layout manipulation utilities
   - Dependencies: Only PyQt6

4. **Extract WidgetCreationRegistry** (`widget_creation_registry.py`):
   - Source: `openhcs/ui/shared/widget_creation_registry.py`
   - Target: `pyqt_formgen/forms/widget_creation_registry.py`
   - Features:
     - `create_pyqt6_registry()` factory function
     - Default widget mappings
   - Dependencies: widget_registry, widget_factory

5. **Extract WidgetDispatcher** (`widget_dispatcher.py`):
   - Source: `openhcs/ui/shared/widget_dispatcher.py`
   - Target: `pyqt_formgen/forms/widget_dispatcher.py`
   - Features:
     - Route widget creation requests
     - Handle nested types
   - Dependencies: widget_factory

6. **Extract WidgetStrategies** (`widget_strategies.py`):
   - Source: `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`
   - Target: `pyqt_formgen/forms/widget_strategies.py`
   - Features:
     - magicgui integration
     - Type conversion utilities
   - Changes:
     - Update imports for local widgets
   - Dependencies: widgets layer, magicgui (optional)

7. **Update forms/__init__.py** (partial - more in plan 10):
   ```python
   from .widget_registry import WidgetRegistry, WidgetMeta
   from .widget_factory import WidgetFactory
   from .widget_operations import WidgetOperations
   ```

8. **Delete original files from OpenHCS**:
   - Delete `openhcs/ui/shared/widget_registry.py`
   - Delete `openhcs/ui/shared/widget_factory.py`
   - Delete `openhcs/ui/shared/widget_operations.py`
   - Delete `openhcs/ui/shared/widget_creation_registry.py`
   - Delete `openhcs/ui/shared/widget_dispatcher.py`
   - Delete `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`

9. **Update all imports in OpenHCS**:
   - Replace `from openhcs.ui.shared.widget_factory import WidgetFactory`
   - With `from pyqt_formgen.forms import WidgetFactory`

10. **Write tests** in `tests/test_widget_factory.py`:
   - Test widget creation from basic types (int, str, bool)
   - Test Optional type handling
   - Test Enum type handling

### Findings

**widget_registry.py**: Contains WidgetMeta metaclass for auto-registration
**widget_factory.py**: Core factory pattern for type → widget
**widget_operations.py**: Utility operations, likely pure PyQt6
**widget_creation_registry.py**: PyQt6-specific registry setup
**widget_dispatcher.py**: Routing logic
**widget_strategies.py**: 
  - Has OpenHCS imports for no_scroll_spinbox
  - Has magicgui dependency
  - Needs import updates

### Implementation Draft
<!-- Only write code here AFTER smell loop passes -->

