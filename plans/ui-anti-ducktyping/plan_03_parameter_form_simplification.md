# plan_03_parameter_form_simplification.md
## Component: Massive ParameterFormManager Simplification

### Objective
Simplify ParameterFormManager by 70%+ using the widget protocol system, eliminating all duck typing and reducing the 2654-line file to ~800 lines by leveraging the adapter pattern and explicit dispatch.

### Problem Analysis

**Current ParameterFormManager Issues:**

1. **Duck Typing Everywhere:**
   - `WIDGET_UPDATE_DISPATCH` - attribute-based fallback chains
   - `WIDGET_GET_DISPATCH` - method presence testing
   - `ALL_INPUT_WIDGET_TYPES` - hardcoded tuple of 11 widget types
   - `findChildren()` calls with explicit type lists

2. **Massive Complexity:**
   - 2654 lines total
   - Handles widget creation, value getting/setting, placeholder management
   - Nested manager coordination
   - Cross-window updates
   - Async widget creation
   - Enabled field styling

3. **No Clear Separation:**
   - Widget creation mixed with value management
   - Placeholder logic scattered throughout
   - Signal connection logic duplicated

**Elegant Pattern to Emulate: LibraryRegistryBase**

From `openhcs/processing/backends/lib_registry/unified_registry.py`:
```python
class LibraryRegistryBase(ABC):
    """
    Unified registry base class - eliminates ~70% code duplication.
    
    Key Benefits:
    - Eliminates ~1000+ lines of duplicated code
    - Enforces consistent patterns
    - Makes adding new libraries trivial (60-120 lines vs 350-400)
    - Centralizes bug fixes
    """
    
    # Abstract class attributes - enforced by ABC
    MODULES_TO_SCAN: List[str]
    MEMORY_TYPE: str
    FLOAT_DTYPE: Any
```

**Key Insight:** By extracting common patterns into a base class with enforced attributes, LibraryRegistryBase reduced registry implementations from 350-400 lines to 60-120 lines. We can do the same for ParameterFormManager.

### Plan

#### 1. Extract Widget Operations Service

**File:** `openhcs/ui/shared/widget_operations.py`

Centralize all widget operations using protocol-based dispatch:

```python
from typing import Any
from .widget_protocols import ValueGettable, ValueSettable, PlaceholderCapable
from .widget_dispatcher import WidgetDispatcher

class WidgetOperations:
    """
    Centralized widget operations using protocol-based dispatch.
    
    Replaces scattered duck typing with explicit protocol checks.
    Eliminates WIDGET_UPDATE_DISPATCH and WIDGET_GET_DISPATCH.
    """
    
    @staticmethod
    def get_value(widget: Any) -> Any:
        """Get value from any widget implementing ValueGettable."""
        return WidgetDispatcher.get_value(widget)
    
    @staticmethod
    def set_value(widget: Any, value: Any) -> None:
        """Set value on any widget implementing ValueSettable."""
        WidgetDispatcher.set_value(widget, value)
    
    @staticmethod
    def set_placeholder(widget: Any, text: str) -> None:
        """Set placeholder on any widget implementing PlaceholderCapable."""
        WidgetDispatcher.set_placeholder(widget, text)
    
    @staticmethod
    def get_all_value_widgets(container: Any) -> list:
        """
        Get all widgets that implement ValueGettable protocol.
        
        Replaces findChildren() with explicit type lists.
        Uses protocol checking instead of duck typing.
        """
        from .widget_registry import WIDGET_IMPLEMENTATIONS
        
        # Get all registered widget types
        widget_types = tuple(WIDGET_IMPLEMENTATIONS.values())
        
        # Find all children of registered types
        all_widgets = container.findChildren(widget_types)
        
        # Filter to only those implementing ValueGettable
        return [w for w in all_widgets if isinstance(w, ValueGettable)]
```

#### 2. Simplify ParameterFormManager

**File:** `openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`

Massive simplification using widget protocols:

```python
# BEFORE: Duck typing dispatch tables (DELETED)
# WIDGET_UPDATE_DISPATCH = [...]
# WIDGET_GET_DISPATCH = [...]
# ALL_INPUT_WIDGET_TYPES = (...)

# AFTER: Protocol-based operations
from openhcs.ui.shared.widget_operations import WidgetOperations

class ParameterFormManager(QWidget):
    """
    SIMPLIFIED: Parameter form manager using widget protocols.
    
    Reduced from 2654 lines to ~800 lines by:
    1. Using WidgetFactory for creation (no duck typing)
    2. Using WidgetOperations for get/set (no dispatch tables)
    3. Using protocol-based widget discovery (no hardcoded type lists)
    """
    
    def __init__(self, object_instance: Any, field_id: str, parent=None, 
                 context_obj=None, **kwargs):
        super().__init__(parent)
        
        # Core setup (unchanged)
        self.object_instance = object_instance
        self.field_id = field_id
        self.context_obj = context_obj
        
        # Widget factory using explicit type dispatch
        from openhcs.ui.shared.widget_factory import WidgetFactory
        self._widget_factory = WidgetFactory()
        
        # Widget operations using protocol dispatch
        self._widget_ops = WidgetOperations()
        
        # Build UI
        self.setup_ui()
    
    def create_widget(self, param_name: str, param_type: Type, 
                     current_value: Any) -> Any:
        """
        SIMPLIFIED: Create widget using factory (no duck typing).
        
        BEFORE: 50+ lines of if/elif chains and hasattr checks
        AFTER: Single factory call
        """
        widget = self._widget_factory.create_widget(param_type, param_name)
        
        # Set initial value using protocol
        if current_value is not None:
            self._widget_ops.set_value(widget, current_value)
        
        return widget
    
    def get_current_values(self) -> Dict[str, Any]:
        """
        SIMPLIFIED: Get values using protocol dispatch.
        
        BEFORE: Duck typing dispatch table iteration
        AFTER: Direct protocol call
        """
        values = {}
        for param_name, widget in self.widgets.items():
            try:
                values[param_name] = self._widget_ops.get_value(widget)
            except TypeError as e:
                # Widget doesn't implement ValueGettable - fail loud
                raise TypeError(
                    f"Widget for parameter '{param_name}' does not implement "
                    f"ValueGettable protocol: {e}"
                )
        return values
    
    def update_parameter(self, param_name: str, value: Any) -> None:
        """
        SIMPLIFIED: Update parameter using protocol dispatch.
        
        BEFORE: Duck typing dispatch table iteration
        AFTER: Direct protocol call
        """
        widget = self.widgets.get(param_name)
        if widget is None:
            raise KeyError(f"No widget found for parameter '{param_name}'")
        
        try:
            self._widget_ops.set_value(widget, value)
        except TypeError as e:
            # Widget doesn't implement ValueSettable - fail loud
            raise TypeError(
                f"Widget for parameter '{param_name}' does not implement "
                f"ValueSettable protocol: {e}"
            )
    
    def _refresh_all_placeholders(self) -> None:
        """
        SIMPLIFIED: Refresh placeholders using protocol dispatch.
        
        BEFORE: hasattr checks and fallback chains
        AFTER: Direct protocol call with fail-loud
        """
        for param_name, widget in self.widgets.items():
            # Resolve placeholder text from context
            placeholder_text = self._resolve_placeholder(param_name)
            
            if placeholder_text:
                try:
                    self._widget_ops.set_placeholder(widget, placeholder_text)
                except TypeError:
                    # Widget doesn't support placeholders - skip silently
                    # (This is acceptable - not all widgets need placeholders)
                    pass
    
    def _apply_enabled_styling(self) -> None:
        """
        SIMPLIFIED: Apply styling using protocol-based widget discovery.
        
        BEFORE: findChildren() with hardcoded ALL_INPUT_WIDGET_TYPES tuple
        AFTER: Protocol-based discovery
        """
        # Get all widgets that can have values
        value_widgets = self._widget_ops.get_all_value_widgets(self)
        
        # Apply dimming based on enabled state
        enabled = self._resolve_enabled_value()
        for widget in value_widgets:
            self._apply_dimming(widget, not enabled)
```

#### 3. Delete Obsolete Code

**Files to Modify:**

1. **`openhcs/pyqt_gui/widgets/shared/parameter_form_manager.py`:**
   - DELETE: `WIDGET_UPDATE_DISPATCH` (lines 19-26)
   - DELETE: `WIDGET_GET_DISPATCH` (lines 28-35)
   - DELETE: `ALL_INPUT_WIDGET_TYPES` (lines 58-62)
   - DELETE: Duck typing helper methods
   - REPLACE: All dispatch table iterations with `WidgetOperations` calls

2. **`openhcs/pyqt_gui/widgets/shared/widget_strategies.py`:**
   - DELETE: `PLACEHOLDER_STRATEGIES` dict (hasattr-based)
   - DELETE: `CONFIGURATION_REGISTRY` (hasattr-based)
   - REPLACE: With protocol-based implementations

3. **`openhcs/ui/shared/parameter_type_utils.py`:**
   - DELETE: `has_dataclass_fields()` - use `isinstance()` instead
   - DELETE: `has_resolve_field_value()` - use `isinstance()` instead
   - DELETE: `extract_value_attribute()` - use explicit enum handling

### Findings

**Code Reduction Estimate:**

| Component | Before | After | Reduction |
|-----------|--------|-------|-----------|
| ParameterFormManager | 2654 lines | ~800 lines | 70% |
| Widget dispatch tables | ~100 lines | 0 lines | 100% |
| Duck typing helpers | ~200 lines | 0 lines | 100% |
| Widget creation logic | ~300 lines | ~50 lines | 83% |
| **TOTAL** | **~3254 lines** | **~850 lines** | **74%** |

**Elegant Patterns Applied:**

1. **From LibraryRegistryBase:**
   - Centralized operations in base class
   - Enforced protocols via ABC
   - Eliminated duplicated dispatch logic

2. **From MemoryTypeConverter:**
   - Adapter pattern for inconsistent APIs
   - Explicit protocol implementation
   - Type-safe dispatch

3. **From StorageBackendMeta:**
   - Auto-registration via metaclass
   - Discoverable via registry
   - Fail-loud on missing implementations

**Benefits:**

1. **Architectural Clarity:**
   - Explicit contracts (ABCs) instead of implicit duck typing
   - Discoverable implementations (registry) instead of scattered code
   - Fail-loud errors instead of silent fallbacks

2. **Maintainability:**
   - Single source of truth for widget operations
   - Adding new widget types: implement protocols + set `_widget_id`
   - No more hunting for hasattr checks

3. **Type Safety:**
   - IDE autocomplete works (knows widget implements protocol)
   - Refactoring is safe (rename method = compiler error)
   - No runtime surprises from typos

### Implementation Draft

(Code will be written after smell loop approval)

