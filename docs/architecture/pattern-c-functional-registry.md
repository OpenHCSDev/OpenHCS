# Pattern C: Functional Registry

## Overview

**Pattern C** is used for simple **type-to-handler mappings** using dict-based registries with functional programming style. No classes, no state, just pure functions mapped to types.

## When to Use Pattern C

Use Functional Registry when:
- ✅ **Simple mappings**: Type → function/handler (no complex metadata)
- ✅ **No state needed**: Handlers are stateless functions
- ✅ **Functional style**: Prefer functions over classes
- ✅ **Dispatch pattern**: Need runtime type-based dispatch
- ✅ **Extensibility**: Easy to add new type mappings

**Examples in OpenHCS:**
- **Widget Creation**: Type → widget creator function
- **Widget Configuration**: Type → configuration function
- **Placeholder Strategies**: Widget type → placeholder applier function

## Architecture

### Core Pattern

```python
# Simple dict mapping types to functions
REGISTRY_NAME: Dict[Type, Callable] = {
    int: lambda widget: configure_int_widget(widget),
    float: lambda widget: configure_float_widget(widget),
    str: lambda widget: configure_str_widget(widget),
}

# Usage: Dispatch based on type
handler = REGISTRY_NAME.get(param_type)
if handler:
    handler(widget)
```

### No Classes Required

Unlike Pattern A (metaclass) and Pattern B (service), Pattern C uses **pure functions**:

```
┌─────────────────────────────────────────────────────────────┐
│                    Functional Registry                       │
│                                                              │
│  REGISTRY: Dict[Type, Callable] = {                         │
│      Type1: handler_func_1,                                 │
│      Type2: handler_func_2,                                 │
│      Type3: handler_func_3,                                 │
│  }                                                           │
│                                                              │
│  # Dispatch                                                  │
│  handler = REGISTRY.get(type)                               │
│  if handler:                                                 │
│      result = handler(*args, **kwargs)                      │
└─────────────────────────────────────────────────────────────┘
```

## Implementation Patterns

### 1. Widget Creation Registry

**Use Case**: Map Python types to widget creator functions

```python
# openhcs/pyqt_gui/widgets/shared/widget_strategies.py

WIDGET_REPLACEMENT_REGISTRY: Dict[Type, Callable] = {
    str: lambda current_value, **kwargs: create_string_fallback_widget(current_value=current_value),
    bool: lambda current_value, **kwargs: (
        lambda w: (w.set_value(current_value), w)[1]
    )(_create_none_aware_checkbox()),
    int: lambda current_value, **kwargs: (
        lambda w: (w.set_value(current_value), w)[1]
    )(_create_none_aware_int_widget()),
    float: lambda current_value, **kwargs: (
        lambda w: (w.setValue(float(current_value)), w)[1] if current_value is not None else w
    )(NoScrollDoubleSpinBox()),
    Path: lambda current_value, param_name, parameter_info, **kwargs:
        create_enhanced_path_widget(param_name, current_value, parameter_info),
}

# Usage
def create_widget(param_type: Type, current_value: Any, **kwargs) -> Widget:
    """Create widget using functional registry dispatch."""
    resolved_type = resolve_optional(param_type)
    
    # Check registry
    replacement_factory = WIDGET_REPLACEMENT_REGISTRY.get(resolved_type)
    
    if replacement_factory:
        widget = replacement_factory(
            current_value=current_value,
            param_name=kwargs.get('param_name'),
            parameter_info=kwargs.get('parameter_info')
        )
        return widget
    
    # Fallback
    return create_default_widget(current_value)
```

### 2. Configuration Registry

**Use Case**: Map types to configuration functions

```python
# openhcs/pyqt_gui/widgets/shared/widget_strategies.py

CONFIGURATION_REGISTRY: Dict[Type, Callable] = {
    int: lambda widget: widget.setRange(WidgetConfig.NUMERIC_RANGE_MIN, WidgetConfig.NUMERIC_RANGE_MAX)
        if hasattr(widget, 'setRange') else None,
    float: lambda widget: (
        widget.setRange(WidgetConfig.NUMERIC_RANGE_MIN, WidgetConfig.NUMERIC_RANGE_MAX)
        if hasattr(widget, 'setRange') else None,
        widget.setDecimals(WidgetConfig.FLOAT_PRECISION)
        if hasattr(widget, 'setDecimals') else None
    )[-1],
}

# Usage
def configure_widget(widget: Widget, param_type: Type) -> None:
    """Configure widget using functional dispatch."""
    configurator = CONFIGURATION_REGISTRY.get(param_type, lambda w: w)
    configurator(widget)
```

### 3. Strategy Registry

**Use Case**: Map widget types to strategy functions

```python
# openhcs/pyqt_gui/widgets/shared/widget_strategies.py

WIDGET_PLACEHOLDER_STRATEGIES: Dict[Type, Callable[[Any, str], None]] = {
    QCheckBox: _apply_checkbox_placeholder,
    QComboBox: _apply_combobox_placeholder,
    QSpinBox: _apply_spinbox_placeholder,
    QDoubleSpinBox: _apply_spinbox_placeholder,
    NoScrollSpinBox: _apply_spinbox_placeholder,
    NoScrollDoubleSpinBox: _apply_spinbox_placeholder,
    QLineEdit: _apply_lineedit_placeholder,
}

# Usage
def apply_placeholder(widget: Widget, placeholder_text: str) -> None:
    """Apply placeholder using declarative widget-strategy mapping."""
    widget_strategy = WIDGET_PLACEHOLDER_STRATEGIES.get(type(widget))
    if widget_strategy:
        return widget_strategy(widget, placeholder_text)
    
    # Fallback
    if hasattr(widget, 'setToolTip'):
        widget.setToolTip(placeholder_text)
```

### 4. Framework-Specific Registries

**Use Case**: Separate registries for different UI frameworks

```python
# openhcs/ui/shared/widget_creation_registry.py

def create_textual_registry():
    """Return Textual widget creator function."""
    from openhcs.textual_tui.widgets.shared.textual_widget_strategies import create_textual_widget
    return create_textual_widget


def create_pyqt6_registry():
    """Return PyQt6 widget creator function."""
    try:
        from openhcs.pyqt_gui.widgets.shared.widget_strategies import MagicGuiWidgetFactory
        factory = MagicGuiWidgetFactory()
        return factory.create_widget
    except ImportError:
        def fallback_creator(*args, **kwargs):
            raise ImportError("PyQt6 not available - install with pip install 'openhcs[gui]'")
        return fallback_creator

# Usage
widget_creator = create_pyqt6_registry()  # or create_textual_registry()
widget = widget_creator(param_name, param_type, current_value, widget_id)
```

## Key Features

### 1. Simple and Direct

No metaclasses, no abstract base classes, no services - just dicts and functions:

```python
# Define
REGISTRY = {Type1: func1, Type2: func2}

# Use
handler = REGISTRY.get(type)
if handler:
    result = handler(*args)
```

### 2. Easy to Extend

Adding new mappings is trivial:

```python
# Add new type mapping
WIDGET_REPLACEMENT_REGISTRY[MyCustomType] = lambda current_value, **kwargs: create_my_widget(current_value)
```

### 3. Dynamic Registration

Can register handlers at runtime:

```python
def _register_path_widget_strategy():
    """Register Path widget strategy dynamically to avoid circular imports."""
    try:
        from openhcs.pyqt_gui.widgets.enhanced_path_widget import EnhancedPathWidget
        WIDGET_PLACEHOLDER_STRATEGIES[EnhancedPathWidget] = _apply_path_widget_placeholder
    except ImportError:
        pass  # Path widget not available

# Register at module load time
_register_path_widget_strategy()
```

### 4. Fallback Strategies

Easy to provide fallbacks when no handler found:

```python
# With default
configurator = CONFIGURATION_REGISTRY.get(param_type, lambda w: w)
configurator(widget)

# With conditional fallback
widget_strategy = WIDGET_PLACEHOLDER_STRATEGIES.get(type(widget))
if widget_strategy:
    widget_strategy(widget, placeholder_text)
else:
    # Fallback logic
    if hasattr(widget, 'setToolTip'):
        widget.setToolTip(placeholder_text)
```

## Comparison with Other Patterns

| Aspect | Pattern A (Metaclass) | Pattern B (Service) | Pattern C (Functional) |
|--------|----------------------|---------------------|------------------------|
| **Complexity** | Medium (metaclass) | High (ABC + service) | Low (dict + functions) |
| **State** | Class-based | Class-based | Stateless functions |
| **Metadata** | Simple (key) | Rich (8+ fields) | None (just mapping) |
| **Registration** | Automatic (class def) | Discovery (introspection) | Manual (dict literal) |
| **Use Case** | Plugin classes | Many items per plugin | Type dispatch |
| **Extensibility** | Subclass + metaclass | Implement ABC | Add dict entry |

## Best Practices

### 1. Use Type Hints

Always type hint your registries:

```python
from typing import Dict, Type, Callable

WIDGET_REPLACEMENT_REGISTRY: Dict[Type, Callable] = {
    str: lambda current_value, **kwargs: create_string_widget(current_value),
    int: lambda current_value, **kwargs: create_int_widget(current_value),
}
```

### 2. Consistent Signatures

All handlers in a registry should have the same signature:

```python
# Good: Consistent signatures
CONFIGURATION_REGISTRY: Dict[Type, Callable[[Widget], None]] = {
    int: lambda widget: widget.setRange(-999999, 999999),
    float: lambda widget: widget.setDecimals(6),
}

# Bad: Inconsistent signatures
CONFIGURATION_REGISTRY = {
    int: lambda widget: widget.setRange(-999999, 999999),
    float: lambda widget, precision: widget.setDecimals(precision),  # Different signature!
}
```

### 3. Use Lambdas for Simple Cases

For simple handlers, lambdas are cleaner than named functions:

```python
# Good: Simple lambda
CONFIGURATION_REGISTRY = {
    int: lambda widget: widget.setRange(-999999, 999999),
}

# Overkill: Named function for simple case
def configure_int_widget(widget):
    widget.setRange(-999999, 999999)

CONFIGURATION_REGISTRY = {
    int: configure_int_widget,
}
```

### 4. Use Named Functions for Complex Cases

For complex handlers, use named functions for readability:

```python
def _apply_checkbox_placeholder(widget: QCheckBox, placeholder_text: str) -> None:
    """Apply placeholder to checkbox with interaction hint."""
    hint = PlaceholderConfig.INTERACTION_HINTS.get('checkbox', '')
    full_text = f"{PlaceholderConfig.PLACEHOLDER_PREFIX}{placeholder_text} ({hint})"
    widget.setToolTip(full_text)
    widget.setStyleSheet(PlaceholderConfig.PLACEHOLDER_STYLE)

WIDGET_PLACEHOLDER_STRATEGIES = {
    QCheckBox: _apply_checkbox_placeholder,
}
```

### 5. Provide Fallbacks

Always handle missing keys gracefully:

```python
# With default value
handler = REGISTRY.get(type, default_handler)
result = handler(*args)

# With conditional
handler = REGISTRY.get(type)
if handler:
    result = handler(*args)
else:
    result = fallback_logic(*args)
```

### 6. Dynamic Registration for Circular Imports

Use dynamic registration to avoid circular imports:

```python
def _register_widget_strategy():
    """Register widget strategy dynamically to avoid circular imports."""
    try:
        from openhcs.pyqt_gui.widgets.enhanced_path_widget import EnhancedPathWidget
        WIDGET_PLACEHOLDER_STRATEGIES[EnhancedPathWidget] = _apply_path_widget_placeholder
    except ImportError:
        pass

# Call at module load time
_register_widget_strategy()
```

## Examples in OpenHCS

### Widget Creation Registries

**Location**: `openhcs/pyqt_gui/widgets/shared/widget_strategies.py`

**Registries**:
- `WIDGET_REPLACEMENT_REGISTRY` - Type → widget creator
- `CONFIGURATION_REGISTRY` - Type → configurator
- `WIDGET_PLACEHOLDER_STRATEGIES` - Widget type → placeholder applier
- `PLACEHOLDER_STRATEGIES` - Method name → placeholder applier

### Framework-Specific Registries

**Location**: `openhcs/ui/shared/widget_creation_registry.py`

**Functions**:
- `create_textual_registry()` - Returns Textual widget creator
- `create_pyqt6_registry()` - Returns PyQt6 widget creator

## When NOT to Use Pattern C

Consider other patterns if:

- ❌ **Need automatic discovery**: Use Pattern A (metaclass) or Pattern B (service)
- ❌ **Complex metadata**: Use Pattern B (service-based)
- ❌ **Many items per plugin**: Use Pattern B (service-based)
- ❌ **Need caching**: Use Pattern B (service-based)
- ❌ **Plugin classes**: Use Pattern A (metaclass)

## Migration Guide

### From Pattern A to Pattern C

If your metaclass registry is just doing simple type dispatch:

```python
# Before: Pattern A (metaclass)
class HandlerMeta(ABCMeta):
    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)
        if not getattr(new_class, '__abstractmethods__', None):
            handler_type = getattr(new_class, '_handler_type', None)
            if handler_type:
                HANDLERS[handler_type] = new_class
        return new_class

# After: Pattern C (functional)
HANDLERS: Dict[str, Callable] = {
    'type1': create_type1_handler,
    'type2': create_type2_handler,
}
```

### From Hardcoded if/elif to Pattern C

```python
# Before: Hardcoded dispatch
def create_widget(param_type):
    if param_type == int:
        return create_int_widget()
    elif param_type == float:
        return create_float_widget()
    elif param_type == str:
        return create_str_widget()
    else:
        return create_default_widget()

# After: Pattern C (functional registry)
WIDGET_CREATORS = {
    int: create_int_widget,
    float: create_float_widget,
    str: create_str_widget,
}

def create_widget(param_type):
    creator = WIDGET_CREATORS.get(param_type, create_default_widget)
    return creator()
```

## See Also

- [Pattern A: Metaclass Auto-Registration](pattern-a-metaclass-registry.md)
- [Pattern B: Service-Based Registry](pattern-b-service-based-registry.md)
- [Pattern D: Manual Registration](pattern-d-manual-registration.md)
- [Registry Pattern Decision Tree](registry-framework.md#decision-tree)

