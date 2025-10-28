# plan_01_widget_protocol_system.md
## Component: Widget Protocol System with ABC Contracts

### Objective
Eliminate duck typing from the UI layer by creating an explicit widget protocol system using ABCs and metaclass auto-registration, mirroring the elegant patterns from StorageBackendMeta and LibraryRegistryBase.

### Problem Analysis

**Current Duck Typing Smells:**
```python
# SMELL: Attribute-based dispatch without contracts
WIDGET_UPDATE_DISPATCH = [
    ('set_value', lambda w, v: w.set_value(v)),
    ('setValue', lambda w, v: w.setValue(v if v is not None else w.minimum())),
    ('setText', lambda w, v: v is not None and w.setText(str(v)) or (v is None and w.clear())),
]

# SMELL: hasattr checks everywhere
if hasattr(widget, 'setRange'):
    widget.setRange(min, max)

# SMELL: Method presence testing
strategy = next(
    (strategy for method_name, strategy in PLACEHOLDER_STRATEGIES.items()
     if hasattr(widget, method_name)),
    lambda w, t: w.setToolTip(t) if hasattr(w, 'setToolTip') else None
)
```

**Why This Is Architectural Debt:**
1. No explicit contracts - relies on "if it quacks like a duck"
2. Silent failures - `if hasattr` hides missing implementations
3. Undiscoverable - can't find all widgets that implement a protocol
4. No compile-time safety - typos in method names fail at runtime
5. Violates OpenHCS fail-loud principle

### Elegant Pattern to Emulate: StorageBackendMeta

**From `openhcs/io/backend_registry.py`:**
```python
class StorageBackendMeta(ABCMeta):
    """Metaclass for automatic registration of storage backends."""
    
    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)
        
        # Only register concrete implementations
        if not getattr(new_class, '__abstractmethods__', None):
            backend_type = getattr(new_class, '_backend_type', None)
            if backend_type is None:
                return new_class
            
            # Auto-register in STORAGE_BACKENDS
            STORAGE_BACKENDS[backend_type] = new_class
            logger.debug(f"Auto-registered {name} as '{backend_type}' backend")
        
        return new_class
```

**Key Principles:**
- Metaclass auto-registration (zero boilerplate)
- Explicit type attribute (`_backend_type`)
- Fail-loud if abstract methods not implemented
- Discoverable via registry

### Plan

#### 1. Create Widget Protocol ABCs

**File:** `openhcs/ui/shared/widget_protocols.py`

Define explicit contracts for widget capabilities:

```python
from abc import ABC, abstractmethod
from typing import Any, Protocol

class ValueGettable(ABC):
    """Widget that can return a value."""
    
    @abstractmethod
    def get_value(self) -> Any:
        """Get the current value from the widget."""
        pass

class ValueSettable(ABC):
    """Widget that can accept a value."""
    
    @abstractmethod
    def set_value(self, value: Any) -> None:
        """Set the widget's value."""
        pass

class PlaceholderCapable(ABC):
    """Widget that can display placeholder text."""
    
    @abstractmethod
    def set_placeholder(self, text: str) -> None:
        """Set placeholder text for the widget."""
        pass

class RangeConfigurable(ABC):
    """Widget that supports numeric range configuration."""
    
    @abstractmethod
    def configure_range(self, minimum: float, maximum: float) -> None:
        """Configure the valid range for numeric input."""
        pass

class EnumSelectable(ABC):
    """Widget that can select from enum values."""
    
    @abstractmethod
    def set_enum_options(self, enum_type: type) -> None:
        """Configure widget with enum options."""
        pass
    
    @abstractmethod
    def get_selected_enum(self) -> Any:
        """Get the currently selected enum value."""
        pass
```

#### 2. Create Widget Registry Metaclass

**File:** `openhcs/ui/shared/widget_registry.py`

Auto-registration system for widgets:

```python
from abc import ABCMeta
from typing import Dict, Type, Set
import logging

logger = logging.getLogger(__name__)

# Global registry of widget implementations
WIDGET_IMPLEMENTATIONS: Dict[str, Type] = {}

# Track which protocols each widget implements
WIDGET_CAPABILITIES: Dict[Type, Set[Type]] = {}

class WidgetMeta(ABCMeta):
    """
    Metaclass for automatic widget registration.
    
    Mirrors StorageBackendMeta pattern - widgets auto-register
    when their classes are defined.
    """
    
    def __new__(cls, name, bases, attrs):
        new_class = super().__new__(cls, name, bases, attrs)
        
        # Only register concrete implementations
        if not getattr(new_class, '__abstractmethods__', None):
            # Extract widget identifier
            widget_id = getattr(new_class, '_widget_id', None)
            
            if widget_id is None:
                logger.debug(f"Skipping registration for {name} - no _widget_id")
                return new_class
            
            # Auto-register
            WIDGET_IMPLEMENTATIONS[widget_id] = new_class
            
            # Track capabilities (which protocols this widget implements)
            capabilities = set()
            for base in new_class.__mro__:
                if base.__name__ in ['ValueGettable', 'ValueSettable', 
                                     'PlaceholderCapable', 'RangeConfigurable',
                                     'EnumSelectable']:
                    capabilities.add(base)
            
            WIDGET_CAPABILITIES[new_class] = capabilities
            
            logger.debug(f"Auto-registered {name} as '{widget_id}' with capabilities: "
                        f"{[c.__name__ for c in capabilities]}")
        
        return new_class
```

#### 3. Implement Protocol-Based Dispatch

**File:** `openhcs/ui/shared/widget_dispatcher.py`

Type-safe dispatch replacing duck typing:

```python
from typing import Any, Type
from .widget_protocols import (ValueGettable, ValueSettable, 
                               PlaceholderCapable, RangeConfigurable)

class WidgetDispatcher:
    """
    Protocol-based widget dispatch - NO DUCK TYPING.
    
    Replaces hasattr checks with explicit isinstance checks.
    Fails loud if widget doesn't implement required protocol.
    """
    
    @staticmethod
    def get_value(widget: Any) -> Any:
        """Get value from widget using explicit protocol check."""
        if not isinstance(widget, ValueGettable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement ValueGettable protocol. "
                f"Add ValueGettable to widget's base classes."
            )
        return widget.get_value()
    
    @staticmethod
    def set_value(widget: Any, value: Any) -> None:
        """Set value on widget using explicit protocol check."""
        if not isinstance(widget, ValueSettable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement ValueSettable protocol. "
                f"Add ValueSettable to widget's base classes."
            )
        widget.set_value(value)
    
    @staticmethod
    def set_placeholder(widget: Any, text: str) -> None:
        """Set placeholder using explicit protocol check."""
        if not isinstance(widget, PlaceholderCapable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement PlaceholderCapable protocol. "
                f"Add PlaceholderCapable to widget's base classes."
            )
        widget.set_placeholder(text)
    
    @staticmethod
    def configure_range(widget: Any, minimum: float, maximum: float) -> None:
        """Configure range using explicit protocol check."""
        if not isinstance(widget, RangeConfigurable):
            raise TypeError(
                f"Widget {type(widget).__name__} does not implement RangeConfigurable protocol. "
                f"Add RangeConfigurable to widget's base classes."
            )
        widget.configure_range(minimum, maximum)
```

### Findings

**Existing Elegant Patterns to Emulate:**

1. **StorageBackendMeta** (`openhcs/io/backend_registry.py`):
   - Metaclass auto-registration
   - `_backend_type` attribute for identification
   - `STORAGE_BACKENDS` global registry
   - Fail-loud on missing abstract methods

2. **MemoryType Enum** (`openhcs/constants/constants.py`):
   - Enum-driven dispatch via `.converter` property
   - Auto-generated methods using metaprogramming
   - Type-safe conversion without duck typing

3. **LibraryRegistryBase** (`openhcs/processing/backends/lib_registry/unified_registry.py`):
   - ABC with enforced abstract attributes (`MODULES_TO_SCAN`, `MEMORY_TYPE`)
   - ProcessingContract enum for polymorphic dispatch
   - Fail-loud if implementations don't declare required attributes

**Current Duck Typing Locations:**

1. `WIDGET_UPDATE_DISPATCH` - attribute-based dispatch table
2. `WIDGET_GET_DISPATCH` - method presence testing
3. `PLACEHOLDER_STRATEGIES` - hasattr fallback chains
4. `CONFIGURATION_REGISTRY` - hasattr checks for setRange/setDecimals
5. `PyQt6WidgetEnhancer.apply_placeholder_text` - hasattr fallback

### Implementation Draft

(Code will be written after smell loop approval)

