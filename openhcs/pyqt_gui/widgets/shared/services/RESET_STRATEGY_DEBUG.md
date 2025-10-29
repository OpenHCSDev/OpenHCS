# ResetStrategy Type-Driven Dispatch Debugging

## Problem Statement

We're trying to eliminate duck-typing smells in `parameter_reset_service.py` by using type-driven dispatch for determining reset strategies.

### Original Smell (FIXED)
```python
def _determine_strategy(self, manager, param_name: str) -> ResetStrategy:
    if self._is_function_parameter(manager, param_name):  # ❌ SMELL
        return ResetStrategy.FUNCTION_PARAM
    
    param_type = manager.parameter_types.get(param_name)
    if not param_type:  # ❌ SMELL
        return ResetStrategy.GENERIC_FIELD
    
    if ParameterTypeUtils.is_optional_dataclass(param_type):  # ❌ SMELL
        return ResetStrategy.OPTIONAL_DATACLASS
```

## Attempted Solutions

### Attempt 1: Enum with Lambda Values ❌ BROKEN
```python
class ResetStrategy(Enum):
    OPTIONAL_DATACLASS = lambda m, p: (pt := m.parameter_types.get(p)) and ParameterTypeUtils.is_optional_dataclass(pt)
    DIRECT_DATACLASS = lambda m, p: (pt := m.parameter_types.get(p)) and dc_module.is_dataclass(pt)
    GENERIC_FIELD = lambda m, p: True
```

**Result**: `Members: []` - Python's Enum doesn't recognize lambdas as valid enum values!

**Why it fails**: Enum uses special metaclass logic that only accepts certain types (strings, ints, tuples, etc.) as values. Functions/lambdas are NOT recognized.

### Attempt 2: Enum with Dataclass Values ❌ TOO MUCH BOILERPLATE
```python
@dataclass
class StrategyConfig:
    predicate: Callable[[Any, str], bool]

class ResetStrategy(Enum):
    OPTIONAL_DATACLASS = StrategyConfig(predicate=lambda m, p: ...)
```

**Result**: Works but adds unnecessary wrapper class.

### Attempt 3: Enum with Hardcoded Dict ❌ SMELL
```python
class ResetStrategy(Enum):
    OPTIONAL_DATACLASS = 1
    
    @property
    def predicate(self):
        return {
            ResetStrategy.OPTIONAL_DATACLASS: lambda m, p: ...,  # ❌ Hardcoded mapping
        }[self]
```

**Result**: Works but reintroduces hardcoded mappings we're trying to eliminate.

## Current State

We need a pattern that:
1. ✅ Eliminates cascading if-else type checks
2. ✅ Auto-registers predicates without hardcoded mappings
3. ✅ Allows adding new strategies without modifying existing code
4. ✅ Keeps predicates co-located with strategy definitions
5. ✅ Works with Python's type system (no broken Enums)

## Final Solution: Service-Level Registry Pattern ✅

**Key Insight**: Services and strategies are NOT the same thing!
- `ParameterResetService` is a SERVICE (auto-discovered by `ServiceRegistryMeta`)
- Reset handlers are INTERNAL implementation details of the service

Use a simple registry pattern within the service class:

```python
class ParameterResetService:
    """Service for resetting parameters with registry-based type dispatch."""

    # Registry: List[(predicate, handler_method_name)]
    # Predicates are checked in order, first match wins
    _RESET_REGISTRY: List[Tuple[Callable, str]] = [
        (lambda m, p: (pt := m.parameter_types.get(p)) and ParameterTypeUtils.is_optional_dataclass(pt), '_reset_optional_dataclass'),
        (lambda m, p: (pt := m.parameter_types.get(p)) and dataclasses.is_dataclass(pt), '_reset_direct_dataclass'),
        (lambda m, p: True, '_reset_generic_field'),  # Fallback
    ]

    def reset_parameter(self, manager, param_name: str) -> None:
        """Reset parameter using registry-based type dispatch."""
        for predicate, handler_name in self._RESET_REGISTRY:
            if predicate(manager, param_name):
                handler = getattr(self, handler_name)
                handler(manager, param_name)
                return
```

**Benefits**:
- ✅ No if-elif-else chains
- ✅ Easy to add new handlers (just add to registry)
- ✅ Predicates and handlers co-located in registry
- ✅ Service remains a simple class (auto-discovered by metaclass)
- ✅ No unnecessary ABC/strategy class hierarchy
- ✅ First-match-wins semantics (order matters)

**File size**: 191 lines (down from 268 lines with enum dispatch)

