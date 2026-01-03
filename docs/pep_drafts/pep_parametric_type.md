# PEP Draft: Parametric Type Construction

**Status**: Draft  
**Author**: OpenHCS Team  
**Created**: 2026-01-03

## Abstract

This PEP proposes extending Python's `type()` constructor to support additional semantic axes beyond the current (Bases, Namespace) model. The extension enables framework authors to attach runtime metadata (scope, registry, hierarchy) at type-creation time rather than through ad-hoc metaclass machinery.

## Motivation

### The (B, S) Limitation

Python's `type(name, bases, namespace)` creates types with exactly two semantic axes:
- **B (Bases)**: The inheritance hierarchy (`__bases__`)
- **S (Namespace)**: The attribute dictionary (`__dict__`)

This is *complete* for static type identity but *incomplete* for runtime context systems that need:
- Hierarchical scope (where does this type participate in a containment hierarchy?)
- Registry membership (which registries should auto-discover this type?)
- Provenance tracking (which scope provided a given field value?)

### Current Workarounds

Frameworks like OpenHCS implement these axes manually:

```python
# Manual scope registration (H axis)
class MyStep(Step):
    pass
ObjectStateRegistry.register(MyStep, scope_id="/plate::step_0")

# Manual registry membership
class MyHandler(MicroscopeHandler):
    _microscope_type = "custom"  # triggers metaclass registration
```

This works but:
1. Requires metaclass machinery per-framework
2. Scatters axis information across class body and external calls
3. Cannot be introspected uniformly

## Specification

### Option A: Extend `type()` with `axes` parameter

```python
type(name, bases, namespace, /, *, axes=None)
```

Where `axes` is an optional mapping of axis names to values:

```python
MyConfig = type(
    "MyConfig",
    (BaseConfig,),
    {"field": 1},
    axes={
        "scope": "/plate::step_0",
        "registry": CONFIG_REGISTRY,
    }
)

# Accessible via new dunder
MyConfig.__axes__  # {"scope": "/plate::step_0", "registry": ...}
```

### Option B: New `type.create()` class method

```python
MyConfig = type.create(
    "MyConfig",
    bases=(BaseConfig,),
    namespace={"field": 1},
    scope="/plate::step_0",
    registry=CONFIG_REGISTRY,
)
```

### Option C: Axis Protocol

Define a protocol for axis providers:

```python
class AxisProvider(Protocol):
    def __axis_name__(self) -> str: ...
    def __axis_attach__(self, cls: type) -> None: ...
    def __axis_value__(self, cls: type) -> Any: ...

# Usage
scope_axis = ScopeAxis("/plate::step_0")
MyConfig = type("MyConfig", (Base,), {}, axes=[scope_axis])
```

## The Three-Axis Model

The extended model becomes **(B, S, H)**:

| Axis | Python Current | Proposed |
|------|----------------|----------|
| B (Bases) | `__bases__` | unchanged |
| S (Namespace) | `__dict__` | unchanged |
| H (Hierarchy) | manual | `__axes__["scope"]` |

**Key insight**: H is orthogonal to (B, S). A type's (B, S) is fixed at definition; its H varies at runtime based on where instances participate.

## Backward Compatibility

- `type(name, bases, ns)` continues to work unchanged
- `__axes__` defaults to `{}` for all existing types
- No changes to `isinstance()`, `issubclass()`, or MRO

## Implementation Notes

1. `__axes__` stored on type object (like `__dict__`)
2. Axes are *not* inherited (each type defines its own)
3. Metaclasses can populate axes in `__new__`
4. `typing.get_type_hints()` unaffected

## Open Questions

1. Should axes be mutable after type creation?
2. Should there be a standard set of axis names (scope, registry, version)?
3. How does this interact with `@dataclass` and other decorators?
4. Should `type.__axes__` be a `MappingProxyType` (immutable view)?

## References

- OpenHCS ObjectStateRegistry: scope-based type registration
- OpenHCS AutoRegisterMeta: registry-based type discovery
- "The Completeness of Nominal Typing" (paper1_typing_discipline)

