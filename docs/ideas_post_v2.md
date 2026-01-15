# Standardized Per-Key Class Metadata (`__axes__` or `__metadata__`)

## The Problem

Frameworks often need class-level metadata that isn't a method or attribute. Here's real code from OpenHCS (microscopy automation):

```python
class ImageXpressHandler(MicroscopeHandler):
    _microscope_type = 'imagexpress'    # registry key (framework metadata)
    _metadata_handler_class = None       # more framework metadata
    
    def microscope_type(self) -> str:    # actual method
        return 'imagexpress'
```

Looking at `__dict__`, you can't tell which of these are framework machinery vs actual class behavior. A metaclass reads `_microscope_type` for registration, but nothing distinguishes it from `microscope_type` the method.

Every framework invents its own convention: `_registry_`, `__scope__`, `FORMAT_NAME`, `_microscope_type`. Tooling can't find any of them without framework-specific knowledge.

## Current Workarounds

You can use `**kwargs` in class definitions and stash metadata somewhere:

```python
class MyClass(Base, registry="foo"):
    pass
```

But where does `registry="foo"` go? Each framework decides differently:
- Some use a metaclass to put it in `__dict__`
- Some use a descriptor
- Some use ChainMap in `__init_subclass__`

All solving the same problem, none interoperable.

## Proposed Solution

A standard attribute (`__axes__` or `__metadata__`, name negotiable) with per-key inheritance:

```python
class Base(axes={"priority": 1, "scope": "/base"}):
    pass

class Child(Base, axes={"scope": "/child"}):
    pass

Child.__axes__["scope"]     # "/child" (overridden)
Child.__axes__["priority"]  # 1 (inherited from Base)
```

The key difference from a plain `__metadata__` dict: each key inherits independently through the MRO. Override one, keep the rest.

With normal MRO on a whole dict, you'd lose `priority`:

```python
class Base:
    __metadata__ = {"priority": 1, "scope": "/base"}

class Child(Base):
    __metadata__ = {"scope": "/child"}

Child.__metadata__  # {"scope": "/child"} — priority is gone
```

## Properties

- **Opt-in**: Classes without `axes=` work exactly as today
- **No grammar change**: Can be implemented via metaclass/base class today; class-statement sugar could come later
- **Framework metadata, not identity**: `isinstance`/`issubclass` unchanged; axes are for framework machinery
- **Standard location**: Tooling can find metadata without framework-specific knowledge

## Working Prototype

I have a working implementation: [GitHub - trissim/ObjectState](https://github.com/trissim/ObjectState)

```python
from parametric_axes import axes_type

Handler = axes_type("Handler", (), {}, registry_key="imagexpress", priority=1)
Handler.__axes__  # {"registry_key": "imagexpress", "priority": 1}
```

## Why Standardize?

Python doesn't limit function parameters to 5 because most functions use fewer. It provides the general mechanism and lets usage follow.

The question is whether per-key inheritable metadata is common enough to warrant a standard surface. If yes, frameworks get interoperability and tooling gets a predictable place to look. If no, we continue with each framework inventing its own conventions.

## Open Questions

- Naming: `__axes__` vs `__metadata__` vs something else?
- Any MRO edge cases beyond per-key resolution?
- Interest in a draft PEP?

I have a formal analysis of why this pattern emerges in framework design, happy to share for those interested, but the proposal stands on the practical examples above.

