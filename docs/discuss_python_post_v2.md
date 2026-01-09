TITLE: Semantic Axes Beyond (B, S): Why type() Needs Extension

---

**TL;DR:** `type()` defines only (B, S) as semantic axes. This proposes an opt-in `axes={...}` parameter to make framework metadata first-class and introspectable, without grammar changes. Legacy classes unchanged; opt-in classes get `__axes__`.

Per Guido van Rossum's suggestion (personal email, Jan 6, 2026), posting to Typing for review.

---

**The Problem**

Python's `type(name, bases, namespace)` has two semantic axes:
- **B** (`__bases__`): inheritance hierarchy
- **S** (`__dict__`): attributes and methods

Frameworks need more. In OpenHCS (microscopy automation), we need scope, registry membership, priority—none of which `type()` provides. The workaround is packing them into S:

```python
class MyStep(Step):
    __scope__ = "/pipeline/step_0"      # framework axis packed into namespace
    __registry__ = "step_handlers"       # another axis packed into namespace
```

This works, but:
1. Requires per-framework metaclass machinery
2. Not uniformly introspectable
3. A type checker can't distinguish `__scope__` (metadata) from `scope()` (method)

---

**Proposed Solution**

Add an opt-in `axes` parameter to `type()`:

```python
MyStep = type("MyStep", (Step,), {"process": fn},
              axes={"scope": "/pipeline/step_0", "registry": STEP_REGISTRY})

MyStep.__axes__  # {"scope": "/pipeline/step_0", "registry": ...}
```

Key properties:
- **Opt-in**: No axes = current behavior unchanged
- **No grammar change**: `class Foo(Base, axes={...})` works today via `__init_subclass__`
- **Inheritance**: Per-key MRO resolution, leftmost wins unless overridden
- **Not core identity**: CPython's `isinstance`/`issubclass` stay keyed on (B, S); axes are framework-level metadata

Why not just metaclasses? Metaclasses can stash metadata, but every framework invents its own dunders. A uniform `__axes__` surface makes detection, tooling, and interop predictable.

---

**Working Prototype**

I have a working implementation:

```python
from parametric_axes import axes_type, with_axes

MyStep = axes_type("MyStep", (Step,), {},
                   scope="/pipeline/step_0",
                   registry=STEP_REGISTRY)

MyStep.__axes__   # {"scope": "/pipeline/step_0", ...}
MyStep.__scope__  # convenience attribute
```

Features: inheritance works, `__axes__` is a `MappingProxyType`, optional `TypedDict` schema for static checkers.

Prototype: https://github.com/trissim/ObjectState (MIT)

---

**Typing Interaction**

- Axes are runtime metadata, orthogonal to `__annotations__`
- Static tools MAY read `__axes__` to validate known keys via optional schema
- Unknown axes are not type errors unless framework opts into validation
- Tiny protocol for checkers: `class HasAxes(Protocol): __axes__: Mapping[str, Any]`

---

**Discussion Questions**

1. Is extending `type()` the right approach, or should this be a new construct?
2. Should Python define a minimal standard schema (e.g., `scope`, `registry`), or leave all schemas to frameworks?
3. How should static checkers surface `__axes__`? (I propose: runtime-only by default, opt-in schema when provided)
4. Any MRO edge cases beyond per-key resolution we should pin down?

I have a draft PEP if there's interest. Happy to hear whether this aligns with typing's goals.

---

*Background: I've formalized why frameworks need extensible axes and why Python is uniquely suited for this. Happy to share the formal analysis if useful, but didn't want to bury the proposal in theory.*

