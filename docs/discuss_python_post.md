TITLE: Semantic Axes Beyond (B, S): Why type() Needs Extension

---

**TL;DR:** `type()` today defines only (B, S) as semantic axes. This proposes an opt-in `axes={...}` metadata parameter to make axis semantics first-class, introspectable, inheritance-stable, and metaclass-free. Legacy classes stay keyed on (B, S); classes that opt into axes can be keyed on (B, S, axes) by frameworks/tools that choose to, while core CPython behavior remains (B, S).

Per Guido van Rossum's suggestion (personal email, Jan 6, 2026), posting this to the Typing topic for review by folks with deep Python typing context.

An **axis** is an orthogonal semantic coordinate of a type. Python's `type(name, bases, namespace)` has two semantic axes:

- **B** (`__bases__`): inheritance hierarchy, MRO
- **S** (`__dict__`): attributes and methods

You can view `type()` as `type(N, B, S)`, but **N** is not an independent semantic axis. The name is a slot on the type object set by `type.__new__()` from its first argument—it's metadata about the class, not a semantic coordinate. Two classes with identical (B, S) would be observationally equivalent; any difference in `__name__` is cosmetic (for repr/debugging), not semantic. The effective axis set is (B, S); N adds no independent information that affects type identity or behavior.

This maps directly to typing disciplines:

- **Structural typing** (Protocol): checks only S. Does the namespace have the right shape?
- **Nominal typing**: checks B via MRO. Is A in the inheritance chain?

---

**The Problem: Frameworks Need More Axes**

In OpenHCS (a microscopy automation framework), we need axes that `type()` doesn't provide.

*Hierarchical scope*: where does this type participate in a containment tree?

    # Current workaround: external registration
    class MyStep(Step):
        pass
    ObjectStateRegistry.register(MyStep, scope_id="/pipeline/step_0")

*Registry membership*: which registries should auto-discover this type?

    # Current workaround: metaclass reads magic attribute
    class MicroscopeHandler(ABC, metaclass=AutoRegisterMeta):
        _registry_config = RegistryConfig(
            registry_dict=MICROSCOPE_HANDLERS,
            key_attribute='FORMAT_NAME',
            skip_if_no_key=True,
        )
        FORMAT_NAME: Optional[str] = None

    class ImageXpressHandler(MicroscopeHandler):
        FORMAT_NAME = 'imagexpress'  # metaclass picks this up

This works, but:

1. Requires per-framework metaclass machinery
2. Scatters axis info across class body and external calls
3. Not uniformly introspectable
4. Collides with real methods: `scope()` vs `__scope__` are indistinguishable to a shape-only checker

---

**The Workaround Pattern**

The common workaround is packing extra axes into S (the namespace):

    class MyStep(Step):
        __scope__ = "/pipeline/step_0"      # H axis packed into S
        __registry__ = "step_handlers"       # R axis packed into S
        FORMAT_NAME = "custom"               # Another axis packed into S

This is analogous to a language where functions only take 1 parameter. You can pack multiple values into a tuple, but you're working around the limitation. Nominal typing (B, S) is like having 2 parameters—better, but still a fixed limit.

---

**Proposed Extension**

    # Axes parameter to **type()** (no grammar change)
    MyStep = type("MyStep", (Step,), {"process": fn},
                  axes={"scope": "/pipeline/step_0", "registry": STEP_REGISTRY})

    MyStep.__axes__  # {"scope": "/pipeline/step_0", "registry": ...}

This code shows the pure runtime API; no grammar changes. It would make framework metadata:

- First-class, not encoded in namespace attributes
- Uniformly introspectable via `__axes__` or `__<name>__`
- Decoupled from metaclass boilerplate
- Inheritance semantics: axes are inherited and can be overridden per key (already in the prototype); unspecified keys simply inherit defaults
- Fully opt-in: existing classes keep current `type()` semantics; the extended form applies only when explicitly requested
- Class-statement syntax already works: `class Foo(Base, axes={...})` is valid today via `__init_subclass__`—no grammar changes needed (see prototype section)
- Why not just metaclasses? Metaclasses can stash metadata, but every framework invents its own dunder names; a uniform `__axes__` surface + helper (e.g., `get_axes(cls)`) makes detection, tooling, and interop predictable.

**Identity rule (important):** If no axes are supplied, core equality/issubclass/isinstance caches remain keyed on (B, S). If axes are present, frameworks/tools MAY treat the class as keyed on (B, S, axes), but CPython's built-ins stay on (B, S) for compatibility. Axes are framework-level metadata, not core type identity.

**What about the `name` parameter?** The first argument to `type(name, bases, ns)` remains for backwards compatibility, debugging, and `repr()`. It's not a semantic axis—two classes with identical (B, S) are observationally equivalent regardless of their `__name__`. The name is cosmetic metadata, like a variable name.

**Public API surface (proposed)**
- `__axes__` : `Mapping[str, Any]` (wrapped in `MappingProxyType`), optional `__axes_enabled__ = True` marker.
- `__<axis>__` convenience attributes for keys present in `__axes__`.
- `get_axes(cls)` helper for unified introspection (prototype supplies one).
- Construction: `axes_type(...)` / `with_axes` decorator (opt-in); native `type()` unchanged except for the new `axes` kwarg.
- Inheritance/precedence: per-key MRO, leftmost wins unless subclass overrides; no post-definition mutation.
- Typing hook: optional schema via `TypedDict` or `HasAxes` protocol; schema is a hint, not a constraint.
- Standard schema (optional): a tiny `StdAxes` (e.g., scope, registry) could be provided for tooling demos; otherwise frameworks define their own.

**On misuse / “dumping ground” concerns**
- Python already allows arbitrary class metadata via attributes, decorators, and metaclasses; `__axes__` does not introduce a new category, it gives that metadata a principled home.
- Axes are explicitly non-behavioral and ignored by core dispatch and identity; if a framework doesn't consume a key, the failure mode is benign (it's ignored).
- By separating type-level metadata from behavioral attributes, axes reduce accidental complexity compared to hiding metadata in the namespace or metaclass logic.

---

**Why This Matters for Typing**

I've been formalizing axis selection for typing disciplines. The short version:

*For any fixed axis set A, there exists a domain requiring an axis not in A.*

Fixed axes are formally shown incomplete (see paper) for some use case. This is why frameworks keep inventing ad-hoc ways to attach metadata. They need axes that `type()` doesn't provide.

When you pack axes into S, you're encoding them in the namespace. A type checker that only sees S can't distinguish between:

- A real method `scope()`
- A metadata attribute `__scope__`
- A registration key `FORMAT_NAME`

They're all just namespace entries. The semantic distinction is lost.

A parametric extension would let the axis set grow with domain needs, making the axes first-class and introspectable rather than smuggled through namespace conventions.

---

**Why Python Specifically?**

In a companion paper, I prove that achieving Single Source of Truth (SSOT) for *structural facts* (class existence, method signatures, type relationships) requires two language features:

1. **Definition-time hooks**: Code that executes when a class is *defined*, not when it's *used* (Python has `__init_subclass__`, metaclasses, decorators)
2. **Introspectable derivation**: The ability to query what was derived and from what (Python has `__subclasses__()`, `__mro__`, etc.)

Among mainstream languages (top-10 TIOBE, consistent 5+ year presence), **Python is uniquely well-suited because it alone combines definition-time hooks and introspectable derivation in one object model**. Java, C++, Go, Rust, TypeScript, etc. lack definition-time hooks—their class declarations are static, not executable.

This means Python is uniquely positioned to support first-class semantic axes. Adding parametric axes to `type()` would make Python the first mainstream language to explicitly support domain-extensible type identity—rather than forcing frameworks to encode it through workarounds.

(SSOT paper with Lean proofs: https://zenodo.org/records/18177320)

---

**Working Prototype**

I have a working Python prototype that demonstrates this pattern:

    from parametric_axes import axes_type, with_axes

    # Factory function (mimics proposed type() extension)
    MyStep = axes_type("MyStep", (Step,), {},
                       scope="/pipeline/step_0",
                       registry=STEP_REGISTRY)

    MyStep.__axes__   # {"scope": "/pipeline/step_0", "registry": ...}
    MyStep.__scope__  # "/pipeline/step_0"

    # Decorator syntax (current workaround)
    @with_axes(scope="/decorated", priority=10)
    class DecoratedStep(Step):
        pass

Features demonstrated:

- `axes_type()` factory mimicking proposed `type(name, bases, ns, **axes)` (opt-in runtime API)
- `__axes__` dict for uniform introspection
- `__<name>__` convenience attributes (e.g., `__scope__`)
- Static typing hook (optional): frameworks that want static validation can expose an axis schema via `TypedDict` (or similar); unknown axes remain permitted and NotRequired by default
- Inheritance preserved (`issubclass` works correctly)
- Framework can introspect and register uniformly

Static vs runtime clarity:
- Axis schemas are tooling hints only
- Each framework defines the axes it cares about; extra axes are ignored unless the framework opts in to validate them
- This mirrors functions accepting `**kwargs`: validation is optional and domain-specific
- Axes are runtime metadata, not type identity; they sit alongside, not inside, the member typing space
- Axes are never behavioral: they don't change dispatch or field semantics; they're metadata only

Serialization:
- Axes are class metadata and should round-trip; the prototype includes them in `__reduce__`/copy so they survive pickling and reloads
- Cross-environment: when unpickling in an environment that doesn't know some axes, they remain present in `__axes__`; frameworks that don't declare those keys simply ignore them

Conflict/merging rules:
- Multiple inheritance: per-key resolution follows Python MRO linearization; for each axis key, the first class in the MRO providing that key determines its value unless the subclass overrides it explicitly.
- Post-definition mutation: `__axes__` is treated as class metadata; overriding happens via subclassing, not mutation. In the prototype it is wrapped in `types.MappingProxyType` to discourage writes.
- Heterogeneous values: leftmost in MRO still wins even if value types differ; no automatic type reconciliation is attempted.

Tiny MI example (deterministic):

```python
# Demonstrates MRO-based per-key resolution for conflicting axes
# Class statement syntax works TODAY via __init_subclass__ (no grammar changes!)

class B(Step, axes={"scope": "b"}): ...
class C(Step, axes={"scope": "c"}): ...

class D(B, C):  # MRO: D, B, C, Step, object
    pass

D.__axes__["scope"] == "b"  # leftmost in MRO wins unless D overrides
```

**Note on syntax:** The `class Foo(Base, axes={...})` syntax already works in Python via `__init_subclass__`. When a base class defines `def __init_subclass__(cls, axes=None, **kwargs)`, subclasses can pass `axes=` as a keyword argument in the class statement. No grammar changes are required—this is a pure library pattern.

Static typing example (tools can see axes):

```python
# Demonstrates optional static schema for checkers; unknown axes still allowed
from typing import TypedDict, NotRequired

class StepAxes(TypedDict, total=False):
    scope: str
    registry: str
    priority: NotRequired[int]

MyStep = axes_type("MyStep", (Step,), {}, scope="/pipeline/step_0", registry=STEP_REGISTRY)
reveal_type(MyStep.__axes__)  # mypy/pyright: StepAxes
```

Opt-in marker and collision avoidance:
- Presence of `__axes__` (and optional `__axes_enabled__ = True`) distinguishes extended classes; ordinary classes are unchanged.
- Axis keys live in `__axes__` / `__<name>__`, keeping them out of normal method/attribute space and avoiding collisions with user-defined members.
- Metaclasses alone can store metadata, but a uniform `__axes__` surface (and a helper like `get_axes(cls)`) avoids bespoke per-framework attributes and keeps detection standardized.

Typing interaction (explicit):
- Axes are runtime metadata; they do not participate in `typing.get_origin/get_args` and do not affect type identity or variance.
- Static tools MAY read `__axes__`/schema to validate known keys; absence or unknown keys is not a type error unless a framework opts into validation.
- Axes are orthogonal to `__annotations__`: annotations describe member types; axes describe structural metadata of the type itself.
- A schema is just a TypedDict-like hint listing known axis keys for a framework; it is optional and does not constrain adding new axes.
- Static helper: a tiny protocol such as `class HasAxes(Protocol): __axes__: Mapping[str, Any]` can be shipped to keep type checkers happy without forcing them to know every axis key.
- Metaclass order: axes are resolved after metaclass `__new__` and before `__init__`, so metaclasses see them in the namespace but post-resolution is stable for subclasses.

The prototype is available at: https://github.com/trissim/ObjectState (MIT license). Happy to receive feedback or PRs.

---

**Formal Results (proof links)**

I have Lean 4 proofs (~15k lines total, no `sorry`) formalizing two related results:

**Paper 1 — Typing Discipline Selection** (~6k lines):
1. The required axis set is computable from domain requirements, not chosen from a menu
2. Any fixed axis set is incomplete for some domain
3. When B exists (inheritance), nominal typing is forced; structural is incorrect

Link: https://zenodo.org/records/18173678 (Section 2.6: axis-parametric framework, Section 4.4: type() extension)

**Paper 2 — SSOT Language Requirements** (~9k lines, 541 theorems):
1. DOF = 1 (Single Source of Truth) is the unique coherent representation
2. SSOT for structural facts requires definition-time hooks AND introspection
3. Python is the only mainstream language with both features
4. Language capability claims derived from formalized operational semantics

Link: https://zenodo.org/records/18177320

---

**Discussion Questions**

1. Is extending `type()` the right approach per the SSOT paper, or should this be handled by a new construct?
2. Should Python define a tiny optional standard axis schema (e.g., scope, registry), or leave all schemas to frameworks?
3. How should static type checkers surface `__axes__`? (Runtime-only by default; opt-in schema when provided.)
4. Are there additional MRO/merge edge cases we should pin down beyond the per-key MRO rule?

I have a draft PEP if there's interest, but wanted to get feedback on the core idea first. The prototype is MIT-licensed and available for testing.

Happy to hear whether this direction aligns with typing's long-term goals for runtime introspection and SSOT.
