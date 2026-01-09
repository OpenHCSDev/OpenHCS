# PEP Draft: Runtime Type Identity

**Status**: Draft
**Author**: Tristan Simas
**Created**: 2026-01-06

## Abstract

> **If you wrote it, you should be able to ask about it.**

Python's static type system knows that `x` is a `list[int]`. But at runtime, that information is gone—`x` is just a `list`. This PEP proposes closing that gap: make runtime honor what you already wrote.

## The Gap

Python has two type systems that don't talk to each other:

```python
# What you write (static typing sees this):
x: list[int] = [1, 2, 3]

# What runtime sees:
type(x)  # list — the `int` is gone
isinstance(x, list[int])  # TypeError
```

The static type checker knows `x` is `list[int]`. The runtime only knows `list`. The information existed—it was just thrown away.

**This PEP says: stop throwing it away.**

---

## The Principle

Every use case below is the same problem:

| You write | Runtime sees | Lost |
|-----------|--------------|------|
| `list[int]` | `list` | The `int` |
| `dict[str, User]` | `dict` | The `str`, the `User` |
| `Handler[Database]` | `Handler` | The `Database` |

The pattern: **specificity at write-time, generality at runtime.**

You can't ask questions about information that was thrown away. So we stop throwing it away.

---

## The Proposal

**One mechanism:** Preserve type identity at runtime, opt-in.

### For Generics

```python
# Opt-in: call the parameterized type
x = list[int]([1, 2, 3])

# Now runtime knows:
type(x)                    # list[int]
type(x).__args__           # (int,)
isinstance(x, list[int])   # True
isinstance(x, list[str])   # False

# Backward compatible — annotation-only syntax unchanged:
y: list[int] = [1, 2, 3]
type(y)                    # list (still erased, as today)
```

**That's it.** If you want the type parameter preserved, construct with `list[int](...)`. If you don't care, use annotation syntax as today.

### For User-Defined Metadata

The same principle extends. If `__args__` holds the generic parameter, users should be able to add their own:

```python
# Today: manual, ad-hoc
class MyHandler(Handler):
    _registry = "handlers"  # Not discoverable uniformly

# Proposed: first-class
class MyHandler(Handler, registry="handlers"):
    pass

MyHandler.__registry__  # "handlers"
```

This isn't a separate feature—it's the same mechanism. `__args__` is one kind of identity metadata. `__registry__` is another. Both answer: "what exactly is this type?"

---

## Why This Is One Thing, Not Two

People might say: "Reified generics and custom metadata are different features."

They're not. Watch:

```python
# Generic parameter — identity info attached at parameterization:
list[int].__args__           # (int,)

# Custom metadata — identity info attached at definition:
MyHandler.__registry__       # "handlers"

# Same question: "what is this type, exactly?"
# Same mechanism: dunder attributes on the type object
# Same principle: preserve what was written
```

The only difference is who writes the metadata:
- `__args__` — Python fills it when you write `list[int]`
- `__registry__` — You fill it when you write `registry="handlers"`

Both are identity information. Both should be preserved. Both should be introspectable.

---

## Detailed Specification

### Reified Generics

| Syntax | Today | With This PEP |
|--------|-------|---------------|
| `x: list[int] = [1,2,3]` | `type(x)` → `list` | `type(x)` → `list` (unchanged) |
| `x = list[int]([1,2,3])` | TypeError | `type(x)` → `list[int]` |
| `isinstance(x, list[int])` | TypeError | Works |
| `list[int] is list[int]` | True (alias) | True (cached type) |

**Key semantics:**
- `list[int]([1,2,3])` creates an instance whose `type()` is `list[int]`
- `isinstance(x, list[int])` checks type identity, NOT element types (O(1), no iteration)
- Type objects are cached: `list[int] is list[int]` returns `True`
- Erased syntax unchanged: `x: list[int] = []` still creates plain `list`

### Type Metadata (Custom Axes)

```python
# Option A: keyword arguments to class statement
class MyStep(Step, scope="/pipeline/step_0"):
    pass

MyStep.__scope__  # "/pipeline/step_0"

# Option B: extend type() builtin
MyStep = type("MyStep", (Step,), {}, scope="/pipeline/step_0")

# Option C: decorator (works today, but not introspectable uniformly)
@with_scope("/pipeline/step_0")
class MyStep(Step):
    pass
```

This PEP prefers Option A or B for uniformity with `__args__`.

### Uniform Introspection API

```python
# All identity metadata accessible uniformly:
type(x).__args__           # (int,) — generic parameter
type(x).__scope__          # "/pipeline/step_0" — custom metadata
type(x).__origin__         # list — base type

# Or bundled:
type(x).__identity__       # {"args": (int,), "scope": "...", "origin": list}
```

---

## Backward Compatibility

**Fully backward compatible.** No existing code changes behavior.

| Existing Code | Behavior |
|---------------|----------|
| `x: list[int] = [1,2,3]` | Still creates `list` |
| `isinstance(x, list)` | Still works |
| `type("Foo", (Bar,), {})` | Still works |

Only NEW syntax opts into identity preservation.

---

## Performance

- **Type caching:** `list[int]` returns the same object on every access (O(1) lookup)
- **Memory:** One type object per unique parameterization (bounded by usage)
- **isinstance:** O(1) metadata comparison, no element traversal

## Static Type Checker Integration

Static type checkers (mypy, pyright) should treat reified construction identically to annotated construction:

```python
# These have identical static types:
x: list[int] = [1, 2, 3]      # Erased at runtime
y = list[int]([1, 2, 3])      # Reified at runtime

reveal_type(x)  # list[int]
reveal_type(y)  # list[int]
```

The difference is purely runtime. Static analysis sees the same type.

## Example: Type-Based Dispatch

This pattern is impossible with erased generics:

```python
handlers: dict[type, Callable] = {}

def register(t: type):
    def decorator(fn):
        handlers[t] = fn
        return fn
    return decorator

@register(list[int])
def handle_int_list(x):
    return sum(x)

@register(list[str])
def handle_str_list(x):
    return ",".join(x)

def dispatch(x):
    return handlers[type(x)](x)

# Works with reified generics:
dispatch(list[int]([1, 2, 3]))   # → 6
dispatch(list[str](["a", "b"])) # → "a,b"
```

---

## Why Now?

Python's type system has evolved:

- **PEP 484 (2014)**: Type hints for static analysis
- **PEP 585 (2020)**: `list[int]` syntax (but still erased)
- **PEP 604 (2020)**: `X | Y` union syntax

Each step made types more first-class. But there's a gap: **static analysis knows things that runtime cannot see**.

This PEP closes that gap. It doesn't change static typing—it makes runtime honor what static typing already knows.

---

## Open Questions

**1. Nested generics—automatic or explicit?**
```python
x = list[list[int]]([[1, 2], [3, 4]])
type(x[0])  # list[int] or list?
```

**2. Variance for `isinstance`?**
```python
isinstance(list[int]([1,2]), list[object])  # True (covariant) or False (invariant)?
```

**3. Custom metadata: standardize names or leave open?**

Should Python define standard axes (`__scope__`, `__registry__`), or let frameworks define their own?

---

## Prior Art

| Language | Approach |
|----------|----------|
| **C#** | **Reified.** `List<int>` ≠ `List<string>` at runtime |
| **Java** | Erased. `List<Integer>` → `List`. Workaround: pass `Class<T>` |
| **Kotlin** | Erased, but `reified` keyword for inline functions |
| **TypeScript** | Erased. Types disappear at compile time |

Python currently matches Java. This PEP moves toward C#—but opt-in, not mandatory.

---

## Rejected Alternatives

**"Use typeguard/beartype"** — These work around erasure but require redundant declarations and decorator overhead. This PEP makes identity first-class.

**"Erasure is fine, use protocols"** — Protocols answer "what can I do with this?" This PEP answers "what IS this?" Different questions.

---

## References

- PEP 484 — Type Hints
- PEP 585 — Type Hinting Generics In Standard Collections
- PEP 604 — Allow writing union types as X | Y

---

## Summary

> **If you wrote it, you should be able to ask about it.**

Python's static type system knows `list[int]`. This PEP makes runtime know it too.

One gap. One fix. Opt-in.
