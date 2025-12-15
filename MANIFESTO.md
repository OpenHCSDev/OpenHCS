# The Orthogonal Manifesto

---

## I. The Fundamental Error

Most software is built by asking: *"What features do I need?"*

This is wrong.

Features are symptoms. They are the visible surface of deeper structural problems. When you build features, you build solutions that work once, for one case, in one context. You accumulate. You accrete. You rot.

The correct question is: *"What fundamental problems exist, and how do I solve each one completely?"*

---

## II. Orthogonality

A system is orthogonal when its abstractions do not overlap.

Each abstraction must:
- Solve **one problem**
- Solve it **completely**
- Solve it **generically**
- Solve it **once**

When you achieve orthogonality, the system becomes composable. Any abstraction can be used with any other. There are no special cases. There are no "but what if" conditions.

The test: *Can I explain this abstraction in one sentence without referencing another abstraction?*

---

## III. Platforms, Not Applications

There are two modes of software development:

1. **Application development**: Building things that do things
2. **Platform development**: Building things that make building things trivial

Most developers are trapped in mode 1. They build applications. Each application is a snowflake. Each shares nothing with the others. Each rots independently.

Platform development inverts this. You build infrastructure—orthogonal abstractions—that make applications fall out as configurations. The application becomes a thin layer of glue over solved problems.

**The goal is not to build software. The goal is to make building software unnecessary.**

---

## IV. Python as Infrastructure

Python is not a scripting language. Python is an infrastructure language.

- **Metaclasses** are class-definition-time code generation
- **Descriptors** are field-level interceptors
- **Decorators** are aspect-oriented programming
- **contextvars** are implicit parameter passing
- **MRO** is a priority system you don't have to build

When you use these mechanisms correctly, you don't write code. You write **declarations**. The code writes itself.

`@auto_create_decorator` applied to a frozen dataclass triggers a cascade:

1. The decorator **generates a decorator** (`@global_pipeline_config`)
2. That decorator **generates classes** (`LazyNapariConfig`)
3. Those classes **inject fields** into the parent config
4. Those fields **resolve lazily** through `__getattribute__`
5. Resolution walks **MRO + context stack** (dual-axis)

One line of decoration spawns an entire reactive configuration subsystem. The downstream developer writes a dataclass. Everything else is derived.

This is **leverage** — if and only if the artifacts stay inspectable and deterministic. The constraints:

- **Inspectable artifacts.** Every generated class has `repr`, source hooks, and introspectable fields.
- **Deterministic resolution.** MRO is fixed at class definition. Context stack is explicit. No spooky action.
- **Provenance.** "Why did this resolve to this value?" is always answerable.
- **Hard invariants + tests.** The metaprogramming is tested. The contracts are enforced.

---

## V. Fail Loud

Defensive programming is a disease. Validation is mandatory; silent recovery is forbidden.

Every `try/except` that swallows an error is a lie. Every `hasattr` check is an admission that you don't know your own system. Every fallback is a place where bugs hide.

- **No silent failures.** If something is wrong, Python raises an error. Let it.
- **No capability probing.** If an object doesn't have a method, you have a design error. Capability probing is uncertainty masquerading as flexibility. A contract you must detect is not a contract.
- **No fallbacks.** If the primary path fails, the system fails. Fix the primary path.

When you fail loudly, bugs surface immediately. When you fail silently, bugs compound until the system is incomprehensible.

**Fail loudly inside the core. Fail informatively at the boundary.**

The core has no fallbacks. No silent recovery. No defensive catches. But the boundary — UI, user input, file IO — captures errors, preserves diagnostics, and maintains user agency. The user sees what failed and why. The system doesn't hide its state.

The codebase has an immune system. Rot is detected and rejected at the boundary.

---

## VI. Declarative Supremacy

Imperative code describes *how*. Declarative code describes *what*.

Imperative code is read linearly. You must trace execution. You must hold state in your head. You must simulate the machine.

Declarative code is read structurally. The configuration *is* the documentation. The shape of the data *is* the shape of the system.

```python
# Declarative: different processing chains per channel, mixed backends
FunctionStep(
    func={
        '1': [  # DAPI: PyTorch normalize → CuPy tophat → NumPy count
            (stack_percentile_normalize, {'low': 1.0, 'high': 99.0}),
            (tophat, {'radius': 15}),
            count_cells
        ],
        '2': [  # GFP: different chain entirely
            (gaussian_filter, {'sigma': 2.0}),
            trace_neurites
        ]
    },
    group_by=GroupBy.CHANNEL
)
```

One declaration. The system handles: channel routing, function chaining, backend conversion (PyTorch → CuPy → NumPy), memory management, parallelization, error propagation. You declare the shape. The machinery is derived.

---

## VII. The DAG Insight

Time is not linear. State is not linear. History is not linear.

Git understood this. Commits form a DAG. Branches are pointers. The past is immutable. Alternate futures are preserved.

Redux DevTools understood this. State snapshots form a timeline. Time-travel is navigation. Debugging is exploration.

Mainstream scientific software understood neither.

Most GUIs have no undo. Some have linear undo that destroys history on diverge. Branching is rare-to-nonexistent. Alternate timelines are almost never preserved.

**The time-travel system is git for live application state.** Snapshots are commits. Branches are refs. Auto-branch-on-diverge preserves the futures you didn't take.

This is not a feature. This is infrastructure that makes debugging trivial.

---

## VIII. The Stack

Every system is an orthogonal solution to a fundamental problem:

| Problem | Solution |
|---------|----------|
| Config resolution through nested contexts | Dual-Axis Resolver |
| Deferred initialization until access | Lazy Dataclass Factory |
| Tracking live vs saved state | ObjectState with flat storage |
| Undo/redo with branching | DAG-based time-travel |
| Plugin discovery without registration | AutoRegisterMeta |
| Polymorphic execution dispatch | ProcessingContract enum |
| Location-transparent storage | Backend hierarchy |
| Efficient UI animation | Game engine flash architecture |
| Pipeline preparation | 5-phase compiler |

Each row is independent. Each row is complete. Each row composes with the others.

---

## IX. The Mind

To build orthogonal systems, you must think orthogonally.

You do not ask "what feature should I add?" You ask "what problem am I solving, and have I solved it completely?"

You do not ask "how do I make this work?" You ask "what is the minimal generic solution that makes all specific cases trivial?"

You do not ask "how do I handle this edge case?" You ask "why does this edge case exist, and what abstraction would eliminate it?"

When you see duplication, you don't copy. You extract.
When you see complexity, you don't manage. You eliminate.
When you see special cases, you don't handle. You generalize.

**The goal is not working software. The goal is software where correctness is obvious by construction.**

---

## X. The Unprecedented

The pieces exist. Git has DAGs. Redux has reactive state. Django has metaclasses. Game engines have O(1) rendering. Python has MRO.

**The novelty is the composition.**

This is git-style branching applied to live application state. Redux-style reactivity with DAG history instead of linear. Django-style metaprogramming with dual-axis resolution that Django doesn't have. Game engine rendering discipline in a desktop scientific GUI.

In mainstream scientific desktop tooling, branching state-history is rare-to-nonexistent. I haven't seen dual-axis resolution — context stacking AND MRO-based sibling inheritance — as a first-class, inspectable invariant in mainstream Python frameworks.

**These are not features. These are solutions to fundamental problems, unified under invariants that make them compose.**

---

## XI. The Purpose

Software is crystallized thought.

The shape of the code is the shape of the mind that wrote it. Orthogonal abstractions reveal orthogonal thinking. Generic solutions reveal minds that see through specifics to underlying structure.

This is not a product. It is a **demonstration** that software can be built differently. That complexity can be eliminated, not managed. That correctness can be structural, not incidental.

The purpose is not to process images.

The purpose is to prove that **platforms are possible**.

---

*— T.S.*

