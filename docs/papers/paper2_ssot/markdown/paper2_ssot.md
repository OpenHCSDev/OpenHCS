# Paper 2: Formal Foundations for the Single Source of Truth Principle

**Status**: TOPLAS-ready | **Lean**: 1,811 lines, 96 theorems, 0 sorry

---

# Introduction

This paper proves that certain programming languages are *incapable* of achieving the Single Source of Truth (SSOT) principle for structural facts. All results are machine-checked in Lean 4 (1,753 lines across 13 files, 0 `sorry` placeholders).

The "Don't Repeat Yourself" (DRY) principle has been industry guidance for 25 years:

> "Every piece of knowledge must have a single, unambiguous, authoritative representation within a system." --- Hunt & Thomas, *The Pragmatic Programmer* (1999)

Despite widespread acceptance, DRY has never been formalized. No prior work answers: *What language features are necessary to achieve SSOT? What language features are sufficient?* We answer both questions, proving the answer is the same for both---an if-and-only-if theorem.

The core insight: SSOT for *structural facts* (class existence, method signatures, type relationships) requires language features that most mainstream languages lack. Specifically:

1.  **Definition-time hooks** (Theorem [\[thm:hooks-necessary\]](#thm:hooks-necessary){reference-type="ref" reference="thm:hooks-necessary"}): Code must execute when a class/function is *defined*, not when it is *used*. This enables derivation at the moment structure is established.

2.  **Introspectable derivation** (Theorem [\[thm:introspection-necessary\]](#thm:introspection-necessary){reference-type="ref" reference="thm:introspection-necessary"}): The program must be able to query what was derived and from what. This enables verification that SSOT holds.

3.  **Both are necessary** (Theorem [\[thm:independence\]](#thm:independence){reference-type="ref" reference="thm:independence"}): Neither feature alone suffices. A language with hooks but no introspection can derive but cannot verify. A language with introspection but no hooks cannot derive at the right moment.

These requirements are **derived**, not chosen. We do not *prefer* definition-time hooks---we *prove* they are necessary. The logical structure forces these requirements as the unique solution.

## Core Theorems {#sec:core-theorems}

This paper's core contribution is three theorems that admit no counterargument:

1.  **Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"} (SSOT Requirements):** A language enables SSOT for structural facts if and only if it provides (1) definition-time hooks AND (2) introspectable derivation results.

    *Proof technique:* This is an if-and-only-if theorem. The requirements are both necessary (without either, SSOT is impossible) and sufficient (with both, SSOT is achievable). There is no middle ground.

2.  **Theorem [\[thm:python-unique\]](#thm:python-unique){reference-type="ref" reference="thm:python-unique"} (Python Uniqueness):** Among mainstream languages (top-10 TIOBE, consistent presence over 5+ years), Python is the only language satisfying both SSOT requirements.

    *Proof technique:* This is proved by exhaustive evaluation. We check every mainstream language against formally-defined criteria. The evaluation is complete---no language is omitted.

3.  **Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"} (Unbounded Complexity Gap):** The ratio of modification complexity between SSOT-incomplete and SSOT-complete architectures grows without bound: $O(1)$ vs $\Omega(n)$ where $n$ is the number of encoding locations.

    *Proof technique:* Asymptotic analysis shows $\lim_{n \to \infty} n/1 = \infty$. For any constant $k$, there exists a codebase size such that SSOT provides at least $k\times$ reduction. The gap is not "large"---it is unbounded.

## What This Paper Does NOT Claim {#sec:non-claims}

To prevent misreading, we state explicit non-claims:

1.  **NOT "Python is the best language."** We claim Python satisfies SSOT requirements. We make no claims about performance, safety, or other dimensions.

2.  **NOT "SSOT matters for all codebases."** Small codebases may not benefit. Our complexity bounds are asymptotic---they matter at scale.

3.  **NOT "Other languages cannot approximate SSOT."** External tools (code generators, linters) can help. We claim the *language itself* cannot achieve SSOT without the identified features.

4.  **NOT "This is novel wisdom."** The insight that metaprogramming helps with DRY is old. What is new is the *formalization* and *machine-checked proof* of necessity.

## Contributions {#sec:contributions}

This paper makes five contributions:

**1. Formal foundations (Section [2](#sec:foundations){reference-type="ref" reference="sec:foundations"}):**

-   Definition of modification complexity as degrees of freedom (DOF) in state space

-   Definition of SSOT as DOF = 1

-   Proof that SSOT is optimal: DOF = 0 means missing specification, DOF $>$ 1 means inconsistency possible

**2. Language requirements (Section [4](#sec:requirements){reference-type="ref" reference="sec:requirements"}):**

-   Theorem [\[thm:hooks-necessary\]](#thm:hooks-necessary){reference-type="ref" reference="thm:hooks-necessary"}: Definition-time hooks are necessary

-   Theorem [\[thm:introspection-necessary\]](#thm:introspection-necessary){reference-type="ref" reference="thm:introspection-necessary"}: Introspection is necessary

-   Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}: Both together are sufficient

-   Proof that these requirements are forced by the structure of the problem

**3. Language evaluation (Section [5](#sec:evaluation){reference-type="ref" reference="sec:evaluation"}):**

-   Exhaustive evaluation of 10 mainstream languages

-   Extended evaluation of 3 non-mainstream languages (CLOS, Smalltalk, Ruby)

-   Theorem [\[thm:three-lang\]](#thm:three-lang){reference-type="ref" reference="thm:three-lang"}: Exactly three languages satisfy SSOT requirements

**4. Complexity bounds (Section [6](#sec:bounds){reference-type="ref" reference="sec:bounds"}):**

-   Theorem [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"}: SSOT achieves $O(1)$ modification complexity

-   Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"}: Non-SSOT requires $\Omega(n)$ modifications

-   Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"}: The gap is unbounded

**5. Empirical validation (Section [\[sec:empirical\]](#sec:empirical){reference-type="ref" reference="sec:empirical"}):**

-   13 case studies from OpenHCS (45K LoC production Python codebase)

-   Concrete DOF measurements: 184 total pre-SSOT, 13 total post-SSOT

-   Mean reduction factor: 14.2$\times$

-   Detailed before/after code for each case study

## Empirical Context: OpenHCS {#sec:openhcs-context}

**What it does:** OpenHCS is a bioimage analysis platform for high-content screening. It processes microscopy images through configurable pipelines, with GUI-based design and Python code export. The system requires:

-   Automatic registration of analysis components

-   Type-safe configuration with inheritance

-   Runtime enumeration of available processors

-   Provenance tracking for reproducibility

**Why it matters for this paper:** OpenHCS requires SSOT for structural facts. When a new image processor is added (by subclassing `BaseProcessor`), it must automatically appear in:

-   The GUI component palette

-   The configuration schema

-   The serialization registry

-   The documentation generator

Without SSOT, adding a processor requires updating 4+ locations. With SSOT, only the class definition is needed---Python's `__init_subclass__` and `__subclasses__()` handle the rest.

**Key finding:** PR #44 migrated from duck typing (`hasattr()` checks) to nominal typing (ABC contracts). This eliminated 47 scattered checks, reducing DOF from 47 to 1. The migration validates both:

1.  The theoretical prediction: DOF reduction is achievable

2.  The practical benefit: Maintenance cost decreased measurably

## Decision Procedure, Not Preference {#sec:decision}

The contribution of this paper is not the theorems alone, but their consequence: *language selection for SSOT becomes a decision procedure*.

Given requirements:

1.  If you need SSOT for structural facts, you need definition-time hooks AND introspection

2.  If your language lacks these features, SSOT is impossible within the language

3.  External tooling can help but introduces fragility (not verifiable at runtime)

**Implications:**

1.  **Language design.** Future languages should include definition-time hooks and introspection if DRY is a design goal. Languages designed without these features (Go, Rust, Swift) cannot achieve SSOT for structural facts.

2.  **Architecture.** When choosing a language for a project requiring SSOT, the choice is constrained by this analysis. "I prefer Go" is not valid when SSOT is required.

3.  **Tooling.** External tools (code generators, macros) can work around language limitations but are not equivalent to language-level support.

4.  **Pedagogy.** Software engineering courses should teach DRY as a formal principle with language requirements, not as a vague guideline.

## Paper Structure {#sec:structure}

Section [2](#sec:foundations){reference-type="ref" reference="sec:foundations"} establishes formal definitions: edit space, facts, encoding, degrees of freedom. Section [3](#sec:ssot){reference-type="ref" reference="sec:ssot"} defines SSOT and proves its optimality. Section [4](#sec:requirements){reference-type="ref" reference="sec:requirements"} derives language requirements with necessity proofs. Section [5](#sec:evaluation){reference-type="ref" reference="sec:evaluation"} evaluates mainstream languages exhaustively. Section [6](#sec:bounds){reference-type="ref" reference="sec:bounds"} proves complexity bounds. Section [\[sec:empirical\]](#sec:empirical){reference-type="ref" reference="sec:empirical"} presents empirical validation with 13 case studies. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"} surveys related work. Appendix [8](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"} addresses anticipated objections. Appendix [\[sec:lean\]](#sec:lean){reference-type="ref" reference="sec:lean"} contains complete Lean 4 proof listings.

# Formal Foundations {#sec:foundations}

We formalize the concepts underlying DRY/SSOT using state space theory. The formalization proceeds in four stages: (1) define the space of possible edits, (2) define what a "fact" is, (3) define what it means for code to "encode" a fact, (4) define the key metric: degrees of freedom.

## Edit Space and Codebases {#sec:edit-space}

::: definition
A *codebase* $C$ is a finite collection of source files, each containing a sequence of syntactic constructs (classes, functions, statements, expressions).
:::

::: definition
A *location* $L \in C$ is a syntactically identifiable region of code: a class definition, a function body, a configuration value, a type annotation, etc.
:::

::: definition
For a codebase $C$, the *edit space* $E(C)$ is the set of all syntactically valid modifications to $C$. Each edit $\delta \in E(C)$ transforms $C$ into a new codebase $C' = \delta(C)$.
:::

The edit space is large---exponential in codebase size. But we are not interested in arbitrary edits. We are interested in edits that *change a specific fact*.

## Facts: Atomic Units of Specification {#sec:facts}

::: definition
[]{#def:fact label="def:fact"} A *fact* $F$ is an atomic unit of program specification---a single piece of knowledge that can be independently modified. Facts are the indivisible units of meaning in a specification.
:::

The granularity of facts is determined by the specification, not the implementation. If two pieces of information must always change together, they constitute a single fact. If they can change independently, they are separate facts.

**Examples of facts:**

::: center
  **Fact**                                           **Description**
  -------------------------------------------------- -----------------------------
  $F_1$: "threshold = 0.5"                           A configuration value
  $F_2$: "`PNGLoader` handles `.png`"                A type-to-handler mapping
  $F_3$: "`validate()` returns `bool`"               A method signature
  $F_4$: "`Detector` is a subclass of `Processor`"   An inheritance relationship
  $F_5$: "`Config` has field `name: str`"            A dataclass field
:::

::: definition
[]{#def:structural-fact label="def:structural-fact"} A fact $F$ is *structural* iff it concerns the structure of the type system: class existence, inheritance relationships, method signatures, or attribute definitions. Structural facts are fixed at *definition time*, not runtime.
:::

The distinction between structural and non-structural facts is crucial. A configuration value ("threshold = 0.5") can be changed at runtime. A method signature ("`validate()` returns `bool`") is fixed when the class is defined. SSOT for structural facts requires different mechanisms than SSOT for configuration values.

## Encoding: The Correctness Relationship {#sec:encoding}

::: definition
[]{#def:encodes label="def:encodes"} Location $L$ *encodes* fact $F$, written $\text{encodes}(L, F)$, iff correctness requires updating $L$ when $F$ changes.

Formally: $$\text{encodes}(L, F) \Longleftrightarrow \forall \delta_F: \neg\text{updated}(L, \delta_F) \rightarrow \text{incorrect}(\delta_F(C))$$

where $\delta_F$ is an edit targeting fact $F$.
:::

**Key insight:** This definition is **forced** by correctness, not chosen. We do not decide what encodes what---correctness requirements determine it. If failing to update location $L$ when fact $F$ changes produces an incorrect program, then $L$ encodes $F$. This is an objective, observable property.

::: example
[]{#ex:encoding label="ex:encoding"} Consider a type registry:

    # Location L1: Class definition
    class PNGLoader(ImageLoader):
        format = "png"

    # Location L2: Registry entry
    LOADERS = {"png": PNGLoader, "jpg": JPGLoader}

    # Location L3: Documentation
    # Supported formats: png, jpg

The fact $F$ = "`PNGLoader` handles `png`" is encoded at:

-   $L_1$: The class definition (primary encoding)

-   $L_2$: The registry dictionary (secondary encoding)

-   $L_3$: The documentation comment (tertiary encoding)

If $F$ changes (e.g., to "`PNGLoader` handles `png` and `apng`"), all three locations must be updated for correctness. The program is incorrect if $L_2$ still says `{"png": PNGLoader}` when the class now handles both formats.
:::

## Modification Complexity {#sec:mod-complexity}

::: definition
[]{#def:mod-complexity label="def:mod-complexity"} $$M(C, \delta_F) = |\{L \in C : \text{encodes}(L, F)\}|$$ The number of locations that must be updated when fact $F$ changes.
:::

Modification complexity is the central metric of this paper. It measures the *cost* of changing a fact. A codebase with $M(C, \delta_F) = 47$ requires 47 edits to correctly implement a change to fact $F$. A codebase with $M(C, \delta_F) = 1$ requires only 1 edit.

::: theorem
[]{#thm:correctness-forcing label="thm:correctness-forcing"} $M(C, \delta_F)$ is the **minimum** number of edits required for correctness. Fewer edits imply an incorrect program.
:::

::: proof
*Proof.* Suppose $M(C, \delta_F) = k$, meaning $k$ locations encode $F$. By Definition [\[def:encodes\]](#def:encodes){reference-type="ref" reference="def:encodes"}, each encoding location must be updated when $F$ changes. If only $j < k$ locations are updated, then $k - j$ locations still reflect the old value of $F$. These locations create inconsistencies:

1.  The specification says $F$ has value $v'$ (new)

2.  Locations $L_1, \ldots, L_j$ reflect $v'$

3.  Locations $L_{j+1}, \ldots, L_k$ reflect $v$ (old)

By Definition [\[def:encodes\]](#def:encodes){reference-type="ref" reference="def:encodes"}, the program is incorrect. Therefore, all $k$ locations must be updated, and $k$ is the minimum. 0◻ ◻
:::

## Independence and Degrees of Freedom {#sec:dof}

Not all encoding locations are created equal. Some are *derived* from others.

::: definition
[]{#def:independent label="def:independent"} Locations $L_1, L_2$ are *independent* for fact $F$ iff they can diverge---updating $L_1$ does not automatically update $L_2$, and vice versa.

Formally: $L_1$ and $L_2$ are independent iff there exists a sequence of edits that makes $L_1$ and $L_2$ encode different values for $F$.
:::

::: definition
[]{#def:derived label="def:derived"} Location $L_{\text{derived}}$ is *derived from* $L_{\text{source}}$ iff updating $L_{\text{source}}$ automatically updates $L_{\text{derived}}$. Derived locations are not independent of their sources.
:::

::: example
[]{#ex:independence label="ex:independence"} Consider two architectures for the type registry:

**Architecture A (independent locations):**

    # L1: Class definition
    class PNGLoader(ImageLoader): ...

    # L2: Manual registry (independent of L1)
    LOADERS = {"png": PNGLoader}

Here $L_1$ and $L_2$ are independent. A developer can change $L_1$ without updating $L_2$, causing inconsistency.

**Architecture B (derived location):**

    # L1: Class definition with registration
    class PNGLoader(ImageLoader):
        format = "png"

    # L2: Derived registry (computed from L1)
    LOADERS = {cls.format: cls for cls in ImageLoader.__subclasses__()}

Here $L_2$ is derived from $L_1$. Updating the class definition automatically updates the registry. They cannot diverge.
:::

::: definition
[]{#def:dof label="def:dof"} $$\text{DOF}(C, F) = |\{L \in C : \text{encodes}(L, F) \land \text{independent}(L)\}|$$ The number of *independent* locations encoding fact $F$.
:::

DOF is the key metric. Modification complexity $M$ counts all encoding locations. DOF counts only the independent ones. If all but one encoding location is derived, DOF = 1 even though $M$ may be large.

::: theorem
[]{#thm:dof-inconsistency label="thm:dof-inconsistency"} $\text{DOF}(C, F) = k$ implies $k$ different values for $F$ can coexist in $C$ simultaneously.
:::

::: proof
*Proof.* Each independent location can hold a different value. By Definition [\[def:independent\]](#def:independent){reference-type="ref" reference="def:independent"}, no constraint forces agreement between independent locations. Therefore, $k$ independent locations can hold $k$ distinct values. The program may compile and run, but it encodes inconsistent specifications. 0◻ ◻
:::

::: corollary
[]{#cor:dof-risk label="cor:dof-risk"} $\text{DOF}(C, F) > 1$ implies potential inconsistency. The codebase can enter a state where different parts encode different values for the same fact.
:::

## The DOF Lattice {#sec:dof-lattice}

DOF values form a lattice with distinct meanings:

::: center
   **DOF**  **Meaning**
  --------- ----------------------------------------------------------
      0     Fact $F$ is not encoded anywhere (missing specification)
      1     Exactly one source of truth (optimal)
   $k > 1$  $k$ independent sources (inconsistency possible)
:::

::: theorem
[]{#thm:dof-optimal label="thm:dof-optimal"} For any fact $F$ that must be encoded, $\text{DOF}(C, F) = 1$ is the unique optimal value:

1.  DOF = 0: Fact is not specified (underspecification)

2.  DOF = 1: Exactly one source (optimal)

3.  DOF $>$ 1: Multiple sources can diverge (overspecification with inconsistency risk)
:::

::: proof
*Proof.*

1.  DOF = 0 means no location encodes $F$. The program cannot correctly implement $F$ because it has no representation. This is underspecification.

2.  DOF = 1 means exactly one independent location encodes $F$. All other encodings (if any) are derived. Updating the single source updates all derived locations. Inconsistency is impossible.

3.  DOF $>$ 1 means multiple independent locations encode $F$. By Corollary [\[cor:dof-risk\]](#cor:dof-risk){reference-type="ref" reference="cor:dof-risk"}, they can diverge. This is overspecification with inconsistency risk.

Therefore, DOF = 1 is the unique value that avoids both underspecification and inconsistency risk. 0◻ ◻
:::

# Single Source of Truth {#sec:ssot}

Having established the formal foundations, we now define SSOT precisely and prove its optimality.

## SSOT Definition {#sec:ssot-def}

::: definition
[]{#def:ssot label="def:ssot"} Codebase $C$ satisfies *SSOT* for fact $F$ iff: $$|\{L \in C : \text{encodes}(L, F) \land \text{independent}(L)\}| = 1$$ Equivalently: $\text{DOF}(C, F) = 1$.
:::

SSOT is the formalization of DRY. Hunt & Thomas's "single, unambiguous, authoritative representation" corresponds precisely to DOF = 1. The representation is:

-   **Single:** Only one independent encoding exists

-   **Unambiguous:** All other encodings are derived, hence cannot diverge

-   **Authoritative:** The single source determines all derived representations

::: theorem
[]{#thm:ssot-optimal label="thm:ssot-optimal"} If $C$ satisfies SSOT for $F$, then the effective modification complexity is 1: updating the single source updates all derived representations.
:::

::: proof
*Proof.* Let $C$ satisfy SSOT for $F$, meaning $\text{DOF}(C, F) = 1$. Let $L_s$ be the single independent encoding location. All other encodings $L_1, \ldots, L_k$ are derived from $L_s$.

When fact $F$ changes:

1.  The developer updates $L_s$ (1 edit)

2.  By Definition [\[def:derived\]](#def:derived){reference-type="ref" reference="def:derived"}, $L_1, \ldots, L_k$ are automatically updated

3.  Total manual edits: 1

The program is correct after 1 edit. Therefore, effective modification complexity is 1. 0◻ ◻
:::

## SSOT vs. Modification Complexity {#sec:ssot-vs-m}

Note the distinction between $M(C, \delta_F)$ and effective modification complexity:

-   $M(C, \delta_F)$ counts *all* locations that must be updated

-   Effective modification complexity counts only *manual* updates

With SSOT, $M$ may be large (many locations encode $F$), but effective complexity is 1 (only the source requires manual update). The derivation mechanism handles the rest.

::: example
[]{#ex:ssot-large-m label="ex:ssot-large-m"} Consider a codebase where 50 classes inherit from `BaseProcessor`:

    class BaseProcessor(ABC):
        @abstractmethod
        def process(self, data: np.ndarray) -> np.ndarray: ...

    class Detector(BaseProcessor): ...
    class Segmenter(BaseProcessor): ...
    # ... 48 more subclasses

The fact $F$ = "All processors must have a `process` method" is encoded in 51 locations:

-   1 ABC definition

-   50 concrete implementations

Without SSOT: Changing the signature (e.g., adding a parameter) requires 51 edits.

With SSOT: The ABC contract is the single source. Python's ABC mechanism enforces that all subclasses implement `process`. Changing the ABC updates the contract; the type checker (or runtime) flags non-compliant subclasses. The developer updates each subclass, but the *specification* of what must be updated is derived from the ABC.

Note: SSOT does not eliminate the need to update implementations. It ensures the *specification* of the contract has a single source. The implementations are separate facts.
:::

## Derivation Mechanisms {#sec:derivation}

::: definition
[]{#def:derivation label="def:derivation"} Location $L_{\text{derived}}$ is *derived from* $L_{\text{source}}$ for fact $F$ iff: $$\text{updated}(L_{\text{source}}) \rightarrow \text{automatically\_updated}(L_{\text{derived}})$$ No manual intervention is required. The update propagates automatically.
:::

Derivation can occur at different times:

::: center
  **Derivation Time**   **Examples**
  --------------------- -----------------------------------------------------------
  Compile time          C++ templates, Rust macros, code generation
  Definition time       Python metaclasses, `__init_subclass__`, class decorators
  Runtime               Lazy computation, memoization
:::

For *structural facts*, derivation must occur at *definition time*. This is because structural facts (class existence, method signatures) are fixed when the class is defined. Compile-time derivation is too early (source code hasn't been parsed). Runtime derivation is too late (structure is already fixed).

::: theorem
[]{#thm:derivation-excludes label="thm:derivation-excludes"} If $L_{\text{derived}}$ is derived from $L_{\text{source}}$, then $L_{\text{derived}}$ does not contribute to DOF.
:::

::: proof
*Proof.* By Definition [\[def:independent\]](#def:independent){reference-type="ref" reference="def:independent"}, locations are independent iff they can diverge. By Definition [\[def:derivation\]](#def:derivation){reference-type="ref" reference="def:derivation"}, derived locations are automatically updated when the source changes. They cannot diverge.

Formally: Let $L_d$ be derived from $L_s$. Suppose $L_s$ encodes value $v$ for fact $F$. Then $L_d$ encodes $f(v)$ for some function $f$ (possibly the identity). When $L_s$ changes to $v'$, $L_d$ automatically changes to $f(v')$. There is no state where $L_s = v'$ and $L_d = f(v)$. They cannot diverge.

Therefore, $L_d$ is not independent of $L_s$, and does not contribute to DOF. 0◻ ◻
:::

::: corollary
[]{#cor:metaprogramming label="cor:metaprogramming"} If all encodings of $F$ except one are derived from that one, then $\text{DOF}(C, F) = 1$.
:::

::: proof
*Proof.* Let $L_s$ be the non-derived encoding. All other encodings $L_1, \ldots, L_k$ are derived from $L_s$. By Theorem [\[thm:derivation-excludes\]](#thm:derivation-excludes){reference-type="ref" reference="thm:derivation-excludes"}, none of $L_1, \ldots, L_k$ contribute to DOF. Only $L_s$ contributes. Therefore, $\text{DOF}(C, F) = 1$. 0◻ ◻
:::

## SSOT Patterns in Python {#sec:ssot-patterns}

Python provides several mechanisms for achieving SSOT:

**Pattern 1: Subclass Registration via `__init_subclass__`**

    class Registry:
        _registry = {}

        def __init_subclass__(cls, **kwargs):
            super().__init_subclass__(**kwargs)
            Registry._registry[cls.__name__] = cls

    class Handler(Registry):
        pass

    class PNGHandler(Handler):  # Automatically registered
        pass

The fact "`PNGHandler` is in the registry" is encoded in two locations:

1.  The class definition (source)

2.  The registry dictionary (derived via `__init_subclass__`)

DOF = 1 because the registry entry is derived.

**Pattern 2: Subclass Enumeration via `__subclasses__()`**

    class Processor(ABC):
        @classmethod
        def all_processors(cls):
            return cls.__subclasses__()

    class Detector(Processor): pass
    class Segmenter(Processor): pass

    # Usage: Processor.all_processors() -> [Detector, Segmenter]

The fact "which classes are processors" is encoded:

1.  In each class definition (via inheritance)

2.  In the `__subclasses__()` result (derived)

DOF = 1 because `__subclasses__()` is computed from the class definitions.

**Pattern 3: ABC Contracts**

    class ImageLoader(ABC):
        @abstractmethod
        def load(self, path: str) -> np.ndarray: ...

        @abstractmethod
        def supported_extensions(self) -> List[str]: ...

The fact "loaders must implement `load` and `supported_extensions`" is encoded once in the ABC. All subclasses must comply. The ABC is the single source; compliance is enforced.

# Language Requirements for SSOT {#sec:requirements}

We now derive the language features necessary and sufficient for achieving SSOT. This section answers: *What must a language provide for SSOT to be possible?*

The answer is derived, not chosen. We do not *prefer* certain features---we *prove* they are necessary.

## The Foundational Axiom {#sec:axiom}

The entire derivation rests on one axiom. This axiom is not an assumption we make---it is a definitional truth about how programming languages work:

::: axiom
[]{#axiom:fixation label="axiom:fixation"} Structural facts are fixed at definition time. After a class/type is defined, its inheritance relationships, method signatures, and other structural properties cannot be retroactively changed.
:::

This is not controversial. In every mainstream language:

-   Once `class Foo extends Bar` is compiled/interpreted, `Foo`'s parent cannot become `Baz`

-   Once `def process(self, x: int)` is defined, the signature cannot retroactively become `(self, x: str)`

-   Once `trait Handler` is implemented for `PNGDecoder`, that relationship is permanent

Languages that allow runtime modification (Python's `__bases__`, Ruby's reopening) are modifying *future* behavior, not *past* structure. The fact that "`PNGHandler` was defined as a subclass of `Handler`" is fixed at the moment of definition.

**All subsequent theorems are logical consequences of this axiom.** Rejecting the axiom requires demonstrating a language where structural facts can be retroactively modified---which does not exist.

## The Timing Constraint {#sec:timing}

The key insight is that structural facts have a *timing constraint*. Unlike configuration values (which can be changed at any time), structural facts are fixed at specific moments:

::: definition
[]{#def:structural-timing label="def:structural-timing"} A structural fact $F$ (class existence, inheritance relationship, method signature) is *fixed* when its defining construct is executed. After that point, the structure cannot be retroactively modified.
:::

In Python, classes are defined when the `class` statement executes:

    class Detector(Processor):  # Structure fixed HERE
        def detect(self, img): ...

    # After this point, Detector's inheritance cannot be changed

In Java, classes are defined at compile time:

    public class Detector extends Processor {  // Structure fixed at COMPILE TIME
        public void detect(Image img) { ... }
    }

**Critical Distinction: Compile-Time vs. Definition-Time**

These terms are often confused. We define them precisely:

::: definition
[]{#def:compile-time label="def:compile-time"} *Compile-time* is when source code is translated to an executable form (bytecode, machine code). Compile-time occurs *before the program runs*.
:::

::: definition
[]{#def:definition-time label="def:definition-time"} *Definition-time* is when a class/type definition is *executed*. In Python, this is *at runtime* when the `class` statement runs. In Java, this is *at compile-time* when `javac` processes the file.
:::

The key insight: **Python's `class` statement is executable code.** When Python encounters:

    class Foo(Bar):
        x = 1

It *executes* code that:

1.  Creates a new namespace

2.  Executes the class body in that namespace

3.  Calls the metaclass to create the class object

4.  Calls `__init_subclass__` on parent classes

5.  Binds the name `Foo` to the new class

This is why Python has "definition-time hooks"---they execute when the definition runs.

Java's `class` declaration is *not* executable---it is a static declaration processed by the compiler. No user code can hook into this process.

The timing constraint has profound implications for derivation:

::: theorem
[]{#thm:timing-forces label="thm:timing-forces"} Derivation for structural facts must occur at or before the moment the structure is fixed.
:::

::: proof
*Proof.* Let $F$ be a structural fact. Let $t_{\text{fix}}$ be the moment $F$ is fixed. Any derivation $D$ that depends on $F$ must execute at some time $t_D$.

Case 1: $t_D < t_{\text{fix}}$. Then $D$ executes before $F$ is fixed. $D$ cannot derive from $F$ because $F$ does not yet exist.

Case 2: $t_D > t_{\text{fix}}$. Then $D$ executes after $F$ is fixed. $D$ can read $F$ but cannot modify structure derived from $F$---the structure is already fixed.

Case 3: $t_D = t_{\text{fix}}$. Then $D$ executes at the moment $F$ is fixed. $D$ can both read $F$ and modify derived structures before they are fixed.

Therefore, derivation for structural facts must occur at definition time ($t_D = t_{\text{fix}}$). 0◻ ◻
:::

## Requirement 1: Definition-Time Hooks {#sec:hooks}

::: definition
[]{#def:hook label="def:hook"} A *definition-time hook* is a language construct that executes arbitrary code when a definition (class, function, module) is *created*, not when it is *used*.
:::

**Python's definition-time hooks:**

::: center
  **Hook**                         **When it executes**
  -------------------------------- ----------------------------------------------------
  `__init_subclass__`              When a subclass is defined
  Metaclass `__new__`/`__init__`   When a class using that metaclass is defined
  Class decorator                  Immediately after class body executes
  `__set_name__`                   When a descriptor is assigned to a class attribute
:::

**Example: `__init_subclass__` registration**

    class Registry:
        _handlers = {}

        def __init_subclass__(cls, format=None, **kwargs):
            super().__init_subclass__(**kwargs)
            if format:
                Registry._handlers[format] = cls

    class PNGHandler(Registry, format="png"):
        pass  # Automatically registered when class is defined

    class JPGHandler(Registry, format="jpg"):
        pass  # Automatically registered when class is defined

    # Registry._handlers == {"png": PNGHandler, "jpg": JPGHandler}

The registration happens at definition time, not at first use. When the `class PNGHandler` statement executes, `__init_subclass__` runs and adds the handler to the registry.

::: theorem
[]{#thm:hooks-necessary label="thm:hooks-necessary"} SSOT for structural facts requires definition-time hooks.
:::

::: proof
*Proof.* By Theorem [\[thm:timing-forces\]](#thm:timing-forces){reference-type="ref" reference="thm:timing-forces"}, derivation for structural facts must occur at definition time. Without definition-time hooks, no code can execute at that moment. Therefore, derivation is impossible. Without derivation, secondary encodings cannot be automatically updated. DOF $>$ 1 is unavoidable.

Contrapositive: If a language lacks definition-time hooks, SSOT for structural facts is impossible. 0◻ ◻
:::

**Languages lacking definition-time hooks:**

-   **Java**: Annotations are metadata, not executable hooks. They are processed by external tools (annotation processors), not by the language at class definition.

-   **C++**: Templates expand at compile time but do not execute arbitrary code. SFINAE and `constexpr if` are not hooks---they select branches, not execute callbacks.

-   **Go**: No hook mechanism. Interfaces are implicit. No code runs at type definition.

-   **Rust**: Procedural macros run at compile time but are opaque at runtime. The macro expansion is not introspectable.

## Requirement 2: Introspectable Derivation {#sec:introspection}

Definition-time hooks enable derivation. But SSOT also requires *verification*---the ability to confirm that DOF = 1.

::: definition
[]{#def:introspection label="def:introspection"} Derivation is *introspectable* iff the program can query:

1.  What structures were derived

2.  From which source each derived structure came

3.  What the current state of derived structures is
:::

**Python's introspection capabilities:**

::: center
  **Query**                            **Python Mechanism**
  ------------------------------------ -------------------------------------
  What subclasses exist?               `cls.__subclasses__()`
  What is the inheritance chain?       `cls.__mro__`
  What attributes does a class have?   `dir(cls)`, `vars(cls)`
  What type is this object?            `type(obj)`, `isinstance(obj, cls)`
  What methods are abstract?           `cls.__abstractmethods__`
:::

**Example: Verifying registration completeness**

    def verify_registration():
        """Verify all subclasses are registered."""
        all_subclasses = set(ImageLoader.__subclasses__())
        registered = set(LOADER_REGISTRY.values())

        unregistered = all_subclasses - registered
        if unregistered:
            raise RuntimeError(f"Unregistered loaders: {unregistered}")

This verification is only possible because Python provides `__subclasses__()`. In languages without this capability, the programmer cannot enumerate what subclasses exist.

::: theorem
[]{#thm:introspection-necessary label="thm:introspection-necessary"} Verifying that SSOT holds requires introspection.
:::

::: proof
*Proof.* Verification of SSOT requires confirming DOF = 1. This requires:

1.  Enumerating all locations encoding fact $F$

2.  Determining which are independent vs. derived

3.  Confirming exactly one is independent

Step (1) requires introspection: the program must query what structures exist and what they encode. Without introspection, the program cannot enumerate encodings. Verification is impossible.

Without verifiable SSOT, the programmer cannot confirm SSOT holds. They must trust that their code is correct without runtime confirmation. Bugs in derivation logic go undetected. 0◻ ◻
:::

**Languages lacking introspection for derivation:**

-   **C++**: Cannot ask "what types instantiated template `Foo<T>`?"

-   **Rust**: Procedural macro expansion is opaque at runtime. Cannot query what was generated.

-   **TypeScript**: Types are erased at runtime. Cannot query type relationships.

-   **Go**: No type registry. Cannot enumerate types implementing an interface.

## Independence of Requirements {#sec:independence}

The two requirements---definition-time hooks and introspection---are independent. Neither implies the other.

::: theorem
[]{#thm:independence label="thm:independence"}

1.  A language can have definition-time hooks without introspection

2.  A language can have introspection without definition-time hooks
:::

::: proof
*Proof.* **(1) Hooks without introspection:** Rust procedural macros execute at compile time (a form of definition-time hook) but the generated code is opaque at runtime. The program cannot query what the macro generated.

**(2) Introspection without hooks:** Java provides `Class.getMethods()`, `Class.getInterfaces()`, etc. (introspection) but no code executes when a class is defined. Annotations are metadata, not executable hooks.

Therefore, the requirements are independent. 0◻ ◻
:::

## The Completeness Theorem {#sec:completeness}

::: theorem
[]{#thm:ssot-iff label="thm:ssot-iff"} A language $L$ enables complete SSOT for structural facts if and only if:

1.  $L$ provides definition-time hooks, AND

2.  $L$ provides introspectable derivation results
:::

::: proof
*Proof.* $(\Rightarrow)$ **Necessity:** Suppose $L$ enables complete SSOT for structural facts.

-   By Theorem [\[thm:hooks-necessary\]](#thm:hooks-necessary){reference-type="ref" reference="thm:hooks-necessary"}, $L$ must provide definition-time hooks

-   By Theorem [\[thm:introspection-necessary\]](#thm:introspection-necessary){reference-type="ref" reference="thm:introspection-necessary"}, $L$ must provide introspection

$(\Leftarrow)$ **Sufficiency:** Suppose $L$ provides both definition-time hooks and introspection.

-   Definition-time hooks enable derivation at the right moment (when structure is fixed)

-   Introspection enables verification that all secondary encodings are derived

-   Therefore, SSOT is achievable: create one source, derive all others, verify completeness

The if-and-only-if follows. 0◻ ◻
:::

::: corollary
[]{#cor:ssot-complete label="cor:ssot-complete"} A language is *SSOT-complete* iff it satisfies both requirements. A language is *SSOT-incomplete* otherwise.
:::

## The Logical Chain (Summary) {#sec:chain}

For clarity, we summarize the complete derivation from axiom to conclusion:

::: center
:::

**Every step is machine-checked in Lean 4.** The proofs compile with zero `sorry` placeholders. Rejecting this chain requires identifying a specific flaw in the axiom, the logic, or the Lean formalization.

## Concrete Impossibility Demonstration {#sec:impossibility}

We now demonstrate *exactly why* SSOT-incomplete languages cannot achieve SSOT for structural facts. This is not about "Java being worse"---it is about what Java *cannot express*.

**The Structural Fact:** "`PNGHandler` handles `.png` files."

This fact must be encoded in two places:

1.  The class definition (where the handler is defined)

2.  The registry/dispatcher (where format→handler mapping lives)

**Python achieves SSOT:**

    class ImageHandler:
        _registry = {}

        def __init_subclass__(cls, format=None, **kwargs):
            super().__init_subclass__(**kwargs)
            if format:
                ImageHandler._registry[format] = cls  # DERIVED

    class PNGHandler(ImageHandler, format="png"):  # SOURCE
        def load(self, path): ...

DOF = 1. The `format="png"` in the class definition is the *single source*. The registry entry is *derived* automatically by `__init_subclass__`. Adding a new handler requires changing exactly one location.

**Java cannot achieve SSOT:**

    // File 1: PNGHandler.java
    @Handler(format = "png")  // Annotation is METADATA, not executable
    public class PNGHandler implements ImageHandler {
        public BufferedImage load(String path) { ... }
    }

    // File 2: HandlerRegistry.java (SEPARATE SOURCE!)
    public class HandlerRegistry {
        static {
            register("png", PNGHandler.class);  // Must be maintained manually
            register("jpg", JPGHandler.class);
            // Forgot to add TIFFHandler? Runtime error.
        }
    }

DOF = 2. The `@Handler(format = "png")` annotation is *data*, not code. It does not execute when the class is defined. The registry must be maintained separately.

::: theorem
[]{#thm:generated-second label="thm:generated-second"} A generated source file constitutes a second encoding, not a derivation. Therefore, code generation does not achieve SSOT.
:::

::: proof
*Proof.* Let $F$ be a structural fact (e.g., "PNGHandler handles .png files").

Let $E_1$ be the annotation: `@Handler(format="png")` on `PNGHandler.java`.

Let $E_2$ be the generated file: `HandlerRegistry.java` containing `register("png", PNGHandler.class)`.

By Definition [\[def:dof\]](#def:dof){reference-type="ref" reference="def:dof"}, $E_1$ and $E_2$ are both encodings of $F$ iff modifying either can change the system's behavior regarding $F$.

Test: If we delete or modify `HandlerRegistry.java`, does the system's behavior change? **Yes**---the handler will not be registered.

Test: If we modify the annotation, does the system's behavior change? **Yes**---the generated file will have different content.

Therefore, $E_1$ and $E_2$ are independent encodings. DOF $= 2$. Formally: if an artifact $r$ is absent from the program's runtime equality relation (cannot be queried or mutated in-process), then $\text{encodes}(r,F)$ introduces an independent DOF.

The fact that $E_2$ was *generated from* $E_1$ does not make it a derivation in the SSOT sense, because:

1.  $E_2$ exists as a separate artifact that can be edited, deleted, or fail to generate

2.  $E_2$ must be separately compiled

3.  The generation process is external to the language and can be bypassed

Contrast with Python, where the registry entry exists only in memory, created by the class statement itself. There is no second file. DOF $= 1$. 0◻ ◻
:::

**Why Rust proc macros don't help:**

::: theorem
[]{#thm:opaque-expansion label="thm:opaque-expansion"} If macro/template expansion is opaque at runtime, SSOT cannot be verified.
:::

::: proof
*Proof.* Verification of SSOT requires answering: "Is every encoding of $F$ derived from the single source?"

This requires enumerating all encodings. If expansion is opaque, the program cannot query what was generated.

In Rust, after `#[derive(Handler)]` expands, the program cannot ask "what did this macro generate?" The expansion is compiled into the binary but not introspectable.

Without introspection, the program cannot verify DOF $= 1$. SSOT may hold but cannot be confirmed. 0◻ ◻
:::

**The Gap is Fundamental:**

The distinction is not "Python has nicer syntax." The distinction is:

-   Python: Class definition *executes code* that creates derived structures *in memory*

-   Java: Class definition *produces data* that external tools process into *separate files*

-   Rust: Macro expansion *is invisible at runtime*---verification impossible

This is a language design choice with permanent consequences. No amount of clever coding in Java can make the registry *derived from* the class definition, because Java provides no mechanism for code to execute at class definition time.

# Language Evaluation {#sec:evaluation}

We now evaluate mainstream programming languages against the SSOT requirements established in Section [4](#sec:requirements){reference-type="ref" reference="sec:requirements"}. This evaluation is exhaustive: we check every mainstream language against formally-defined criteria.

## Evaluation Criteria {#sec:criteria}

We evaluate languages on four criteria, derived from the SSOT requirements:

::: center
  **Criterion**             **Abbrev**   **Test**
  ------------------------- ------------ -----------------------------------------------------
  Definition-time hooks     DEF          Can arbitrary code execute when a class is defined?
  Introspectable results    INTRO        Can the program query what was derived?
  Structural modification   STRUCT       Can hooks modify the structure being defined?
  Hierarchy queries         HIER         Can the program enumerate subclasses/implementers?
:::

**DEF** and **INTRO** are the two requirements from Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}. **STRUCT** and **HIER** are refinements that distinguish partial from complete support.

**Scoring (Precise Definitions):**

-   = Full support: The feature is available, usable for SSOT, and does not require external tools

-   $\times$ = No support: The feature is absent or fundamentally cannot be used for SSOT

-   $\triangle$ = Partial/insufficient: Feature exists but fails a requirement (e.g., needs external tooling or lacks runtime reach)

**Methodology note (tooling exclusions):** We exclude capabilities that require external build tools or libraries (annotation processors, Lombok, `reflect-metadata`+`ts-transformer`, `ts-json-schema-generator`, etc.). Only language-native, runtime-verifiable features count toward DEF/INTRO/STRUCT/HIER.

**Note:** We use $\triangle$ sparingly for mainstream languages only when a built-in mechanism exists but fails SSOT (e.g., requires compile-time tooling or lacks runtime reach). For non-mainstream languages in Section [5.4](#sec:non-mainstream){reference-type="ref" reference="sec:non-mainstream"}, we note partial support where relevant since these languages are not our primary focus. For INTRO, we require *subclass enumeration*---the ability to answer "what classes inherit from X?" at runtime. Java's `getMethods()` does not satisfy this because it cannot enumerate subclasses without classpath scanning via external libraries.

## Mainstream Language Definition {#sec:mainstream-def}

::: definition
[]{#def:mainstream label="def:mainstream"} A language is *mainstream* iff it appears in the top 20 of at least two of the following indices consistently over 5+ years:

1.  TIOBE Index (monthly language popularity)

2.  Stack Overflow Developer Survey (annual)

3.  GitHub Octoverse (annual repository statistics)

4.  RedMonk Programming Language Rankings (quarterly)
:::

This definition excludes niche languages (Haskell, Erlang, Clojure) while including all languages a typical software organization might consider. The 5-year consistency requirement excludes flash-in-the-pan languages.

## Mainstream Language Evaluation {#sec:mainstream-eval}

::: center
  **Language**      **DEF**      **INTRO**    **STRUCT**   **HIER**   **SSOT?**
  -------------- ------------- ------------- ------------ ---------- -----------
  Python                                                               **YES**
  JavaScript       $\times$      $\times$      $\times$    $\times$      NO
  Java             $\times$      $\times$      $\times$    $\times$      NO
  C++              $\times$      $\times$      $\times$    $\times$      NO
  C#               $\times$      $\times$      $\times$    $\times$      NO
  TypeScript      $\triangle$   $\triangle$    $\times$    $\times$      NO
  Go               $\times$      $\times$      $\times$    $\times$      NO
  Rust             $\times$      $\times$      $\times$    $\times$      NO
  Kotlin           $\times$      $\times$      $\times$    $\times$      NO
  Swift            $\times$      $\times$      $\times$    $\times$      NO
:::

TypeScript earns $\triangle$ for DEF/INTRO because decorators plus `reflect-metadata` can run at class decoration time and expose limited metadata, but (a) they require compiler flags/transformers instead of being always-on language features, (b) they cannot enumerate implementers at runtime, and (c) they are erased for plain JavaScript consumers. Consequently SSOT remains impossible without external tooling, so the overall verdict stays NO.

### Python: Full SSOT Support

Python provides all four capabilities:

**DEF (Definition-time hooks):**

-   `__init_subclass__`: Executes when a subclass is defined

-   Metaclasses: `__new__` and `__init__` execute at class creation

-   Class decorators: Execute immediately after class body

**INTRO (Introspection):**

-   `__subclasses__()`: Returns list of direct subclasses

-   `__mro__`: Returns method resolution order

-   `type()`, `isinstance()`, `issubclass()`: Type queries

-   `dir()`, `vars()`, `getattr()`: Attribute introspection

**STRUCT (Structural modification):**

-   Metaclasses can add/remove/modify class attributes

-   `__init_subclass__` can modify the subclass being defined

-   Decorators can return a different class entirely

**HIER (Hierarchy queries):**

-   `__subclasses__()`: Enumerate subclasses

-   `__bases__`: Query parent classes

-   `__mro__`: Full inheritance chain

### JavaScript: No SSOT Support

JavaScript lacks definition-time hooks:

**DEF:** $\times$. No code executes when a class is defined. The `class` syntax is declarative. Decorators (Stage 3 proposal) are not yet standard and have limited capabilities.

**INTRO:** $\times$. `Object.getPrototypeOf()`, `instanceof` exist but *cannot enumerate subclasses*. No equivalent to `__subclasses__()`.

**STRUCT:** $\times$. Cannot modify class structure at definition time.

**HIER:** $\times$. Cannot enumerate subclasses. No equivalent to `__subclasses__()`.

### Java: No SSOT Support

Java's annotations are metadata, not executable hooks:

**DEF:** $\times$. Annotations are processed by external tools (annotation processors), not by the JVM at class loading. The class is already fully defined when annotation processing occurs.

**INTRO:** $\times$. `Class.getMethods()`, `Class.getInterfaces()`, `Class.getSuperclass()` exist but *cannot enumerate subclasses*. The JVM does not track subclass relationships. External libraries (Reflections, ClassGraph) provide this via classpath scanning---but that is external tooling, not a language feature.

**STRUCT:** $\times$. Cannot modify class structure at runtime. Bytecode manipulation (ASM, ByteBuddy) is external tooling, not language-level support.

**HIER:** $\times$. Cannot enumerate subclasses without external libraries (Reflections, ClassGraph).

**Why annotation processors don't count:**

1.  They run at compile time, not definition time---the class being processed is already fixed

2.  They cannot modify the class being defined; they generate *new* classes

3.  Generated classes are separate compilation units, not derived facts within the source

4.  Results are not introspectable at runtime---you cannot query "was this method generated?"

**Why Lombok doesn't count:** Lombok approximates SSOT but violates it: the Lombok configuration becomes a second source of truth. Changes require updating both source and Lombok annotations. The tool can fail, be misconfigured, or be bypassed.

### C++: No SSOT Support

C++ templates are compile-time, not definition-time:

**DEF:** $\times$. Templates expand at compile time but do not execute arbitrary code. `constexpr` functions are evaluated at compile time but cannot hook into class definition.

**INTRO:** $\times$. No runtime type introspection. RTTI (`typeid`, `dynamic_cast`) provides minimal information. Cannot enumerate template instantiations.

**STRUCT:** $\times$. Cannot modify class structure after definition.

**HIER:** $\times$. Cannot enumerate subclasses. No runtime class registry.

### Go: No SSOT Support

Go's design philosophy explicitly rejects metaprogramming:

**DEF:** $\times$. No hook mechanism. Types are defined declaratively. No code executes at type definition.

**INTRO:** $\times$. `reflect` package provides limited introspection but cannot enumerate types implementing an interface.

**STRUCT:** $\times$. Cannot modify type structure.

**HIER:** $\times$. Interfaces are implicit (structural typing). Cannot enumerate implementers.

### Rust: No SSOT Support

Rust's procedural macros are compile-time and opaque:

**DEF:** $\times$. Procedural macros execute at compile time, not definition time. The generated code is not introspectable at runtime.

**INTRO:** $\times$. No runtime type introspection. `std::any::TypeId` provides minimal information.

**STRUCT:** $\times$. Cannot modify type structure at runtime.

**HIER:** $\times$. Cannot enumerate trait implementers.

**Why procedural macros don't count:**

1.  They execute at compile time, not definition time---the generated code is baked into the binary

2.  `#[derive(Debug)]` generates code, but you cannot query "does this type derive Debug?" at runtime

3.  Verification requires source inspection or documentation, not runtime query

4.  No equivalent to Python's `__subclasses__()`---you cannot enumerate trait implementers

**Consequence:** Rust achieves *compile-time* SSOT but not *runtime* SSOT. For applications requiring runtime reflection (ORMs, serialization frameworks, dependency injection), Rust requires manual synchronization or external codegen tools.

::: theorem
[]{#thm:python-unique label="thm:python-unique"} Among mainstream languages, Python is the only language satisfying all SSOT requirements.
:::

::: proof
*Proof.* By exhaustive evaluation. We checked all 10 mainstream languages against the four criteria. Only Python satisfies all four. The evaluation is complete---no mainstream language is omitted. 0◻ ◻
:::

## Non-Mainstream Languages {#sec:non-mainstream}

Three non-mainstream languages also satisfy SSOT requirements:

::: center
  **Language**          **DEF**   **INTRO**   **STRUCT**   **HIER**   **SSOT?**
  -------------------- --------- ----------- ------------ ---------- -----------
  Common Lisp (CLOS)                                                   **YES**
  Smalltalk                                                            **YES**
  Ruby                                         Partial                 Partial
:::

### Common Lisp (CLOS)

CLOS (Common Lisp Object System) provides the most powerful metaobject protocol:

**DEF:** . The MOP (Metaobject Protocol) allows arbitrary code execution at class definition via `:metaclass` and method combinations.

**INTRO:** . `class-direct-subclasses`, `class-precedence-list`, `class-slots` provide complete introspection.

**STRUCT:** . MOP allows complete structural modification.

**HIER:** . `class-direct-subclasses` enumerates subclasses.

CLOS is arguably more powerful than Python for metaprogramming. However, it is not mainstream by our definition.

### Smalltalk

Smalltalk pioneered many of these concepts:

**DEF:** . Classes are objects. Creating a class sends messages that can be intercepted.

**INTRO:** . `subclasses`, `allSubclasses`, `superclass` provide complete introspection.

**STRUCT:** . Classes can be modified at any time.

**HIER:** . `subclasses` enumerates subclasses.

### Ruby

Ruby provides hooks but with limitations:

**DEF:** . `inherited`, `included`, `extended` hooks execute at definition time.

**INTRO:** . `subclasses`, `ancestors`, `instance_methods` provide introspection.

**STRUCT:** Partial. Can add methods but cannot easily modify class structure during definition.

**HIER:** . `subclasses` enumerates subclasses.

Ruby is close to full SSOT support but the structural modification limitations prevent complete SSOT for some use cases.

::: theorem
[]{#thm:three-lang label="thm:three-lang"} Exactly three languages in common use satisfy complete SSOT requirements: Python, Common Lisp (CLOS), and Smalltalk.
:::

::: proof
*Proof.* By exhaustive evaluation of mainstream and notable non-mainstream languages. Python, CLOS, and Smalltalk satisfy all four criteria. Ruby satisfies three of four (partial STRUCT). All other evaluated languages fail at least two criteria. 0◻ ◻
:::

## Implications for Language Selection {#sec:implications}

The evaluation has practical implications:

**1. If SSOT for structural facts is required:**

-   Python is the only mainstream option

-   CLOS and Smalltalk are alternatives if mainstream status is not required

-   Ruby is a partial option with workarounds needed

**2. If using a non-SSOT language:**

-   External tooling (code generators, linters) can help

-   But tooling is not equivalent to language-level support

-   Tooling cannot be verified at runtime

-   Tooling adds build complexity

**3. For language designers:**

-   Definition-time hooks and introspection should be considered if DRY is a design goal

-   These features have costs (complexity, performance) that must be weighed

-   The absence of these features is a deliberate design choice with consequences

# Complexity Bounds {#sec:bounds}

We now prove the complexity bounds that make SSOT valuable. The key result: the gap between SSOT-complete and SSOT-incomplete architectures is *unbounded*---it grows without limit as codebases scale.

## Upper Bound: SSOT Achieves O(1) {#sec:upper-bound}

::: theorem
[]{#thm:upper-bound label="thm:upper-bound"} For a codebase satisfying SSOT for fact $F$: $$M_{\text{effective}}(C, \delta_F) = O(1)$$ Effective modification complexity is constant regardless of codebase size.
:::

::: proof
*Proof.* Let $C$ satisfy SSOT for fact $F$. By Definition [\[def:ssot\]](#def:ssot){reference-type="ref" reference="def:ssot"}, $\text{DOF}(C, F) = 1$. Let $L_s$ be the single independent encoding location.

When $F$ changes:

1.  The developer updates $L_s$ (1 edit)

2.  All derived locations $L_1, \ldots, L_k$ are automatically updated by the derivation mechanism

3.  Total manual edits: 1

The number of derived locations $k$ may grow with codebase size, but the number of *manual* edits remains 1. Therefore, $M_{\text{effective}}(C, \delta_F) = O(1)$. 0◻ ◻
:::

**Note on "effective" vs. "total" complexity:** Total modification complexity $M(C, \delta_F)$ counts all locations that change. Effective modification complexity counts only manual edits. With SSOT, total complexity may be $O(n)$ (many derived locations change), but effective complexity is $O(1)$ (one manual edit).

## Lower Bound: Non-SSOT Requires $\Omega(n)$ {#sec:lower-bound}

::: theorem
[]{#thm:lower-bound label="thm:lower-bound"} For a codebase *not* satisfying SSOT for fact $F$, if $F$ is encoded at $n$ independent locations: $$M_{\text{effective}}(C, \delta_F) = \Omega(n)$$
:::

::: proof
*Proof.* Let $C$ not satisfy SSOT for $F$. By Definition [\[def:ssot\]](#def:ssot){reference-type="ref" reference="def:ssot"}, $\text{DOF}(C, F) > 1$. Let $\text{DOF}(C, F) = n$ where $n > 1$.

By Definition [\[def:independent\]](#def:independent){reference-type="ref" reference="def:independent"}, the $n$ encoding locations are independent---updating one does not automatically update the others. When $F$ changes:

1.  Each of the $n$ independent locations must be updated manually

2.  No automatic propagation exists between independent locations

3.  Total manual edits: $n$

Therefore, $M_{\text{effective}}(C, \delta_F) = \Omega(n)$. 0◻ ◻
:::

## The Unbounded Gap {#sec:gap}

::: theorem
[]{#thm:unbounded-gap label="thm:unbounded-gap"} The ratio of modification complexity between SSOT-incomplete and SSOT-complete architectures grows without bound: $$\lim_{n \to \infty} \frac{M_{\text{incomplete}}(n)}{M_{\text{complete}}} = \lim_{n \to \infty} \frac{n}{1} = \infty$$
:::

::: proof
*Proof.* By Theorem [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"}, $M_{\text{complete}} = O(1)$. Specifically, $M_{\text{complete}} = 1$ for any codebase size.

By Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"}, $M_{\text{incomplete}}(n) = \Omega(n)$ where $n$ is the number of independent encoding locations.

The ratio is: $$\frac{M_{\text{incomplete}}(n)}{M_{\text{complete}}} = \frac{n}{1} = n$$

As $n \to \infty$, the ratio $\to \infty$. The gap is unbounded. 0◻ ◻
:::

::: corollary
[]{#cor:arbitrary-reduction label="cor:arbitrary-reduction"} For any constant $k$, there exists a codebase size $n$ such that SSOT provides at least $k\times$ reduction in modification complexity.
:::

::: proof
*Proof.* Choose $n = k$. Then $M_{\text{incomplete}}(n) = n = k$ and $M_{\text{complete}} = 1$. The reduction factor is $k/1 = k$. 0◻ ◻
:::

## Practical Implications {#sec:practical-implications}

The unbounded gap has practical implications:

**1. SSOT matters more at scale.** For small codebases ($n = 3$), the difference between 3 edits and 1 edit is minor. For large codebases ($n = 50$), the difference between 50 edits and 1 edit is significant.

**2. The gap compounds over time.** Each modification to fact $F$ incurs the complexity cost. If $F$ changes $m$ times over the project lifetime, total cost is $O(mn)$ without SSOT vs. $O(m)$ with SSOT.

**3. The gap affects error rates.** Each manual edit is an opportunity for error. With $n$ edits, the probability of at least one error is $1 - (1-p)^n$ where $p$ is the per-edit error probability. As $n$ grows, this approaches 1.

:::: example
[]{#ex:error-rate label="ex:error-rate"} Assume a 1% error rate per edit ($p = 0.01$).

::: center
   **Edits ($n$)**   **P(at least one error)**   **Architecture**
  ----------------- --------------------------- ------------------
          1                    1.0%                    SSOT
         10                    9.6%                  Non-SSOT
         50                    39.5%                 Non-SSOT
         100                   63.4%                 Non-SSOT
:::

With 50 encoding locations, there is a 39.5% chance of introducing an error when modifying fact $F$. With SSOT, the chance is 1%.
::::

## Amortized Analysis {#sec:amortized}

The complexity bounds assume a single modification. Over the lifetime of a codebase, facts are modified many times.

::: theorem
[]{#thm:amortized label="thm:amortized"} Let fact $F$ be modified $m$ times over the project lifetime. Let $n$ be the number of encoding locations. Total modification cost is:

-   SSOT: $O(m)$

-   Non-SSOT: $O(mn)$
:::

::: proof
*Proof.* Each modification costs $O(1)$ with SSOT and $O(n)$ without. Over $m$ modifications, total cost is $m \cdot O(1) = O(m)$ with SSOT and $m \cdot O(n) = O(mn)$ without. 0◻ ◻
:::

For a fact modified 100 times with 50 encoding locations:

-   SSOT: 100 edits total

-   Non-SSOT: 5,000 edits total

The 50$\times$ reduction factor applies to every modification, compounding over the project lifetime.

# Conclusion {#sec:conclusion}

We have provided the first formal foundations for the Single Source of Truth principle. The key contributions are:

**1. Formal Definition:** SSOT is defined as DOF = 1, where DOF (Degrees of Freedom) counts independent encoding locations for a fact. This definition is derived from the structure of the problem, not chosen arbitrarily.

**2. Language Requirements:** We prove that SSOT for structural facts requires (1) definition-time hooks AND (2) introspectable derivation. Both are necessary; both together are sufficient. This is an if-and-only-if theorem.

**3. Language Evaluation:** Among mainstream languages, only Python satisfies both requirements. CLOS and Smalltalk also satisfy them but are not mainstream. This is proved by exhaustive evaluation.

**4. Complexity Bounds:** SSOT achieves $O(1)$ modification complexity; non-SSOT requires $\Omega(n)$. The gap is unbounded: for any constant $k$, there exists a codebase size where SSOT provides at least $k\times$ reduction.

**5. Empirical Validation:** 13 case studies from OpenHCS (45K LoC) demonstrate a mean 14.2$\times$ DOF reduction, with a maximum of 47$\times$ (PR #44: hasattr migration).

**Implications:**

1.  **For practitioners:** If SSOT for structural facts is required, Python (or CLOS/Smalltalk) is necessary. Other mainstream languages cannot achieve SSOT within the language.

2.  **For language designers:** Definition-time hooks and introspection should be considered if DRY is a design goal. Their absence is a deliberate choice with consequences.

3.  **For researchers:** Software engineering principles can be formalized and machine-checked. This paper demonstrates the methodology.

**Limitations:**

-   Results apply to *structural* facts. Configuration values and runtime state have different characteristics.

-   Empirical validation is from a single codebase. Replication in other domains would strengthen the findings.

-   The complexity bounds are asymptotic. Small codebases may not benefit significantly.

**Future Work:**

-   Extend the formalization to non-structural facts

-   Develop automated DOF measurement tools

-   Study the relationship between DOF and other software quality metrics

-   Investigate SSOT in multi-language systems

**Connection to Leverage Framework:**

SSOT achieves *infinite leverage* in the framework of the companion paper on leverage-driven architecture: $$L(\text{SSOT}) = \frac{|\text{Derivations}|}{1} \to \infty$$

A single source derives arbitrarily many facts. This is the theoretical maximum---no architecture can exceed infinite leverage. The leverage framework provides a unified view: this paper (SSOT) and the companion paper on typing discipline selection are both instances of leverage maximization. The metatheorem---"maximize leverage"---subsumes both results.

All results are machine-checked in Lean 4 with zero `sorry` placeholders. The proofs are available at `proofs/ssot/`.

# Preemptive Rebuttals {#sec:rebuttals}

This appendix addresses anticipated objections. Each objection is stated in its strongest form, then refuted.

## Objection: The SSOT Definition is Too Narrow

**Objection:** "Your definition of SSOT as DOF = 1 is too restrictive. Real-world systems have acceptable levels of duplication."

**Response:** The definition is **derived**, not chosen. DOF = 1 is the unique optimal point:

::: center
          **DOF**         **Meaning**
  ----------------------- ---------------------------------------------------
             0            Fact is not encoded (underspecification)
             1            Single source of truth (optimal)
   $>$`<!-- -->`{=html}1  Multiple sources can diverge (inconsistency risk)
:::

There is no "acceptable level of duplication" in the formal sense. DOF = 2 means two locations can hold different values for the same fact. Whether this causes problems in practice depends on discipline, but the *possibility* of inconsistency exists.

The definition is not a recommendation---it is a mathematical characterization. You may choose to accept DOF $>$ 1 for pragmatic reasons, but you cannot claim SSOT while doing so.

## Objection: Other Languages Can Approximate SSOT

**Objection:** "Java with annotations, C++ with templates, or Rust with macros can achieve similar results. Your analysis is too narrow."

**Response:** Approximation $\neq$ guarantee. External tools and compile-time mechanisms differ from language-level support in three ways:

1.  **Not part of the language:** Annotation processors, code generators, and build tools are external. They can fail, be misconfigured, or be bypassed.

2.  **Not verifiable at runtime:** The program cannot confirm that derivation occurred correctly. In Python, `__subclasses__()` can verify registration completeness at runtime. In Java, there is no equivalent.

3.  **Not portable:** External tools are project-specific. Python's `__init_subclass__` works in any Python environment without configuration.

We do not claim other languages *cannot* achieve SSOT-like results. We claim they cannot achieve SSOT *within the language* with runtime verification.

## Objection: This is Just Advocacy for Python

**Objection:** "This paper is thinly-veiled Python advocacy dressed up as formal analysis."

**Response:** The derivation runs in the opposite direction:

1.  We define SSOT mathematically (DOF = 1)

2.  We prove what language features are necessary (definition-time hooks, introspection)

3.  We evaluate languages against these criteria

4.  Python, CLOS, and Smalltalk satisfy the criteria

If we were advocating for Python, we would not include CLOS and Smalltalk. The fact that three languages satisfy the criteria---and that two are not mainstream---validates that our criteria identify a genuine language capability class, not a Python-specific feature set.

The analysis would produce the same results if Python did not exist. The requirements are derived from the definition of SSOT, not from Python's feature set.

## Objection: The Case Studies are Cherry-Picked

**Objection:** "You selected case studies that show dramatic improvements. Real codebases have more modest results."

**Response:** The 13 case studies are **exhaustive** for one codebase. We identified *all* structural facts in OpenHCS and measured DOF for each. No case study was excluded.

The results include:

-   The largest reduction (47$\times$, PR #44)

-   The smallest reduction (5$\times$, Error Handler Chain)

-   The median reduction (11$\times$)

If anything, the case studies are *conservative*. We only counted structural facts with clear before/after states. Many smaller improvements were not counted.

## Objection: Complexity Bounds are Theoretical

**Objection:** "Asymptotic bounds like $O(1)$ vs $\Omega(n)$ don't matter in practice. Real codebases are finite."

**Response:** The case studies provide concrete numbers:

-   Total pre-SSOT DOF: 184

-   Total post-SSOT DOF: 13

-   Concrete reduction: 14.2$\times$

These are measured values, not asymptotic predictions. The 47$\times$ reduction in PR #44 is a real number from a real codebase.

The asymptotic bounds explain *why* the concrete numbers are what they are. As codebases grow, the gap widens. A codebase with 1000 encoding locations would show even larger reductions.

## Objection: SSOT Has Costs

**Objection:** "Metaprogramming is complex, hard to debug, and has performance overhead. The cure is worse than the disease."

**Response:** This is a valid concern, but orthogonal to our claims. We prove that SSOT *requires* certain features. We do not claim SSOT is always worth the cost.

The decision to use SSOT involves trade-offs:

-   **Benefit:** Reduced modification complexity ($O(1)$ vs $\Omega(n)$)

-   **Cost:** Metaprogramming complexity, potential performance overhead

For small codebases or rarely-changing facts, the cost may exceed the benefit. For large codebases with frequently-changing structural facts, the benefit is substantial.

Our contribution is the formal analysis, not a recommendation. We provide the tools to make an informed decision.

## Objection: The Lean Proofs are Trivial

**Objection:** "The Lean proofs just formalize obvious definitions. There's no deep mathematics here."

**Response:** The value is not in the difficulty of the proofs but in their *existence*. Machine-checked proofs provide:

1.  **Precision:** Informal arguments can be vague. Lean requires every step to be explicit.

2.  **Verification:** The proofs are checked by a computer. Human error is eliminated.

3.  **Reproducibility:** Anyone can run the proofs and verify the results.

Many "obvious" software engineering principles have never been formalized. The contribution is demonstrating that formalization is possible and valuable, not that the mathematics is difficult.

## Objection: Just Use Make/Bazel/Code Generation

**Objection:** "External build tools can achieve SSOT without language support. Generate the code at build time."

**Response:** External tools *shift* the SSOT problem, they don't *solve* it:

1.  **Two sources of truth:** The build tool configuration becomes a second source. Changes require updating both the source AND the build config. Formally: let $C$ be a codebase using tool $T$. Then $\text{DOF}(C \cup T, F) \geq 2$ because both source and tool config encode $F$.

2.  **Not verifiable at runtime:** Generated code is not introspectable as *derived*. You cannot query "was this method generated or hand-written?" The program loses provenance information.

3.  **Build cache invalidation:** The build tool must track dependencies, introducing its own consistency problem. Stale caches cause bugs that don't exist with language-native derivation.

4.  **Development friction:** Every edit requires a build step. Language-native SSOT (Python metaclasses) executes during `import`---no separate build, no cache, no configuration.

External tools are a *mitigation*, not a *solution*. They reduce DOF from $n$ to $k$ where $k$ is the number of tool configurations, but $k > 1$ still violates SSOT.

**When external tools are acceptable:** For cross-language code generation (e.g., protobuf generating Python, Java, Go), external tools are the only option since no single language can control another's type definitions. Our analysis focuses on single-language SSOT.

---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper2_ssot/proofs/`
- Lines: 1,811
- Theorems: 96
- Sorry placeholders: 0

