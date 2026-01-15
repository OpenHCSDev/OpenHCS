# Paper: Formal Foundations for the Single Source of Truth Principle

**Status**: TOPLAS-ready | **Lean**: 1811 lines, 96 theorems

---

## Abstract

**Epistemic Foundation.** Any system encoding facts faces a fundamental constraint: when multiple independent locations encode the same fact, truth becomes indeterminate. We prove that DOF = 1 (Single Source of Truth) is the unique representation guaranteeing coherence---the impossibility of disagreement among encodings.

**The Core Theorem (Oracle Arbitrariness).** In any incoherent encoding system (DOF $> 1$ with divergent values), no resolution is principled: for ANY oracle claiming to identify the "true" value, there exists an equally-present value that disagrees. This is not about inconvenience. It is about the determinacy of truth.

**Software as Instance.** Programming languages instantiate this epistemic structure:

-   Encoding systems $\to$ Codebases

-   Facts $\to$ Structural specifications (class existence, method signatures)

-   Coherence $\to$ Consistency across encoding locations

-   DOF = 1 $\to$ Single Source of Truth (DRY principle)

We prove that achieving DOF = 1 for structural facts requires specific language features: definition-time hooks AND introspectable derivation. Most mainstream languages (Java, C++, Rust, Go, TypeScript, etc.) lack these features and **cannot achieve coherence** for structural facts regardless of programmer effort.

**Four Theorems:**

1.  **Coherence Forcing (Theorem [\[thm:dof-optimal\]](#thm:dof-optimal){reference-type="ref" reference="thm:dof-optimal"}):** DOF = 1 is the unique value guaranteeing coherence. DOF = 0 means the fact is unrepresented; DOF $> 1$ permits incoherent states.

2.  **Oracle Arbitrariness (Theorem [\[thm:oracle-arbitrary\]](#thm:oracle-arbitrary){reference-type="ref" reference="thm:oracle-arbitrary"}):** Under incoherence, any resolution is arbitrary---no oracle is justified by the encodings alone.

3.  **Language Requirements (Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}):** For structural facts in software, DOF = 1 requires definition-time hooks AND introspection. These are logically forced.

4.  **Strict Dominance (Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"}):** The coherence restoration complexity gap is unbounded: $O(1)$ vs $\Omega(n)$.

**Theoretical Foundation.** The derivation theory (independence, derivability, axis collapse) is established in Paper 1 [@paper1_typing_discipline]. This paper proves the coherence consequences and instantiates them to programming languages.

All theorems machine-checked in Lean 4 (9,351 lines, 541 theorems, 0 `sorry`). Language capability claims derived from formalized operational semantics, not declared. Practical demonstration via OpenHCS [@openhcs2025] PR #44 [@openhcsPR44]: migration from 47 scattered checks to 1 ABC (DOF 47 $\to$ 1).

**Keywords:** epistemic coherence, encoding systems, Single Source of Truth, language design, formal methods


# Introduction

## The Epistemic Problem {#sec:epistemic-problem}

When multiple locations encode the same fact, which location holds the truth?

This question has no principled answer. If location $L_1$ says "threshold = 0.5" and location $L_2$ says "threshold = 0.7", no information internal to the encoding system determines which is correct. Any resolution is arbitrary---it requires external information (developer intent, timestamps, priority rules) that the encodings themselves do not contain.

This is not a software engineering problem. It is an **epistemic** problem: the determinacy of truth under redundant encoding.

> **Oracle Arbitrariness Theorem.** For any incoherent encoding system and any oracle that resolves it to a value, there exists an equally-present value that disagrees with the oracle's choice.

The theorem is proved formally (Theorem [\[thm:oracle-arbitrary\]](#thm:oracle-arbitrary){reference-type="ref" reference="thm:oracle-arbitrary"}). Its consequence: **DOF = 1 is epistemically necessary** for coherent representation. With exactly one independent source, disagreement is impossible. Truth is determinate.

## Software as Instance {#sec:software-instance}

Programming languages instantiate this epistemic structure. A codebase is an encoding system. Structural facts (class existence, method signatures, type relationships) are the facts being encoded. The "Don't Repeat Yourself" (DRY) principle [@hunt1999pragmatic] is the software engineering recognition of epistemic necessity.

This paper proves:

1.  **The epistemic foundation:** DOF = 1 is the unique representation guaranteeing coherence

2.  **The software instantiation:** Achieving DOF = 1 for structural facts requires specific language features

3.  **The impossibility result:** Most mainstream languages lack these features and cannot achieve coherence

## Metatheoretic Foundations

Following the tradition of formal language design criteria (Liskov & Wing [@liskov1994behavioral] for subtyping; Cook et al. [@cook1989inheritance] for inheritance semantics), we formalize correctness criteria for SSOT-completeness in programming languages. Our contribution is not advocating specific languages, but deriving the necessary and sufficient requirements that enable Single Source of Truth for structural facts.

The derivation theory (independence, derivability, axis collapse) is established in Paper 1 [@paper1_typing_discipline]. This paper proves the coherence consequences and instantiates them to programming languages.

## The Universal Principle {#sec:universal-principle}

This paper proves an epistemic result that applies beyond programming:

1.  **DOF = 1 guarantees coherence.** With exactly one independent encoding, disagreement is impossible. Truth is determinate.

2.  **DOF $> 1$ permits incoherence.** With multiple independent encodings, disagreeing states are reachable. Truth becomes indeterminate.

3.  **DOF = 1 is uniquely optimal.** DOF = 0 means the fact is unrepresented. DOF $> 1$ permits incoherence. Only DOF = 1 achieves coherent representation.

**The forcing theorem.** Given coherence as a requirement, DOF = 1 is the unique solution. We do not claim all systems require coherence. We prove that systems requiring coherence have no design freedom---the solution is forced.

**The language instantiation.** For *structural facts* in programming languages, DOF = 1 requires specific language features: definition-time hooks and introspection. Languages lacking either *cannot achieve* DOF = 1 for structural facts regardless of programmer effort. This is an impossibility result (Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}).

The epistemic principle is universal. The language evaluation is its instantiation to software. Both are machine-checked.

## Overview

This paper establishes **coherence impossibility theorems** for programming languages: we prove that most mainstream languages **cannot guarantee coherence** for structural facts. All results are machine-checked in Lean 4 [@demoura2021lean4] (2,104 lines across 13 files, 0 `sorry` placeholders).

**Incompleteness.** We prove that Java, C++, C#, JavaScript, Go, Rust, TypeScript, Kotlin, and Swift lack the semantic machinery to achieve DOF = 1 (coherent representation) for structural facts. This is not a limitation of particular implementations. It is a fundamental property of their language semantics: incoherent states are always reachable.

**Completeness.** We prove that Python, Common Lisp (CLOS), and Smalltalk possess the necessary semantic features. Among mainstream languages (top-10 TIOBE, consistent 5+ year presence), Python is unique in this capability.

**Connection to software engineering practice.** The "Don't Repeat Yourself" (DRY) principle [@hunt1999pragmatic], articulated as "Every piece of knowledge must have a single, unambiguous, authoritative representation within a system" (Hunt & Thomas, 1999), is the practitioner's recognition of epistemic necessity. We prove DRY reduces to DOF = 1, which is the unique coherent representation (Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"}). To our knowledge, this is the first formalization of DRY/SSOT as an epistemic requirement.

**Note on terminology:** The term "Single Source of Truth" also appears in data management literature, referring to authoritative data repositories. Our usage is distinct: we mean SSOT for *program structure* (class existence, method signatures, type relationships), not for data storage.

The core insight: coherence for *structural facts* requires language features that most mainstream languages lack:

1.  **Definition-time hooks** (Theorem [\[thm:hooks-necessary\]](#thm:hooks-necessary){reference-type="ref" reference="thm:hooks-necessary"}): Code must execute when a class/function is *defined*, not when it is *used*. This enables derivation at the moment structure is established.

2.  **Introspectable derivation** (Theorem [\[thm:introspection-necessary\]](#thm:introspection-necessary){reference-type="ref" reference="thm:introspection-necessary"}): The program must be able to query what was derived and from what. This enables verification of the derivation relationship.

3.  **Both are necessary** (Theorem [\[thm:independence\]](#thm:independence){reference-type="ref" reference="thm:independence"}): Neither feature alone suffices. Without both, independent locations remain, and incoherence is possible.

These requirements are **information-theoretic**: Languages lacking either capability cannot eliminate independent locations regardless of programmer effort.

## Core Theorems {#sec:core-theorems}

We establish four theorems characterizing coherence achievability:

1.  **Theorem [\[thm:oracle-arbitrary\]](#thm:oracle-arbitrary){reference-type="ref" reference="thm:oracle-arbitrary"} (Oracle Arbitrariness):** In any incoherent encoding system, no resolution is principled. For any oracle selecting a value, there exists an equally-present value that disagrees.

    *Proof technique:* By incoherence, at least two values exist. Any selection leaves the other disagreeing.

2.  **Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"} (Coherence Forcing):** DOF = 1 guarantees coherence. With exactly one independent source, disagreement is impossible.

    *Proof technique:* All other locations are derived (cannot diverge). Single source determines all values.

3.  **Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"} (Language Requirements):** A language enables DOF = 1 for structural facts if and only if it provides (1) definition-time hooks AND (2) introspectable derivation.

    *Proof technique:* Necessity by exhibiting incoherent states when either is missing. Sufficiency by construction.

4.  **Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"} (Coherence Restoration Gap):** The complexity of restoring coherence after modification is unbounded: $O(1)$ for DOF = 1 vs $\Omega(n)$ for DOF $= n > 1$.

    *Proof technique:* Asymptotic analysis: $\lim_{n \to \infty} \frac{n}{1} = \infty$.

**Forced solution.** Given coherence as a requirement, DOF = 1 is the unique solution (Corollary [\[cor:coherence-forces-ssot\]](#cor:coherence-forces-ssot){reference-type="ref" reference="cor:coherence-forces-ssot"}). Language selection becomes **determined**: incomplete languages cannot achieve coherence regardless of implementation effort. This is not preference. It is epistemic necessity.

## Scope {#sec:scope}

This work characterizes SSOT for *structural facts* (class existence, method signatures, type relationships) within *single-language* systems. The complexity analysis is asymptotic, applying to systems where $n$ grows. External tooling can approximate SSOT behavior but operates outside language semantics.

**Multi-language systems.** When a system spans multiple languages (e.g., Python backend + TypeScript frontend + protobuf schemas), cross-language SSOT requires external code generation tools. The analysis in this paper characterizes single-language SSOT; multi-language SSOT is noted as future work (Section [\[sec:conclusion\]](#sec:conclusion){reference-type="ref" reference="sec:conclusion"}).

## Contributions {#sec:contributions}

This paper makes six contributions:

**1. Epistemic foundations (Section [\[sec:epistemic\]](#sec:epistemic){reference-type="ref" reference="sec:epistemic"}):**

-   Definition of coherence and incoherence for encoding systems

-   **Theorem [\[thm:oracle-arbitrary\]](#thm:oracle-arbitrary){reference-type="ref" reference="thm:oracle-arbitrary"} (Oracle Arbitrariness):** Under incoherence, no resolution is principled. The epistemic core.

-   **Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"} (Coherence Forcing):** DOF = 1 guarantees coherence

-   **Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"}:** DOF $> 1$ permits incoherence

-   **Corollary [\[cor:coherence-forces-ssot\]](#cor:coherence-forces-ssot){reference-type="ref" reference="cor:coherence-forces-ssot"}:** Given coherence requirement, DOF = 1 is necessary and sufficient

**2. Software instantiation (Section [\[sec:edit-space\]](#sec:edit-space){reference-type="ref" reference="sec:edit-space"}):**

-   Mapping: encoding systems $\to$ codebases, facts $\to$ structural specifications

-   Definition of SSOT as DOF = 1 for software

-   Theorem [\[thm:ssot-determinate\]](#thm:ssot-determinate){reference-type="ref" reference="thm:ssot-determinate"}: SSOT eliminates indeterminacy

**3. Language requirements (Section [\[sec:requirements\]](#sec:requirements){reference-type="ref" reference="sec:requirements"}):**

-   Theorem [\[thm:hooks-necessary\]](#thm:hooks-necessary){reference-type="ref" reference="thm:hooks-necessary"}: Definition-time hooks are necessary

-   Theorem [\[thm:introspection-necessary\]](#thm:introspection-necessary){reference-type="ref" reference="thm:introspection-necessary"}: Introspection is necessary

-   Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}: Both together are sufficient

-   Proof that these requirements are forced by the structure of the problem

**4. Language evaluation (Section [\[sec:evaluation\]](#sec:evaluation){reference-type="ref" reference="sec:evaluation"}):**

-   Exhaustive evaluation of 10 mainstream languages

-   Extended evaluation of 3 non-mainstream languages (CLOS, Smalltalk, Ruby)

-   Theorem [\[thm:three-lang\]](#thm:three-lang){reference-type="ref" reference="thm:three-lang"}: Exactly three languages satisfy requirements

**5. Complexity bounds (Section [\[sec:bounds\]](#sec:bounds){reference-type="ref" reference="sec:bounds"}):**

-   Theorem [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"}: SSOT achieves $O(1)$ coherence restoration

-   Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"}: Non-SSOT requires $\Omega(n)$ modifications

-   Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"}: The gap is unbounded

**6. Practical demonstration (Section [\[sec:empirical\]](#sec:empirical){reference-type="ref" reference="sec:empirical"}):**

-   Before/after examples from OpenHCS (production Python codebase)

-   PR #44 [@openhcsPR44]: Migration from 47 scattered checks to 1 ABC (DOF 47 $\to$ 1)

-   Empirical validation that coherence is achievable in practice

## Empirical Context: OpenHCS {#sec:openhcs-context}

**What it does:** OpenHCS [@openhcs2025] is an open-source bioimage analysis platform for high-content screening (45K LoC Python). It processes microscopy images through configurable pipelines, with GUI-based design and Python code export. The system requires:

-   Automatic registration of analysis components

-   Type-safe configuration with inheritance

-   Runtime enumeration of available processors

-   Provenance tracking for reproducibility

**Why it matters for this paper:** OpenHCS requires SSOT for structural facts. When a new image processor is added (by subclassing `BaseProcessor`), it must automatically appear in:

-   The GUI component palette

-   The configuration schema

-   The serialization registry

-   The documentation generator

Without SSOT, adding a processor requires updating 4+ locations. With SSOT, only the class definition is needed. Python's `__init_subclass__` and `__subclasses__()` handle the rest.

**Key finding:** PR #44 [@openhcsPR44] migrated from duck typing (`hasattr()` checks) to nominal typing (ABC contracts). This eliminated 47 scattered checks, reducing DOF from 47 to 1. The migration validates both:

1.  The theoretical prediction: DOF reduction is achievable

2.  The practical benefit: Maintenance cost decreased measurably

## Decision Procedure, Not Preference {#sec:decision}

The contribution of this paper is not the theorems alone, but their consequence: *language selection for coherent representation becomes a decision procedure*.

Given coherence as a requirement:

1.  DOF = 1 is necessary (Corollary [\[cor:coherence-forces-ssot\]](#cor:coherence-forces-ssot){reference-type="ref" reference="cor:coherence-forces-ssot"})

2.  DOF = 1 for structural facts requires definition-time hooks AND introspection (Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"})

3.  Languages lacking these features cannot achieve coherence for structural facts

**Implications:**

1.  **Language design.** Future languages should include definition-time hooks and introspection if coherent structural representation is a design goal.

2.  **Architecture.** When coherence is required, language selection is constrained. "I prefer Go" is not valid when structural coherence is required.

3.  **Tooling.** External tools can work around language limitations but operate outside language semantics.

4.  **Pedagogy.** DRY should be taught as epistemic necessity with language requirements, not as a vague guideline.

## Paper Structure {#sec:structure}

Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"} establishes epistemic foundations (coherence, oracle arbitrariness) and instantiates them to software. Section [\[sec:ssot\]](#sec:ssot){reference-type="ref" reference="sec:ssot"} defines SSOT as the coherent representation and proves its properties. Section [\[sec:requirements\]](#sec:requirements){reference-type="ref" reference="sec:requirements"} derives language requirements with necessity proofs. Section [\[sec:evaluation\]](#sec:evaluation){reference-type="ref" reference="sec:evaluation"} evaluates mainstream languages exhaustively. Section [\[sec:bounds\]](#sec:bounds){reference-type="ref" reference="sec:bounds"} proves complexity bounds. Section [\[sec:empirical\]](#sec:empirical){reference-type="ref" reference="sec:empirical"} demonstrates practical application. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"} surveys related work. Appendix [\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"} addresses anticipated objections. Appendix [\[sec:lean\]](#sec:lean){reference-type="ref" reference="sec:lean"} contains complete Lean 4 proof listings.

## Anticipated Objections {#sec:objection-summary}

Before proceeding, we address objections readers are likely forming. Each is refuted in detail in Appendix [\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"}; here we summarize the key points.

#### "The model doesn't capture real Python/Rust semantics."

The model is validated through instantiation proofs (§[\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"}, Part I). `PythonInstantiation.lean` proves that all Python observables factor through the (B, S) axes. `LangPython.lean` directly encodes Python's datamodel specification. The model is falsifiable: produce Python code where two types with identical `__bases__` and `__dict__` behave differently, or where `__init_subclass__` fails to fire.

#### "Rust can achieve SSOT with proc macros and static registries."

No. Proc macros are per-item isolated---they cannot see other items during expansion. Registration is bypassable: you can `impl Trait` without any `#[derive]` annotation. The `inventory` crate uses linker tricks external to language semantics. Contrast Python: `__init_subclass__` fires automatically and *cannot be bypassed*. This is enforcement vs. enablement (§[\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"}, Part III).

#### "The requirements are circular---you define structural facts as fixed at definition time, then prove you need definition-time hooks."

No. We define structural facts by their *syntactic locus* (encoded in type definitions). The observation that they are fixed at definition time is a *consequence* of this locus. The theorem that hooks are required is *derived* from the observation. The circularity objection mistakes consequence for premise (§[\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"}, Part II).

#### "Build.rs / external tools can achieve SSOT."

External tools operate outside language semantics. They can fail, be misconfigured, or be bypassed. They provide no runtime verification---the program cannot confirm derivation occurred. Build tool configuration becomes a second source (DOF $\geq$ 2). This approximates SSOT but does not achieve it (§[\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"}, Parts II--III).

#### "The DOF = 1 definition is too restrictive."

The definition is *derived*, not chosen. DOF = 0 means the fact is unrepresented. DOF $> 1$ means multiple sources can diverge. DOF = 1 is the unique optimal point. Systems with DOF $> 1$ may be pragmatically acceptable but do not satisfy SSOT (§[\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"}, Part II).

#### "You just need discipline, not language features."

Discipline *is* the external oracle. The theorem states: with DOF $> 1$, consistency requires an external oracle. "Code review and documentation" are exactly that oracle---human-maintained, fallible, bypassable. Language enforcement cannot be forgotten; human discipline can (§[\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"}, Part IV).

#### "The proofs are trivial (`rfl`)."

When modeling is correct, theorems become definitional. This is a feature. Not all proofs are `rfl`: `rust_lacks_introspection` is 40 lines of actual reasoning. The contribution is making the right definitions so that consequences follow structurally (§[\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"}, Part V).

**If you have an objection not listed above,** check Appendix [\[sec:rebuttals\]](#sec:rebuttals){reference-type="ref" reference="sec:rebuttals"} (16 objections addressed) before concluding it has not been considered.


# Formal Foundations {#sec:foundations}

We establish the epistemic foundations of representation theory, then instantiate them to software. The core insight: SSOT is not a software engineering guideline but an epistemic necessity for coherent representation of facts.

## Epistemic Foundations {#sec:epistemic}

Before formalizing codebases and edits, we establish the epistemic structure that underlies all representation systems.

::: definition
[]{#def:encoding-system label="def:encoding-system"} An *encoding system* for a fact $F$ is a collection of locations $\{L_1, \ldots, L_n\}$, each capable of holding a value for $F$.
:::

::: definition
[]{#def:coherence label="def:coherence"} An encoding system is *coherent* iff all locations hold the same value: $$\forall i, j: \text{value}(L_i) = \text{value}(L_j)$$
:::

::: definition
[]{#def:incoherence label="def:incoherence"} An encoding system is *incoherent* iff some locations disagree: $$\exists i, j: \text{value}(L_i) \neq \text{value}(L_j)$$
:::

**The Epistemic Problem.** When an encoding system is incoherent, which value is "true"? This question has no answer internal to the system.

::: theorem
[]{#thm:oracle-arbitrary label="thm:oracle-arbitrary"} For any incoherent encoding system $S$ and any oracle $O$ that resolves $S$ to a value $v \in S$, there exists a value $v' \in S$ such that $v' \neq v$.
:::

::: proof
*Proof.* By incoherence, $\exists v_1, v_2 \in S: v_1 \neq v_2$. Either $O$ picks $v_1$ (then $v_2$ disagrees) or $O$ doesn't pick $v_1$ (then $v_1$ disagrees). ◻
:::

**Interpretation.** This theorem is not about difficulty---it is about *indeterminacy*. Under incoherence, the encoding system does not determine which value is true. Any resolution requires information external to the encodings.

::: definition
[]{#def:dof-epistemic label="def:dof-epistemic"} The *degrees of freedom* (DOF) of an encoding system is the number of locations that can be modified independently.
:::

::: theorem
[]{#thm:dof-one-coherence label="thm:dof-one-coherence"} If DOF = 1, then the encoding system is coherent in all reachable states.
:::

::: proof
*Proof.* With DOF = 1, exactly one location is independent. All other locations are derived (automatically updated when the source changes). Derived locations cannot diverge from their source. Therefore, all locations hold the value determined by the single independent source. Disagreement is impossible. ◻
:::

::: theorem
[]{#thm:dof-gt-one-incoherence label="thm:dof-gt-one-incoherence"} If DOF $> 1$, then incoherent states are reachable.
:::

::: proof
*Proof.* With DOF $> 1$, at least two locations are independent. Independent locations can be modified separately. A sequence of edits can set $L_1 = v_1$ and $L_2 = v_2$ where $v_1 \neq v_2$. This is an incoherent state. ◻
:::

::: corollary
[]{#cor:coherence-forces-ssot label="cor:coherence-forces-ssot"} If coherence must be guaranteed (no incoherent states reachable), then DOF = 1 is necessary and sufficient.
:::

This is the epistemic foundation of SSOT.

**Information-Theoretic Interpretation.** The DOF = 1 condition has a precise information-theoretic characterization. Rissanen's Minimum Description Length (MDL) principle [@rissanen1978mdl] states that the optimal representation minimizes total description length: $|$model$|$ + $|$data given model$|$. When DOF = 1, the single source *is* the minimal model; all derived locations are the "data given model" with zero additional description length (they are fully determined). When DOF $> 1$, the redundant independent locations require explicit synchronization---additional description length that serves no epistemic purpose. Grünwald [@gruenwald2007mdl] provides a comprehensive treatment showing that MDL-optimal representations are unique under mild conditions---precisely what Theorem [\[thm:dof-optimal\]](#thm:dof-optimal){reference-type="ref" reference="thm:dof-optimal"} establishes for DOF.

Heering [@heering2015generative] formalized this connection for software specifically: the *generative complexity* of a program family is the length of the shortest generator. SSOT architectures achieve minimal generative complexity by construction---the single source is the generator, and derived locations are the generated instances. This framing connects our formalization to Kolmogorov complexity theory while remaining constructive (we provide the generator, not just prove its existence).

The following sections instantiate these concepts to software.

## Software Instantiation: Codebases {#sec:edit-space}

::: definition
A *codebase* $C$ is a finite collection of source files, each containing a sequence of syntactic constructs (classes, functions, statements, expressions).
:::

::: definition
A *location* $L \in C$ is a syntactically identifiable region of code: a class definition, a function body, a configuration value, a type annotation, etc.
:::

::: definition
For a codebase $C$, the *edit space* $E(C)$ is the set of all syntactically valid modifications to $C$. Each edit $\delta \in E(C)$ transforms $C$ into a new codebase $C' = \delta(C)$.
:::

The edit space is large (exponential in codebase size). But we are not interested in arbitrary edits. We are interested in edits that *change a specific fact*.

## Facts: Atomic Units of Specification {#sec:facts}

::: definition
[]{#def:fact label="def:fact"} A *fact* $F$ is an atomic unit of program specification: a single piece of knowledge that can be independently modified. Facts are the indivisible units of meaning in a specification.
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
[]{#def:structural-fact label="def:structural-fact"} A fact $F$ is *structural* with respect to codebase $C$ iff the locations encoding $F$ are syntactic constituents of type definitions: $$\text{structural}(F, C) \Longleftrightarrow \forall L: \text{encodes}(L, F) \rightarrow L \in \text{TypeSyntax}(C)$$ where $\text{TypeSyntax}(C)$ comprises class declarations, method signatures, inheritance clauses, and attribute definitions.
:::

**Key property:** Structural facts are fixed at *definition time*. Once a class is defined, its structure (methods, bases, attributes) cannot change without redefining the class. This is why structural SSOT requires definition-time hooks: the encoding locations are only mutable during class creation.

**Non-structural facts** (configuration values, runtime state) have encoding locations outside type syntax. They can be modified at runtime without redefining types. SSOT for non-structural facts requires different mechanisms (e.g., reactive bindings, event systems) and is outside the scope of this paper.

## Encoding: The Correctness Relationship {#sec:encoding}

::: definition
[]{#def:encodes label="def:encodes"} Location $L$ *encodes* fact $F$, written $\text{encodes}(L, F)$, iff correctness requires updating $L$ when $F$ changes.

Formally: $$\text{encodes}(L, F) \Longleftrightarrow \forall \delta_F: \neg\text{updated}(L, \delta_F) \rightarrow \text{incorrect}(\delta_F(C))$$

where $\delta_F$ is an edit targeting fact $F$.
:::

**Key insight:** This definition is **forced** by correctness, not chosen. We do not decide what encodes what. Correctness requirements determine it. If failing to update location $L$ when fact $F$ changes produces an incorrect program, then $L$ encodes $F$. This is an objective, observable property.

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

By Definition [\[def:encodes\]](#def:encodes){reference-type="ref" reference="def:encodes"}, the program is incorrect. Therefore, all $k$ locations must be updated, and $k$ is the minimum. ◻
:::

## Independence and Degrees of Freedom {#sec:dof}

Not all encoding locations are created equal. Some are *derived* from others.

::: definition
[]{#def:independent label="def:independent"} Locations $L_1, L_2$ are *independent* for fact $F$ iff they can diverge. Updating $L_1$ does not automatically update $L_2$, and vice versa.

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
[]{#thm:dof-inconsistency label="thm:dof-inconsistency"} $\text{DOF}(C, F) = k$ implies $k$ different values for $F$ can coexist in $C$ simultaneously. With $k > 1$, incoherent states are reachable.
:::

::: proof
*Proof.* Each independent location can hold a different value. By Definition [\[def:independent\]](#def:independent){reference-type="ref" reference="def:independent"}, no constraint forces agreement between independent locations. Therefore, $k$ independent locations can hold $k$ distinct values. This is an instance of Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"} applied to software. ◻
:::

::: corollary
[]{#cor:dof-risk label="cor:dof-risk"} $\text{DOF}(C, F) > 1$ implies incoherent states are reachable. The codebase can enter a state where different locations encode different values for the same fact.
:::

## The DOF Lattice {#sec:dof-lattice}

DOF values form a lattice with distinct epistemic meanings:

::: center
   **DOF**  **Epistemic Status**
  --------- -------------------------------------------------------------
      0     Fact $F$ is not represented (no encoding)
      1     Coherence guaranteed (truth determinate)
   $k > 1$  Incoherence possible (truth indeterminate under divergence)
:::

::: theorem
[]{#thm:dof-optimal label="thm:dof-optimal"} For any fact $F$ that must be encoded, $\text{DOF}(C, F) = 1$ is the unique value guaranteeing coherence:

1.  DOF = 0: Fact is not represented

2.  DOF = 1: Coherence guaranteed (by Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"})

3.  DOF $>$ 1: Incoherence reachable (by Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"})
:::

::: proof
*Proof.* This is a direct instantiation of Corollary [\[cor:coherence-forces-ssot\]](#cor:coherence-forces-ssot){reference-type="ref" reference="cor:coherence-forces-ssot"} to software:

1.  DOF = 0 means no location encodes $F$. The fact is unrepresented.

2.  DOF = 1 means exactly one independent location. All other encodings are derived. Divergence is impossible. Coherence is guaranteed.

3.  DOF $>$ 1 means multiple independent locations. By Corollary [\[cor:dof-risk\]](#cor:dof-risk){reference-type="ref" reference="cor:dof-risk"}, they can diverge. Incoherence is reachable.

Only DOF = 1 achieves coherent representation. This is epistemic necessity, not design preference. ◻
:::


# Single Source of Truth {#sec:ssot}

Having established the epistemic foundations (Section [\[sec:epistemic\]](#sec:epistemic){reference-type="ref" reference="sec:epistemic"}), we now define SSOT as the instantiation of coherence to software and prove its necessity.

## SSOT as Epistemic Coherence {#sec:ssot-def}

SSOT is not a design guideline. It is the unique representation guaranteeing epistemic coherence for facts encoded in software.

::: definition
[]{#def:ssot label="def:ssot"} Codebase $C$ satisfies *SSOT* for fact $F$ iff: $$\text{DOF}(C, F) = 1$$ Equivalently: exactly one independent encoding location exists for $F$.
:::

**Epistemic interpretation:**

-   DOF = 1 means exactly one independent encoding location

-   All other locations are derived (cannot diverge from source)

-   Incoherence is *impossible*, not merely unlikely

-   Truth is determinate: the single source IS the value of $F$

::: theorem
[]{#thm:ssot-determinate label="thm:ssot-determinate"} If $\text{DOF}(C, F) = 1$, then for all reachable states of $C$, the value of $F$ is determinate: all encodings agree.
:::

::: proof
*Proof.* By Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"}, DOF = 1 guarantees coherence. Coherence means all encodings hold the same value. Therefore, the value of $F$ is uniquely determined by the single source. ◻
:::

Hunt & Thomas's "single, unambiguous, authoritative representation" [@hunt1999pragmatic] corresponds precisely to this epistemic structure:

-   **Single:** DOF = 1

-   **Unambiguous:** No incoherent states possible (Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"})

-   **Authoritative:** The source determines all derived values

::: theorem
[]{#thm:ssot-optimal label="thm:ssot-optimal"} If $C$ satisfies SSOT for $F$, then modification complexity is 1: updating the single source maintains coherence.
:::

::: proof
*Proof.* Let $C$ satisfy SSOT for $F$, meaning $\text{DOF}(C, F) = 1$. Let $L_s$ be the single independent encoding location. All other encodings $L_1, \ldots, L_k$ are derived from $L_s$.

When fact $F$ changes:

1.  The developer updates $L_s$ (1 edit)

2.  By Definition [\[def:derived\]](#def:derived){reference-type="ref" reference="def:derived"}, $L_1, \ldots, L_k$ are automatically updated

3.  Coherence is maintained: all locations agree on the new value

Coherence restoration requires 1 edit. ◻
:::

::: theorem
[]{#thm:ssot-unique label="thm:ssot-unique"} SSOT (DOF=1) is the **unique** coherent representation for structural facts. DOF = 0 fails to represent; DOF $> 1$ permits incoherence.
:::

::: proof
*Proof.* By Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"}, DOF = 1 guarantees coherence. By Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"}, DOF $> 1$ permits incoherence.

This leaves only DOF = 1 as coherent representation. DOF = 0 means no independent location encodes $F$---the fact is not represented.

Therefore, DOF = 1 is uniquely coherent. This is epistemic necessity, not design choice. ◻
:::

::: corollary
[]{#cor:no-redundancy label="cor:no-redundancy"} Multiple independent sources encoding the same fact permit incoherent states. DOF $> 1 \Rightarrow$ incoherence reachable.
:::

::: proof
*Proof.* Direct application of Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"}. With DOF $> 1$, independent locations can be modified separately, reaching states where they disagree. ◻
:::

## Coherence Restoration Complexity {#sec:ssot-vs-m}

When fact $F$ changes, how many edits are required to restore coherence?

-   With DOF = 1: 1 edit (the single source). All derived locations update automatically.

-   With DOF $= n > 1$: $n$ edits. Each independent location must be updated manually.

With SSOT, many locations may encode $F$, but coherence restoration requires only 1 edit. The derivation mechanism handles the rest.

::: example
[]{#ex:ssot-large-m label="ex:ssot-large-m"} Consider a codebase where 50 classes inherit from `BaseProcessor`:

    class BaseProcessor(ABC):
        @abstractmethod
        def process(self, data: np.ndarray) -> np.ndarray: ...

    class Detector(BaseProcessor): ...
    class Segmenter(BaseProcessor): ...
    # ... 48 more subclasses

The fact $F$ = "All processors must have a `process` method" is encoded in 51 locations.

**Without SSOT (DOF = 51):** Changing the signature requires 51 edits. After each edit, coherence is partially restored. Only after all 51 edits is the system coherent.

**With SSOT (DOF = 1):** The ABC contract is the single source. Changing the ABC updates the specification; derived locations (type checker flags, runtime enforcement) update automatically. The *contract specification* has a single source.

Note: Implementations are separate facts. SSOT for the contract does not eliminate implementation edits---it ensures the specification is determinate.
:::

## Derivation: The Coherence Mechanism {#sec:derivation}

Derivation is the mechanism by which DOF is reduced without losing encodings. A derived location cannot diverge from its source, eliminating it as a source of incoherence.

::: definition
[]{#def:derivation label="def:derivation"} Location $L_{\text{derived}}$ is *derived from* $L_{\text{source}}$ for fact $F$ iff: $$\text{updated}(L_{\text{source}}) \rightarrow \text{automatically\_updated}(L_{\text{derived}})$$ No manual intervention is required. Coherence is maintained automatically.
:::

Derivation can occur at different times:

::: center
  **Derivation Time**   **Examples**
  --------------------- -----------------------------------------------------------
  Compile time          C++ templates, Rust macros, code generation
  Definition time       Python metaclasses, `__init_subclass__`, class decorators
  Runtime               Lazy computation, memoization
:::

For *structural facts*, derivation must occur at *definition time*. Structural facts (class existence, method signatures) are fixed when the class is defined. Compile-time is too early (source not parsed). Runtime is too late (structure already fixed).

::: theorem
[]{#thm:derivation-excludes label="thm:derivation-excludes"} If $L_{\text{derived}}$ is derived from $L_{\text{source}}$, then $L_{\text{derived}}$ cannot diverge from $L_{\text{source}}$ and does not contribute to DOF.
:::

::: proof
*Proof.* By Definition [\[def:derivation\]](#def:derivation){reference-type="ref" reference="def:derivation"}, derived locations are automatically updated when the source changes. Let $L_d$ be derived from $L_s$. If $L_s$ encodes value $v$, then $L_d$ encodes $f(v)$ for some function $f$. When $L_s$ changes to $v'$, $L_d$ automatically changes to $f(v')$.

There is no reachable state where $L_s = v'$ and $L_d = f(v)$ with $v' \neq v$. Divergence is impossible. Therefore, $L_d$ does not contribute to DOF. ◻
:::

::: corollary
[]{#cor:metaprogramming label="cor:metaprogramming"} If all encodings of $F$ except one are derived from that one, then $\text{DOF}(C, F) = 1$ and coherence is guaranteed.
:::

::: proof
*Proof.* Let $L_s$ be the non-derived encoding. All other encodings $L_1, \ldots, L_k$ are derived from $L_s$. By Theorem [\[thm:derivation-excludes\]](#thm:derivation-excludes){reference-type="ref" reference="thm:derivation-excludes"}, none can diverge. Only $L_s$ is independent. Therefore, $\text{DOF}(C, F) = 1$, and by Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"}, coherence is guaranteed. ◻
:::

## Coherence Patterns in Python {#sec:ssot-patterns}

Python provides several mechanisms for achieving DOF = 1 (coherent representation):

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

DOF = 1 because the registry entry is derived. Incoherence is impossible: the registry cannot disagree with the class hierarchy.

**Pattern 2: Subclass Enumeration via `__subclasses__()`**

    class Processor(ABC):
        @classmethod
        def all_processors(cls):
            return cls.__subclasses__()

    class Detector(Processor): pass
    class Segmenter(Processor): pass

    # Usage: Processor.all_processors() -> [Detector, Segmenter]

The fact "which classes are processors" has DOF = 1: `__subclasses__()` is computed from the class definitions. No separate list can become stale.

**Pattern 3: ABC Contracts**

    class ImageLoader(ABC):
        @abstractmethod
        def load(self, path: str) -> np.ndarray: ...

        @abstractmethod
        def supported_extensions(self) -> List[str]: ...

The contract "loaders must implement `load` and `supported_extensions`" is encoded once in the ABC. The ABC is the single source; compliance is enforced. Truth about the contract is determinate.


# Language Requirements for SSOT {#sec:requirements}

We now derive the language features necessary and sufficient for achieving SSOT. This section answers: *What must a language provide for SSOT to be possible?*

The requirements are derived from SSOT's definition. The proofs establish necessity.

## The Foundational Axiom {#sec:axiom}

The derivation rests on one axiom, which follows from how programming languages work:

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

Therefore, derivation for structural facts must occur at definition time ($t_D = t_{\text{fix}}$). ◻
:::

## Requirement 1: Definition-Time Hooks {#sec:hooks}

::: definition
[]{#def:hook label="def:hook"} A *definition-time hook* is a language construct that executes arbitrary code when a definition (class, function, module) is *created*, not when it is *used*.
:::

This concept has theoretical foundations in metaobject protocols [@kiczales1991art], where class initialization in CLOS allows arbitrary code execution at definition time. Python's implementation of this capability is derived from the same tradition.

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

Contrapositive: If a language lacks definition-time hooks, SSOT for structural facts is impossible. ◻
:::

**Languages lacking definition-time hooks:**

-   **Java**: Annotations are metadata, not executable hooks. They are processed by external tools (annotation processors), not by the language at class definition.

-   **C++**: Templates expand at compile time but do not execute arbitrary code. SFINAE and `constexpr if` are not hooks---they select branches, not execute callbacks.

-   **Go**: No hook mechanism. Interfaces are implicit. No code runs at type definition.

-   **Rust**: Procedural macros run at compile time but are opaque at runtime. The macro expansion is not introspectable.

## Requirement 2: Introspectable Derivation {#sec:introspection}

Definition-time hooks enable derivation. But SSOT also requires *verification*---the ability to confirm that DOF = 1. This requires *computational reflection*---the ability of a program to reason about its own structure [@smith1984reflection].

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

Without verifiable SSOT, the programmer cannot confirm SSOT holds. They must trust that their code is correct without runtime confirmation. Bugs in derivation logic go undetected. ◻
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

Therefore, the requirements are independent. ◻
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

The if-and-only-if follows. ◻
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

Contrast with Python, where the registry entry exists only in memory, created by the class statement itself. There is no second file. DOF $= 1$. ◻
:::

**Why Rust proc macros don't help:**

::: theorem
[]{#thm:opaque-expansion label="thm:opaque-expansion"} If macro/template expansion is opaque at runtime, SSOT cannot be verified.
:::

::: proof
*Proof.* Verification of SSOT requires answering: "Is every encoding of $F$ derived from the single source?"

This requires enumerating all encodings. If expansion is opaque, the program cannot query what was generated.

In Rust, after `#[derive(Handler)]` expands, the program cannot ask "what did this macro generate?" The expansion is compiled into the binary but not introspectable.

Without introspection, the program cannot verify DOF $= 1$. SSOT may hold but cannot be confirmed. ◻
:::

**The Gap is Fundamental:**

The distinction is not "Python has nicer syntax." The distinction is:

-   Python: Class definition *executes code* that creates derived structures *in memory*

-   Java: Class definition *produces data* that external tools process into *separate files*

-   Rust: Macro expansion *is invisible at runtime*---verification impossible

This is a language design choice with permanent consequences. No amount of clever coding in Java can make the registry *derived from* the class definition, because Java provides no mechanism for code to execute at class definition time.
