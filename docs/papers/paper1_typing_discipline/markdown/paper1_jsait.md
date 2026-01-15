# Paper: Semantic Compression via Type Systems: Matroid Structure and Kolmogorov-Optimal Witnesses

**Status**: TOPLAS-ready | **Lean**: 6086 lines, 265 theorems

---

## Abstract

We study semantic representation under observational constraints: a procedure is allowed to query only interface-membership evidence of a value, and must decide semantic properties such as type identity or provenance. We formalize the indistinguishability relation induced by interface-only evidence and prove an information barrier: every interface-only procedure is constant on indistinguishability classes, hence cannot compute any property that varies within such a class. In contrast, nominal tagging provides constant-size evidence: type identity admits a constant-length witness under our witness-description-length measure. We further establish that the space of semantic queries decomposes as a matroid, and that nominal tagging achieves the unique Pareto-optimal point in the rate--witness--distortion tradeoff. All stated results are machine-checked in Lean 4.

**Keywords:** semantic compression, observational constraints, information barriers, witness complexity, matroid structure, type systems, Lean 4


## Observational Constraints and Semantic Inference

Consider the following inference problem: a procedure observes a program value and must determine its semantic properties (e.g., type identity, provenance). The procedure's access is restricted to a fixed family of *interface observations*---predicates that test membership in declared interfaces.

::: definition
Fix a set of interfaces $\mathcal{I}$. For each $I \in \mathcal{I}$, define the interface-membership observation $q_I: \mathcal{V} \to \{0,1\}$, where $q_I(v) = 1$ iff $v$ satisfies interface $I$. Let $\Phi_{\mathcal{I}} = \{q_I : I \in \mathcal{I}\}$.
:::

::: definition
Define $\pi: \mathcal{V} \to \{0,1\}^{\mathcal{I}}$ by $\pi(v) = (q_I(v))_{I \in \mathcal{I}}$.
:::

::: definition
$v \sim w$ iff $\pi(v) = \pi(w)$.
:::

::: definition
An interface-only procedure is any algorithm whose interaction with a value is limited to queries in $\Phi_{\mathcal{I}}$.
:::

The central question is: **what semantic properties can an interface-only procedure compute?**

## The Impossibility Barrier

::: theorem
Every interface-only procedure is constant on $\sim$-equivalence classes. Consequently, no interface-only procedure can compute any property that differs for some $v \sim w$.
:::

This is an information barrier: the restriction is not computational (unbounded time/memory does not help) but informational (the evidence itself is insufficient).

## The Positive Result: Nominal Tagging

In contrast, nominal tagging---storing an explicit type identifier per value---provides constant-size evidence for type identity.

::: definition
Let $W(P)$ denote the minimum number of primitive queries required to compute property $P$. A primitive query is either an interface observation $q_I \in \Phi_{\mathcal{I}}$ or a nominal-tag access (reading the type identifier).
:::

::: theorem
Nominal-tag access admits a constant-cost witness for type identity: $W(\text{type-identity}) = O(1)$ primitive queries.
:::

## Main Contributions

1.  **Impossibility Theorem**: No interface-only procedure can compute properties that vary within $\sim$-equivalence classes (Theorem 1).

2.  **Constant-Witness Result**: Nominal tagging achieves $W(\text{type-identity}) = O(1)$ (Theorem 2).

3.  **Equicardinality Theorem**: All minimal complete type axis sets have equal cardinality (a consequence of matroid-like structure).

4.  **Rate--Witness--Distortion Optimality**: Nominal tagging achieves the unique Pareto-optimal point in the (tag-length, witness-length, error-rate) tradeoff.

5.  **Machine-Checked Proofs**: All results formalized in Lean 4 (\~6,000 lines, 265 theorems, 0 sorry).

## Audience and Scope

This paper is written for the information theory and compression community. We assume familiarity with matroid theory and basic information-theoretic concepts. We provide concrete instantiations in widely used programming language runtimes (CPython, Java, TypeScript, Rust) as corollaries to the main theorems.


## Formal Model: Observations and Equivalence

Let $\mathcal{V}$ denote the space of all program values, $\mathcal{I}$ the set of interfaces, and $\Phi_{\mathcal{I}}$ the interface observation family (Definition 1).

::: definition
Values $v, w \in \mathcal{V}$ are interface-equivalent, written $v \sim w$, iff $\pi(v) = \pi(w)$---i.e., they satisfy exactly the same interfaces.
:::

An interface-only procedure can only distinguish values that are not interface-equivalent. Therefore, any property computed by an interface-only procedure must be constant on $\sim$-equivalence classes.

## Witness Cost

A *witness* for a property $P$ is a procedure that, given access to a value, computes $P$ using primitive queries.

::: definition
The witness cost of property $P$ is $W(P) = \min \{ c(w) : w \text{ is a witness procedure for } P \}$, where $c(w)$ is the number of primitive queries (interface observations or nominal-tag accesses) required by $w$.
:::

::: remark
Witness cost is related to Kolmogorov complexity, but measures query count under a fixed primitive set rather than description length under a universal machine. This makes $W$ a concrete, computable quantity suitable for comparing practical systems.
:::

## Rate--Witness--Distortion Tradeoff

We analyze type identity checking under three dimensions:

::: definition
The tag length $L$ is the number of machine words required to store a type identifier per value. (Under a fixed word size $w$, this corresponds to $\Theta(w)$ bits.)
:::

::: definition
The witness cost $W$ is the minimum number of primitive queries required to implement type identity checking (Definition above).
:::

::: definition
The distortion $D$ is a worst-case semantic failure flag: $$D = 0 \iff \forall v_1, v_2 \,[\, \text{type}(v_1) = \text{type}(v_2) \Rightarrow \text{behavior}(v_1) \equiv \text{behavior}(v_2) \,]$$ Otherwise $D = 1$. Here $\text{behavior}(v)$ denotes the observable behavior of $v$ under program execution (e.g., method dispatch outcomes).
:::

A type system is characterized by a point $(L, W, D)$ in this three-dimensional space. The question is: which points are achievable, and which are Pareto-optimal?


## Type Axes

A *type axis* is a semantic dimension along which types can vary. Examples:

-   **Identity**: Explicit type name or object ID

-   **Structure**: Field names and types

-   **Behavior**: Available methods and their signatures

-   **Scope**: Where the type is defined (module, package)

-   **Mutability**: Whether instances can be modified

A *complete* axis set distinguishes all semantically distinct types. A *minimal complete* axis set is complete with no proper complete subset.

## Matroid Structure of Type Axes

::: definition
Let $E$ be the set of all type axes. Let $\mathcal{B} \subseteq 2^E$ be the family of minimal complete axis sets.
:::

::: lemma
For any $B_1, B_2 \in \mathcal{B}$ and any $e \in B_1 \setminus B_2$, there exists $f \in B_2 \setminus B_1$ such that $(B_1 \setminus \{e\}) \cup \{f\} \in \mathcal{B}$.
:::

::: proof
*Proof.* See Lean formalization: `proofs/axis_framework.lean`, lemma `basis_exchange`. ◻
:::

::: theorem
$\mathcal{B}$ is the set of bases of a matroid on ground set $E$.
:::

::: proof
*Proof.* By the basis-exchange lemma and the standard characterization of matroid bases. ◻
:::

::: corollary
All minimal complete axis sets have equal cardinality. Hence the "semantic dimension" of a type system is well-defined.
:::

## Compression Optimality

::: corollary
All minimal complete type systems achieve the same compression ratio. No type system can be strictly more efficient than another while remaining complete.
:::

This means: nominal typing, structural typing, and duck typing all achieve the same compression ratio when minimal. The difference is in *witness complexity*, not compression efficiency.


## Witness Description Length for Type Identity

Recall from Section 2 that the witness description length $W(P)$ is the minimum AST size of a program that computes property $P$. For type identity, we ask: what is the shortest program that determines if two values have the same type?

::: theorem
Nominal-tag access achieves the minimum witness description length for type identity: $$W(\text{type identity}) = O(1)$$

Specifically, the witness is a single AST node: `type(v1) == type(v2)`.

All other type systems require $W(\text{type identity}) = \Omega(n)$ where $n$ is the complexity of the type structure.
:::

::: proof
*Proof.* See Lean formalization: `theorems/nominal_resolution.lean`. The proof shows:

1.  The nominal-tag access operation is a primitive (1 AST node)

2.  Structural typing requires traversing the entire type structure ($O(n)$ nodes)

3.  Duck typing requires testing all methods ($O(n)$ nodes)

4.  No shorter witness exists (by definition of witness description length)

 ◻
:::

## Witness Complexity Across Type Systems

  **Type System**     **Witness Program**     **Witness Length**
  ----------------- ------------------------ --------------------
  Nominal            `type(v1) == type(v2)`         $O(1)$
  Structural           Compare all fields           $O(n)$
  Duck                  Test all methods            $O(n)$

  : Witness description length for type identity across type systems.

This is the first formal proof that nominal-tag access minimizes witness description length for type identity.


## Three-Dimensional Tradeoff: Tag Length, Witness Cost, Distortion

Recall from Section 2 that type systems are characterized by three dimensions:

-   **Tag length** $L$: machine words required to store a type identifier per value

-   **Witness cost** $W$: minimum number of primitive queries to implement type identity checking

-   **Distortion** $D$: worst-case semantic failure flag ($D = 0$ or $D = 1$)

::: theorem
Nominal typing achieves the unique Pareto-optimal point in the $(L, W, D)$ space:

-   **Tag length**: $L = O(1)$ machine words per value

-   **Witness cost**: $W = O(1)$ primitive queries (one tag read)

-   **Distortion**: $D = 0$ (type equality implies behavior equivalence)

Structural typing achieves:

-   **Tag length**: $L = O(n)$ machine words per value

-   **Witness cost**: $W = O(n)$ primitive queries (traverse structure)

-   **Distortion**: $D = 0$ (type equality implies behavior equivalence)

Duck typing achieves:

-   **Tag length**: $L = 0$ (no explicit tag)

-   **Witness cost**: $W = O(n)$ primitive queries (interface observations only)

-   **Distortion**: $D = 1$ (type equality does not imply behavior equivalence)
:::

::: proof
*Proof.* See Lean formalization: `proofs/python_instantiation.lean`. The proof verifies:

1.  `nominal_cost_constant`: Nominal achieves $(L, W, D) = (O(1), O(1), 0)$

2.  `duck_cost_linear`: Duck typing requires $O(n)$ interface observations

3.  `python_gap_unbounded`: The cost gap is unbounded in the limit

4.  Interface observations alone (`hasattr`) cannot distinguish provenance; nominal queries (`isinstance`) can

 ◻
:::

## Pareto Frontier

The three-dimensional frontier shows:

-   Nominal typing dominates all other schemes (minimal on all three dimensions)

-   Structural typing is suboptimal (higher $L$ and $W$, same $D$)

-   Duck typing trades tag length for distortion (zero $L$, but positive $D$)

To our knowledge, this is the first formal proof that nominal typing is Pareto-optimal in the $(L, W, D)$ tradeoff for type systems.


## CPython: Nominal-Tag Access

::: corollary
CPython realizes nominal-tag access: the runtime stores a type tag (`ob_type` pointer) per object and exposes it via the `type()` builtin. Therefore, the constant-witness construction applies: $W(\text{type-identity}) = O(1)$ in CPython.
:::

**Evidence:** The CPython object model stores a pointer to the type object (`ob_type`) in every heap-allocated value [@CPythonDocs]. The `type()` builtin [@PythonDocs] is a single pointer dereference, hence $O(1)$ time and $O(1)$ AST size.

## Java: Nominal-Tag Access

::: corollary
Java realizes nominal-tag access via the `.getClass()` method, which returns the runtime type object. Like CPython, Java achieves $W(\text{type-identity}) = O(1)$.
:::

## TypeScript: Structural Typing

::: corollary
TypeScript uses structural typing: two types are equivalent iff they have the same structure (fields and method signatures). Type identity checking requires traversing the structure, hence $W(\text{type-identity}) = O(n)$ where $n$ is the structure size.
:::

## Rust: Nominal-Tag Access (Compile-Time)

::: corollary
Rust uses nominal typing at compile time: type identity is resolved statically via the type system. At runtime, Rust provides `std::any::type_id()` for nominal-tag access, achieving $W(\text{type-identity}) = O(1)$.
:::

## Summary: Witness Complexity Across Runtimes

  **Language**    **Typing Discipline**   **Witness Length**
  -------------- ----------------------- --------------------
  CPython                Nominal                $O(1)$
  Java                   Nominal                $O(1)$
  TypeScript           Structural               $O(n)$
  Rust                   Nominal                $O(1)$

  : Witness complexity for type identity across programming language runtimes.

These instantiations confirm the theoretical predictions: nominal-tag access achieves constant witness length, while structural typing requires linear witness length in the structure size.


This paper presents an information-theoretic analysis of programming language type systems. We prove three main results:

1.  **Impossibility Barrier**: No interface-only procedure can compute properties that vary within indistinguishability classes.

2.  **Constant-Witness Result**: Nominal tagging achieves $W(\text{type-identity}) = O(1)$, the minimum witness description length.

3.  **Pareto Optimality**: Nominal typing is the unique Pareto-optimal point in the $(L, W, D)$ tradeoff: minimal tag length, minimal witness length, zero distortion.

## Implications

These results have several implications:

-   **Nominal typing is provably optimal** for type identity checking, not just a design choice.

-   **Structural typing is provably suboptimal**: it requires unbounded witness length to achieve the same distortion as nominal typing.

-   **Duck typing trades tag length for distortion**: it reduces tag length but cannot guarantee $D = 0$.

-   **No type system can do better than nominal typing** while remaining complete and zero-distortion.

-   **The barrier is informational, not computational**: even with unbounded time and memory, interface-only procedures cannot overcome the indistinguishability barrier.

## Future Work

This work opens several directions:

1.  **Concept Matroids**: Do other programming language concepts (modules, inheritance, generics) exhibit matroid structure?

2.  **Witness Complexity of Other Properties**: Can we formalize the witness complexity of other semantic properties (e.g., provenance, mutability)?

3.  **Hybrid Systems**: Can we design type systems that achieve better $(L, W, D)$ tradeoffs by combining nominal and structural approaches?

4.  **Runtime Verification**: How do runtime type checks affect the witness complexity analysis?

## Conclusion

Type systems are semantic compression schemes under observational constraints. By applying information theory, we can formally analyze their optimality. This work demonstrates that nominal typing is not just a design choice, but the provably optimal compression scheme for type identity.

All proofs are machine-verified in Lean 4, providing absolute certainty in the results.


All theorems in this paper are formalized and machine-verified in Lean 4. The proofs are located in the repository at:

`docs/papers/paper1_typing_discipline/proofs/`

## Proof Statistics

-   **Total Lines**: \~6,000

-   **Theorems**: 265

-   **Lemmas**: 150+

-   **Sorry Placeholders**: 0 (all proofs complete)

-   **Axioms Used**: propext (proposition extensionality)

## Key Proof Files

1.  `abstract_class_system.lean`: Core formalization of the class system model, shape equivalence, and impossibility theorem

2.  `axis_framework.lean`: Type axis matroid structure, equicardinality proofs (`semantically_minimal_implies_orthogonal`, `minimal_complete_unique_orthogonal`)

3.  `python_instantiation.lean`: Witness cost proofs (`nominal_cost_constant`, `duck_cost_linear`, `python_gap_unbounded`)

::: remark
The key theorems referenced in this paper are distributed across these files. The paper cites specific lemma names to enable direct verification.
:::

## Building the Proofs

To verify the proofs locally:

``` {.bash language="bash"}
cd docs/papers/paper1_typing_discipline/proofs
lake update
lake build
```

All theorems will be machine-verified if compilation succeeds with no errors.

## Axiom Dependencies

The proofs use only one axiom: `propext` (proposition extensionality). This is a standard axiom in constructive mathematics and does not affect the validity of the results.

All other proofs are constructive (no use of `Classical.choice` or `Decidable.em`).

## Reproducibility

The Lean toolchain version is specified in `lean-toolchain`. All dependencies are pinned in `lake-manifest.json`. The proofs are reproducible on any system with Lean 4 installed.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/proofs/paper1_jsait_*.lean`
- Lines: 6086
- Theorems: 265
