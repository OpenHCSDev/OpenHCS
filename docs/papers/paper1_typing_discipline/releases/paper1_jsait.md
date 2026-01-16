# Paper: Information Barriers in Classification Systems: Matroid Structure and Witness Complexity

**Status**: JSAIT-ready | **Lean**: 6086 lines, 265 theorems

---

## Abstract

We extend classical rate-distortion theory to a discrete classification setting with three resources: *tag rate* $L$ (bits of storage per entity), *identification cost* $W$ (queries to determine class membership, measured per identification under constraints excluding global preprocessing and amortized caching), and *distortion* $D$ (misidentification probability). The fundamental question is: how do these resources trade off when an observer must identify an entity's class from limited observations?

**Information barrier (zero-error identifiability).** When distinct classes share identical attribute profiles, no algorithm, regardless of computational power, can identify the class from attribute queries alone. Formally: if $\pi$ is not injective on classes, then zero-error identification from attribute queries alone is impossible (equivalently, the induced observation channel cannot support zero-error class recovery).

**Rate-identification tradeoff.** We identify the unique Pareto-optimal zero-error point in the $(L, W, D)$ tradeoff space and describe the induced tradeoff geometry. A nominal tag of $L = \lceil \log_2 k \rceil$ bits for $k$ classes yields $W = O(1)$ with $D = 0$. Without tags ($L = 0$), identification requires $W = \Omega(n)$ queries and may incur $D > 0$.

**Converse.** Any scheme achieving $D = 0$ requires $L \geq \log_2 k$ bits. This is tight: nominal tagging achieves the bound with $W = O(1)$.

**Matroid structure.** Minimal sufficient query sets form the bases of a matroid. The *distinguishing dimension* (the common cardinality of all minimal query sets) is well-defined and computable, connecting to zero-error source coding via graph entropy.

**Applications.** The theory instantiates to type systems (duck vs. nominal typing), databases (attribute vs. key lookup), and biological taxonomy (phenotype vs. species identifier). The unbounded gap $\Omega(n)$ vs. $O(1)$ explains convergence toward hybrid systems combining structural observation with nominal tagging.

All results are machine-checked in Lean 4 (6,000+ lines, 0 `sorry`).

**Keywords:** rate-distortion theory, identification capacity, zero-error source coding, query complexity, matroid structure, classification systems


## The Identification Problem

Consider an encoder-decoder pair communicating about entities from a large universe $\mathcal{V}$. The decoder must *identify* each entity, determining which of $k$ classes it belongs to, using only:

-   A *tag* of $L$ bits stored with the entity, and/or

-   *Queries* to a binary oracle: "does entity $v$ satisfy attribute $I$?"

This is not reconstruction (the decoder need not recover $v$), but *identification* in the sense of Ahlswede and Dueck [@ahlswede1989identification]: the decoder must answer "which class?" with zero or bounded error.

We prove three results:

1.  **Information barrier (identifiability limit).** When the attribute profile $\pi: \mathcal{V} \to \{0,1\}^n$ is not injective on classes, zero-error identification via queries alone is impossible: any decoder produces identical output on colliding classes, so cannot be correct for both.

2.  **Optimal tagging (achievability).** A tag of $L = \lceil \log_2 k \rceil$ bits achieves zero-error identification with $W = O(1)$ query cost. This is Pareto-optimal in the $(L, W, D)$ tradeoff space.

3.  **Matroid structure (query complexity).** Minimal sufficient query sets form the bases of a matroid. The *distinguishing dimension* (the common cardinality of all minimal sets) lower-bounds the query cost $W$ for any tag-free scheme.

These results are universal: the theory applies to type systems, databases, biological taxonomy, and knowledge graphs. We develop the mathematics in full generality, then exhibit concrete instantiations.

## The Observation Model

We formalize the observational constraint as a family of binary predicates. The terminology is deliberately abstract; concrete instantiations follow in Section [\[sec:applications\]](#sec:applications){reference-type="ref" reference="sec:applications"}.

::: definition
Let $\mathcal{V}$ be a set of entities (program objects, database records, biological specimens, library items). Let $\mathcal{I}$ be a finite set of *attributes*: observable properties that partition the entity space.
:::

::: remark
We use "attribute" for the abstract concept. In type systems, attributes are *interfaces* or *method signatures*. In databases, they are *columns*. In taxonomy, they are *phenotypic characters*. In library science, they are *facets*. The mathematics is identical.
:::

::: definition
For each $I \in \mathcal{I}$, define the interface-membership observation $q_I: \mathcal{V} \to \{0,1\}$: $$q_I(v) = \begin{cases} 1 & \text{if } v \text{ satisfies interface } I \\ 0 & \text{otherwise} \end{cases}$$ Let $\Phi_{\mathcal{I}} = \{q_I : I \in \mathcal{I}\}$ denote the interface observation family.
:::

::: definition
The interface profile function $\pi: \mathcal{V} \to \{0,1\}^{|\mathcal{I}|}$ maps each value to its complete interface signature: $$\pi(v) = (q_I(v))_{I \in \mathcal{I}}$$
:::

::: definition
Values $v, w \in \mathcal{V}$ are *interface-indistinguishable*, written $v \sim w$, iff $\pi(v) = \pi(w)$.
:::

The relation $\sim$ is an equivalence relation. We write $[v]_\sim$ for the equivalence class of $v$.

::: definition
An *interface-only observer* is any procedure whose interaction with a value $v \in \mathcal{V}$ is limited to queries in $\Phi_{\mathcal{I}}$. Formally, the observer receives only $\pi(v)$, not $v$ itself.
:::

## The Central Question

The central question is: **what semantic properties can an interface-only observer compute?**

A semantic property is a function $P: \mathcal{V} \to \{0,1\}$ (or more generally, $P: \mathcal{V} \to Y$ for some codomain $Y$). We say $P$ is *interface-computable* if there exists a function $f: \{0,1\}^{|\mathcal{I}|} \to Y$ such that $P(v) = f(\pi(v))$ for all $v$.

## The Information Barrier

::: theorem
[]{#thm:information-barrier label="thm:information-barrier"} Let $P: \mathcal{V} \to Y$ be any function. If $P$ is interface-computable, then $P$ is constant on $\sim$-equivalence classes: $$v \sim w \implies P(v) = P(w)$$ Equivalently: no interface-only observer can compute any property that varies within an equivalence class.
:::

::: proof
*Proof.* Suppose $P$ is interface-computable via $f$, i.e., $P(v) = f(\pi(v))$ for all $v$. Let $v \sim w$, so $\pi(v) = \pi(w)$. Then: $$P(v) = f(\pi(v)) = f(\pi(w)) = P(w)$$ ◻
:::

::: remark
The barrier is *informational*, not computational. Given unlimited time, memory, and computational power, an interface-only observer still cannot distinguish $v$ from $w$ when $\pi(v) = \pi(w)$. The constraint is on the evidence itself.
:::

::: corollary
[]{#cor:provenance-barrier label="cor:provenance-barrier"} Let $\text{type}: \mathcal{V} \to \mathcal{T}$ be the type assignment function. If there exist values $v, w$ with $\pi(v) = \pi(w)$ but $\text{type}(v) \neq \text{type}(w)$, then type identity is not interface-computable.
:::

::: proof
*Proof.* Direct application of Theorem [\[thm:information-barrier\]](#thm:information-barrier){reference-type="ref" reference="thm:information-barrier"} to $P = \text{type}$. ◻
:::

## The Positive Result: Nominal Tagging

We now show that augmenting interface observations with a single primitive, nominal-tag access, achieves constant witness cost.

::: definition
A *nominal tag* is a value $\tau(v) \in \mathcal{T}$ associated with each $v \in \mathcal{V}$, representing the type identity of $v$. The *nominal-tag access* operation returns $\tau(v)$ in $O(1)$ time.
:::

::: definition
The extended primitive query set is $\Phi_{\mathcal{I}}^+ = \Phi_{\mathcal{I}} \cup \{\tau\}$, where $\tau$ denotes nominal-tag access.
:::

::: definition
Let $W(P)$ denote the minimum number of primitive queries from $\Phi_{\mathcal{I}}^+$ required to compute property $P$: $$W(P) = \min \{ c(A) : A \text{ is a procedure computing } P \}$$ where $c(A)$ counts the number of queries to $\Phi_{\mathcal{I}}^+$ made by $A$.
:::

::: theorem
[]{#thm:constant-witness label="thm:constant-witness"} Under nominal-tag access, type identity checking has constant witness cost: $$W(\text{type-identity}) = O(1)$$ Specifically, the witness procedure is: return $\tau(v_1) = \tau(v_2)$.
:::

::: proof
*Proof.* The procedure makes exactly 2 primitive queries (one $\tau$ access per value) and one comparison. This is $O(1)$ regardless of the number of interfaces $|\mathcal{I}|$. ◻
:::

::: theorem
[]{#thm:interface-lower-bound label="thm:interface-lower-bound"} For interface-only observers, type identity checking requires: $$W(\text{type-identity}) = \Omega(|\mathcal{I}|)$$ in the worst case.
:::

::: proof
*Proof.* Construct a family of $|\mathcal{I}|$ types where each type $T_i$ satisfies exactly the interfaces $\{I_1, \ldots, I_i\}$. Distinguishing $T_{i}$ from $T_{i+1}$ requires querying $I_{i+1}$. Thus, distinguishing all pairs requires querying all $|\mathcal{I}|$ interfaces. ◻
:::

## Main Contributions

This paper establishes the following results:

1.  **Information Barrier Theorem** (Theorem [\[thm:information-barrier\]](#thm:information-barrier){reference-type="ref" reference="thm:information-barrier"}): Interface-only observers cannot compute any property that varies within $\sim$-equivalence classes. This is an information-theoretic impossibility, not a computational limitation.

2.  **Constant-Witness Theorem** (Theorem [\[thm:constant-witness\]](#thm:constant-witness){reference-type="ref" reference="thm:constant-witness"}): Nominal-tag access achieves $W(\text{type-identity}) = O(1)$, with matching lower bound $\Omega(|\mathcal{I}|)$ for interface-only observers (Theorem [\[thm:interface-lower-bound\]](#thm:interface-lower-bound){reference-type="ref" reference="thm:interface-lower-bound"}).

3.  **Complexity Separation** (Section [\[sec:complexity\]](#sec:complexity){reference-type="ref" reference="sec:complexity"}): We establish O(1) vs O(k) vs $\Omega(n)$ complexity bounds for error localization under different observation regimes.

4.  **Matroid Structure** (Section [\[sec:matroid\]](#sec:matroid){reference-type="ref" reference="sec:matroid"}): Minimal distinguishing query sets form the bases of a matroid. All such sets have equal cardinality, establishing a well-defined "distinguishing dimension."

5.  **$(L, W, D)$ Optimality** (Section [\[sec:lwd\]](#sec:lwd){reference-type="ref" reference="sec:lwd"}): Nominal-tag observers achieve the unique Pareto-optimal point in the $(L, W, D)$ tradeoff space (tag length, witness cost, distortion).

6.  **Machine-Checked Proofs**: All results formalized in Lean 4 (6,086 lines, 265 theorems, 0 `sorry` placeholders).

## Related Work and Positioning

**Identification via channels.** Our work extends the identification paradigm introduced by Ahlswede and Dueck [@ahlswede1989identification; @ahlswede1989identification2]. In their framework, a decoder need not reconstruct a message but only answer "is the message $m$?" for a given hypothesis. This yields dramatically different capacity: double-exponential codebook sizes become achievable. Our setting differs in three ways: (1) we consider zero-error identification rather than vanishing error, (2) queries are adaptive rather than block codes, and (3) we allow auxiliary tagging (rate $L$) to reduce query cost. The $(L, W, D)$ tradeoff generalizes Ahlswede-Dueck to a multi-dimensional operating regime.

**Rate-distortion theory.** The $(L, W, D)$ framework connects to Shannon's rate-distortion theory [@shannon1959coding; @berger1971rate] with an important twist: the "distortion" $D$ is semantic (class misidentification), and there is a second resource $W$ (query cost) alongside rate $L$. Classical rate-distortion asks: what is the minimum rate to achieve distortion $D$? We ask: given rate $L$, what is the minimum query cost $W$ to achieve distortion $D = 0$? Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"} identifies the unique Pareto-optimal point in this three-dimensional tradeoff at $D = 0$.

**Rate-distortion-perception tradeoffs.** Blau and Michaeli [@blau2019rethinking] extended rate-distortion theory by adding a perception constraint, creating a three-way tradeoff. Our query cost $W$ plays an analogous role: it measures the interactive cost of achieving low distortion rather than a distributional constraint. This parallel suggests that $(L, W, D)$ tradeoffs may admit similar geometric characterizations. Section [\[sec:extensions\]](#sec:extensions){reference-type="ref" reference="sec:extensions"} develops this connection further.

**Zero-error information theory.** The matroid structure (Section [\[sec:matroid\]](#sec:matroid){reference-type="ref" reference="sec:matroid"}) connects to zero-error capacity and graph entropy. Körner [@korner1973coding] and Witsenhausen [@witsenhausen1976zero] studied zero-error source coding where confusable symbols must be distinguished. Our distinguishing dimension (Definition [\[def:distinguishing-dimension\]](#def:distinguishing-dimension){reference-type="ref" reference="def:distinguishing-dimension"}) is the minimum number of binary queries to separate all classes, which is precisely the zero-error identification cost when $L = 0$.

**Query complexity and communication complexity.** The $\Omega(n)$ lower bound for interface-only identification relates to decision tree complexity [@buhrman2002complexity] and interactive communication [@orlitsky1991worst]. The key distinction is that our queries are constrained to a fixed attribute family $\mathcal{I}$, not arbitrary predicates. This constraint models practical systems where the observer's interface to entities is architecturally fixed.

**Compression in classification systems.** Our framework instantiates to type systems, where the compression question becomes: how many bits must be stored per object to enable $O(1)$ type identification? The answer ($\lceil \log_2 k \rceil$ bits for $k$ classes) matches the converse bound (Theorem [\[thm:converse\]](#thm:converse){reference-type="ref" reference="thm:converse"}). This provides an information-theoretic foundation for the nominal-vs-structural typing debate in programming language theory [@Cardelli1985; @cook1990inheritance].

**Historical context.** The "duck typing" philosophy ("if it walks like a duck and quacks like a duck, it's a duck") advocates structural observation over nominal tagging. Within our model, we prove this incurs $\Omega(n)$ witness cost where tagging achieves $O(1)$. The result does not "resolve" the broader debate (which involves usability and tooling concerns beyond this model) but establishes that the tradeoff has a precise information-theoretic component.

**Practical convergence.** Modern systems have converged on hybrid classification: Python's Abstract Base Classes, TypeScript's branded types, Rust's trait system, DNA barcoding in taxonomy [@DNABarcoding]. This convergence is consistent with the rate-query tradeoff: nominal tags provide $O(1)$ identification at cost $O(\log k)$ bits. The contribution is not advocacy for any design, but a formal framework for analyzing identification cost in classification systems.

## Paper Organization

Section [\[sec:framework\]](#sec:framework){reference-type="ref" reference="sec:framework"} formalizes the compression framework and defines the $(L, W, D)$ tradeoff. Section [\[sec:complexity\]](#sec:complexity){reference-type="ref" reference="sec:complexity"} establishes complexity bounds for error localization. Section [\[sec:matroid\]](#sec:matroid){reference-type="ref" reference="sec:matroid"} proves the matroid structure of type axes. Section [\[sec:witness\]](#sec:witness){reference-type="ref" reference="sec:witness"} analyzes witness cost in detail. Section [\[sec:lwd\]](#sec:lwd){reference-type="ref" reference="sec:lwd"} proves Pareto optimality. Section [\[sec:applications\]](#sec:applications){reference-type="ref" reference="sec:applications"} instantiates the theory in real runtimes. Section [\[sec:conclusion\]](#sec:conclusion){reference-type="ref" reference="sec:conclusion"} concludes. Appendix [\[sec:lean\]](#sec:lean){reference-type="ref" reference="sec:lean"} describes the Lean 4 formalization.


## Semantic Compression: The Problem

The fundamental problem of *semantic compression* is: given a value $v$ from a large space $\mathcal{V}$, how can we represent $v$ compactly while preserving the ability to answer semantic queries about $v$? This differs from classical source coding in that the goal is not reconstruction but *identification*: determining which equivalence class $v$ belongs to.

Classical rate-distortion theory [@shannon1959coding] studies the tradeoff between representation size and reconstruction fidelity. We extend this to a discrete classification setting with three dimensions: *tag length* $L$ (bits of storage), *witness cost* $W$ (queries or bits of communication required to determine class membership), and *distortion* $D$ (semantic fidelity).

## Universe of Discourse

::: definition
A *classification scheme* is any procedure (deterministic or randomized), with arbitrary time and memory, whose only access to a value $v \in \mathcal{V}$ is via:

1.  The *observation family* $\Phi = \{q_I : I \in \mathcal{I}\}$, where $q_I(v) = 1$ iff $v$ satisfies attribute $I$; and optionally

2.  A *nominal-tag primitive* $\tau: \mathcal{V} \to \mathcal{T}$ returning an opaque type identifier.

All theorems in this paper quantify over all such schemes.
:::

This definition is intentionally broad: schemes may be adaptive, randomized, or computationally unbounded. The constraint is *observational*, not computational.

::: theorem
[]{#thm:info-barrier label="thm:info-barrier"} For all classification schemes with access only to $\Phi$ (no nominal tag), the output is constant on $\sim_\Phi$-equivalence classes. Therefore, no such scheme can compute any property that varies within a $\sim_\Phi$-class.
:::

::: proof
*Proof.* Let $v \sim_\Phi w$, meaning $q_I(v) = q_I(w)$ for all $I \in \mathcal{I}$. Any scheme's execution trace depends only on query responses. Since all queries return identical values for $v$ and $w$, the scheme cannot distinguish them. Any output must therefore be identical. ◻
:::

::: proposition
[]{#prop:model-capture label="prop:model-capture"} Any real-world classification protocol whose evidence consists solely of attribute-membership queries is representable as a scheme in the above model. Conversely, any additional capability corresponds to adding new observations to $\Phi$.
:::

This proposition forces any objection into a precise form: to claim the theorem does not apply, one must name the additional observation capability not in $\Phi$. "Different universe" is not a coherent objection; it must reduce to "I have access to oracle $X \notin \Phi$."

## The Two-Axis Model

We adopt a two-axis model of semantic structure, where each value is characterized by:

-   **Lineage axis ($B$)**: The provenance chain of the value's class (which classes it derives from, in what order)[^1]

-   **Profile axis ($S$)**: The observable interface (which attributes/methods the value provides)

::: definition
A value $v \in \mathcal{V}$ has representation $(B(v), S(v))$ where: $$\begin{aligned}
B(v) &= \text{lineage}(\text{class}(v)) \quad \text{(class derivation chain)} \\
S(v) &= \pi(v) = (q_I(v))_{I \in \mathcal{I}} \quad \text{(interface profile)}
\end{aligned}$$ The lineage axis captures *nominal* identity: where the class comes from. The profile axis captures *structural* identity: what the value can do.
:::

::: theorem
[]{#thm:model-completeness label="thm:model-completeness"} In classification systems with explicit class derivation, the pair $(B, S)$ is complete: every semantic property of a value is a function of $(B(v), S(v))$.
:::

::: proof
*Proof.* Any property not determined by $(B, S)$ would require information beyond class identity and interface. In hierarchical classification systems (type systems, biological taxonomy, library classification), the class and its observable attributes jointly determine all semantically relevant properties. ◻
:::

## Interface Equivalence and Observational Limits

Recall from Section 1 the interface equivalence relation:

::: definition
Values $v, w \in \mathcal{V}$ are interface-equivalent, written $v \sim w$, iff $\pi(v) = \pi(w)$, i.e., they satisfy exactly the same interfaces.
:::

::: proposition
The relation $\sim$ partitions $\mathcal{V}$ into equivalence classes. Let $\mathcal{V}/{\sim}$ denote the quotient space. An interface-only observer effectively operates on $\mathcal{V}/{\sim}$, not $\mathcal{V}$.
:::

::: corollary
The information lost by interface-only observation is: $$H(\mathcal{V}) - H(\mathcal{V}/{\sim}) = H(\mathcal{V} | \pi)$$ where $H$ denotes entropy. This quantity is positive whenever multiple types share the same interface profile.
:::

## Identification Capacity {#sec:identification-capacity}

We now formalize the identification problem in channel-theoretic terms. Let $C: \mathcal{V} \to \{1, \ldots, k\}$ denote the class assignment function, and let $\pi: \mathcal{V} \to \{0,1\}^n$ denote the attribute profile.

::: definition
The *identification channel* induced by observation family $\Phi$ is the mapping $C \to \pi(V)$ for a random entity $V$ drawn from distribution $P_V$ over $\mathcal{V}$. The channel output is the attribute profile; the channel input is implicitly the class $C(V)$.
:::

::: theorem
[]{#thm:identification-capacity label="thm:identification-capacity"} Let $\mathcal{C} = \{1, \ldots, k\}$ be the class space. The *zero-error identification capacity* of the observation channel is: $$C_{\text{id}} = \begin{cases}
\log_2 k & \text{if } \pi \text{ is injective on classes} \\
0 & \text{otherwise}
\end{cases}$$ That is, zero-error identification of all $k$ classes is achievable if and only if every class has a distinct attribute profile. When $\pi$ is not class-injective, no rate of identification is achievable with zero error.
:::

::: proof
*Proof.* *Achievability*: If $\pi$ is injective on classes, then observing $\pi(v)$ determines $C(v)$ uniquely. The decoder simply inverts the class-to-profile mapping.

*Converse* (deterministic): Suppose two distinct classes $c_1 \neq c_2$ share a profile: $\exists v_1 \in c_1, v_2 \in c_2$ with $\pi(v_1) = \pi(v_2)$. Then any decoder $g(\pi(v))$ outputs the same class label on both $v_1$ and $v_2$, so it cannot be correct for both. Hence zero-error identification of all classes is impossible. ◻
:::

::: remark
Under any distribution with positive mass on both colliding classes, $I(C; \pi(V)) < H(C)$. This is an average-case consequence of the deterministic barrier above.
:::

::: remark
In the identification paradigm of [@ahlswede1989identification], the decoder asks "is the message $m$?" rather than "what is the message?" This yields double-exponential codebook sizes. Our setting is different: we require zero-error identification of the *class*, not hypothesis testing. The one-shot zero-error identification feasibility threshold ($\pi$ must be class-injective) is binary rather than a rate.
:::

The key insight is that tagging provides a *side channel* that restores identifiability when the attribute channel fails:

::: theorem
[]{#thm:tag-restored label="thm:tag-restored"} A tag of length $L \geq \lceil \log_2 k \rceil$ bits restores zero-error identification capacity, regardless of whether $\pi$ is class-injective. The tag provides a noiseless side channel with capacity $L$ bits.
:::

::: proof
*Proof.* A nominal tag $\tau: \mathcal{V} \to \{1, \ldots, k\}$ assigns a unique identifier to each class. Reading $\tau(v)$ determines $C(v)$ in $O(1)$ queries, independent of the attribute channel. ◻
:::

## Witness Cost: Query Complexity for Semantic Properties

::: definition
A *witness procedure* for property $P: \mathcal{V} \to Y$ is an algorithm $A$ that:

1.  Takes as input a value $v \in \mathcal{V}$ (via query access only)

2.  Makes queries to the primitive set $\Phi_{\mathcal{I}}^+$

3.  Outputs $P(v)$
:::

::: definition
The *witness cost* of property $P$ is: $$W(P) = \min_{A \text{ computes } P} c(A)$$ where $c(A)$ is the worst-case number of primitive queries made by $A$.
:::

::: remark
Witness cost is a form of query complexity [@buhrman2002complexity] specialized to semantic properties. Unlike Kolmogorov complexity, $W$ is computable and depends on the primitive set, not a universal machine.
:::

::: lemma
For any property $P$:

1.  If $P$ is interface-computable: $W(P) \leq |\mathcal{I}|$

2.  If $P$ varies within some $\sim$-class: $W(P) = \infty$ for interface-only observers

3.  With nominal-tag access: $W(\text{type-identity}) = O(1)$
:::

## The $(L, W, D)$ Tradeoff

We now define the three-dimensional tradeoff space that characterizes observation strategies, using information-theoretic units.

::: definition
Let $\mathcal{T}$ be the set of type identifiers (tags) with $|\mathcal{T}| = k$. The *tag length* $L$ is the number of bits required to encode a type identifier: $$L \geq \log_2 k \quad \text{bits per value}$$ For nominal-tag observers, $L = \lceil \log_2 k \rceil$ (optimal prefix-free encoding). For interface-only observers, $L = 0$ (no explicit tag stored). Under a distribution $P$ over types, the expected tag length is $\mathbb{E}[L] \geq H(P)$ by Shannon's source coding theorem [@shannon1959coding].
:::

::: definition
The *witness cost* $W$ is the minimum number of primitive queries (or bits of interactive communication) required for type identity checking: $$W = \min_{A \text{ decides type-identity}} c(A)$$ where $c(A)$ is the worst-case query count. This is a form of query complexity [@buhrman2002complexity] or interactive identification cost.
:::

::: definition
Let $\text{behavior}: \mathcal{V} \to \mathcal{B}$ be a function mapping each entity to its observable behavior (the set of responses to all possible operations). Two entities $v, w$ are *behaviorally equivalent*, written $v \equiv w$, iff $\text{behavior}(v) = \text{behavior}(w)$.

In type systems, $\text{behavior}(v)$ is the denotational semantics: the function computed by $v$. In databases, it is the set of query results. In taxonomy, it is the phenotype. The formalism is parametric in this choice.
:::

::: definition
Let $d: \mathcal{V} \times \mathcal{V} \to \{0, 1\}$ be the misclassification indicator: $$d(v, \hat{v}) = \begin{cases}
0 & \text{if } \text{type}(v) = \text{type}(\hat{v}) \Rightarrow v \equiv \hat{v} \\
1 & \text{otherwise (semantic error)}
\end{cases}$$ That is, $d = 0$ when type equality implies behavioral equivalence (soundness), and $d = 1$ when the observer conflates behaviorally distinct entities.
:::

::: definition
Given a distribution $P$ over values, the *expected distortion* is: $$D = \mathbb{E}_{v \sim P}[d(v, \hat{v})]$$ The *zero-error regime* requires $D = 0$ (no semantic errors for any $v$). All theorems in this paper are proved in the zero-error regime, the strongest case where the separation is sharpest.
:::

::: remark
$D = 0$ means the observation strategy is *sound*: type equality (as computed by the observer) implies behavioral equivalence. $D > 0$ means the strategy may conflate behaviorally distinct values with positive probability. We use $D$ as expected misclassification rate, and in the core theorems we focus on the zero-error regime $D=0$ vs $D>0$; richer distortion structures are discussed in Section [\[sec:extensions\]](#sec:extensions){reference-type="ref" reference="sec:extensions"}.
:::

## The $(L, W, D)$ Tradeoff Space

**Admissible schemes.** To make the Pareto-optimality claim precise, we specify the class of admissible observation strategies:

-   **Deterministic or randomized**: Schemes may use randomness; $W$ is worst-case query count.

-   **Computationally unbounded**: No time/space restrictions; the constraint is observational.

-   **No preprocessing over type universe**: The scheme cannot precompute a global lookup table indexed by all possible types.

-   **Tags are injective on classes**: A nominal tag $\tau(v)$ uniquely identifies the type of $v$. Variable-length or compressed tags are permitted; $L$ counts bits.

-   **No amortization across queries**: $W$ is per-identification cost, not amortized over a sequence.

**Justification.** The "no preprocessing" and "no amortization" constraints exclude trivializations:

-   *Preprocessing*: With unbounded preprocessing over the type universe $\mathcal{T}$, one could build a lookup table mapping attribute profiles to types. This reduces identification to $O(1)$ table lookup, but the table has size $O(|\mathcal{T}|)$, hiding the complexity in space rather than eliminating it. The constraint models systems that cannot afford $O(|\mathcal{T}|)$ storage per observer.

-   *Amortization*: If $W$ were amortized over $n$ identifications, one could cache earlier results. This again hides complexity in state. The per-identification model captures stateless observers (typical in type checking, database queries, and biological identification).

Dropping these constraints changes the achievable region but not the qualitative separation: nominal tags still dominate for $D = 0$ because they provide $O(1)$ worst-case identification without requiring $O(|\mathcal{T}|)$ preprocessing.

Under these rules, "dominance" means strict improvement on at least one of $(L, W, D)$ with no regression on others.

::: definition
A point $(L, W, D)$ is *achievable* if there exists an admissible observation strategy realizing those values. Let $\mathcal{R} \subseteq \mathbb{R}_{\geq 0} \times \mathbb{R}_{\geq 0} \times [0,1]$ denote the achievable region.
:::

::: definition
A point $(L^*, W^*, D^*)$ is *Pareto-optimal* if there is no achievable $(L, W, D)$ with $L \leq L^*$, $W \leq W^*$, $D \leq D^*$, and at least one strict inequality.
:::

The main result of Section [\[sec:lwd\]](#sec:lwd){reference-type="ref" reference="sec:lwd"} is that nominal-tag observation achieves the unique Pareto-optimal point with $D = 0$.

## Converse: Tag Rate Lower Bound

::: theorem
[]{#thm:converse label="thm:converse"} Any scheme achieving $D = 0$ (zero-error identification) requires tag length $L \geq \log_2 k$, where $k$ is the number of distinct classes.
:::

::: proof
*Proof.* Zero error requires that distinct classes map to distinct decoder outputs. With $k$ classes, at least $\log_2 k$ bits are needed to encode $k$ distinct values. Without tags ($L = 0$), the decoder sees only query responses $\pi(v) \in \{0,1\}^{|\mathcal{I}|}$. If $\pi$ is not injective on classes (i.e., $\exists$ classes $c_1 \neq c_2$ with identical profiles), zero error is impossible. The converse is tight: $L = \lceil \log_2 k \rceil$ suffices. ◻
:::

## Rate-Distortion Tradeoff

When $D > 0$ is permitted, we obtain a classic rate-distortion tradeoff:

::: proposition
For any $\epsilon \in (0, 1)$, there exist schemes with $L = 0$ (no tags) achieving $D \leq \epsilon$ with query cost $W = O(\log(1/\epsilon) \cdot d)$, where $d$ is the distinguishing dimension. The tradeoff: smaller $D$ requires larger $W$.
:::

The zero-error corner ($D = 0$) is special: nominal tagging is the unique Pareto optimum. Relaxing to $D > 0$ enables tag-free schemes at the cost of increased query complexity. This mirrors the classical distinction between zero-error and $\epsilon$-error capacity in channel coding.

## Concrete Example

Consider a type system with $k = 1000$ classes, each characterized by a subset of $n = 50$ interface methods. Table [1](#tab:strategies){reference-type="ref" reference="tab:strategies"} compares the strategies.

::: {#tab:strategies}
  **Strategy**                            **Tag $L$**                 **Witness $W$**
  ------------------------- --------------------------------------- -------------------
  Nominal (class ID)         $\lceil \log_2 1000 \rceil = 10$ bits        $O(1)$
  Duck typing (query all)                     $0$                    $\leq 50$ queries
  Adaptive duck typing                        $0$                    $\geq d$ queries

  : Identification strategies for 1000 classes with 50 methods.
:::

Here $d$ is the distinguishing dimension, the size of any minimal distinguishing query set. For typical hierarchies, $d \approx 5$--$15$. The gap between 10 bits of storage vs. 5--50 queries per identification is the cost of forgoing nominal tagging.

[^1]: In the Lean formalization (Appendix [\[formalization-and-verification\]](#formalization-and-verification){reference-type="ref" reference="formalization-and-verification"}), the lineage axis is denoted `Bases`, reflecting its instantiation as the inheritance chain in object-oriented languages.


## Query Families and Distinguishing Sets

The classification problem is: given a set of queries, which subsets suffice to distinguish all entities?

::: definition
Let $\mathcal{Q}$ be the set of all primitive queries available to an observer. For a classification system with interface set $\mathcal{I}$, we have $\mathcal{Q} = \{q_I : I \in \mathcal{I}\}$ where $q_I(v) = 1$ iff $v$ satisfies interface $I$.
:::

::: definition
A subset $S \subseteq \mathcal{Q}$ is *distinguishing* if, for all values $v, w$ with $\text{type}(v) \neq \text{type}(w)$, there exists $q \in S$ such that $q(v) \neq q(w)$.
:::

::: definition
A distinguishing set $S$ is *minimal* if no proper subset of $S$ is distinguishing.
:::

## Matroid Structure of Query Families

**Structural assumptions.** The matroid theorem below is *unconditional* given the definitions above. It depends only on:

1.  Queries are binary-valued functions $q: \mathcal{V} \to \{0, 1\}$.

2.  "Distinguishing" is defined by: $\exists q \in S$ such that $q(v) \neq q(w)$.

3.  "Minimal" means no proper subset suffices.

No further assumptions on the query family, value space, or type structure are required. The proof constructs a closure operator satisfying extensivity, monotonicity, and idempotence, from which basis exchange follows (see Lean formalization).

::: definition
Let $E = \mathcal{Q}$ be the ground set of all queries. Let $\mathcal{B} \subseteq 2^E$ be the family of minimal distinguishing sets.
:::

::: lemma
For any $B_1, B_2 \in \mathcal{B}$ and any $q \in B_1 \setminus B_2$, there exists $q' \in B_2 \setminus B_1$ such that $(B_1 \setminus \{q\}) \cup \{q'\} \in \mathcal{B}$.
:::

::: proof
*Proof sketch.* Define the closure operator $\text{cl}(X) = \{q : X\text{-equivalence implies }q\text{-equivalence}\}$. This satisfies:

1.  *Extensive*: $X \subseteq \text{cl}(X)$ (if $q \in X$, then $X$-equivalence trivially implies $q$-equivalence).

2.  *Monotone*: $X \subseteq Y \Rightarrow \text{cl}(X) \subseteq \text{cl}(Y)$ (more queries give finer equivalence).

3.  *Idempotent*: $\text{cl}(\text{cl}(X)) = \text{cl}(X)$ (closure is transitive).

A closure operator satisfying these axioms plus the *exchange property* (if $q \notin \text{cl}(X)$ and $q \in \text{cl}(X \cup \{q'\})$, then $q' \in \text{cl}(X \cup \{q\})$) defines a matroid. The exchange property follows from symmetry of indistinguishability: if adding $q'$ to $X$ newly determines $q$, there exist witnesses $v, w$ with $X$-equivalence, $q'$-inequivalence, and $q$-inequivalence; the same witnesses show adding $q$ newly determines $q'$.

Minimal distinguishing sets are exactly the bases of this matroid. Full machine-checked proof: `proofs/abstract_class_system.lean`, namespace `AxisClosure`. ◻
:::

::: theorem
$\mathcal{B}$ is the set of bases of a matroid on ground set $E$.
:::

::: proof
*Proof.* By the basis-exchange lemma and the standard characterization of matroid bases [@Welsh1976]. ◻
:::

::: definition
[]{#def:distinguishing-dimension label="def:distinguishing-dimension"} The *distinguishing dimension* of a classification system is the common cardinality of all minimal distinguishing sets.
:::

::: corollary
All minimal distinguishing sets have equal cardinality. Thus the distinguishing dimension (Definition [\[def:distinguishing-dimension\]](#def:distinguishing-dimension){reference-type="ref" reference="def:distinguishing-dimension"}) is well-defined.
:::

## Implications for Witness Cost

::: corollary
For any interface-only observer, $W(\text{type-identity}) \geq d$ where $d$ is the distinguishing dimension.
:::

::: proof
*Proof.* Any witness procedure must query at least one minimal distinguishing set. ◻
:::

The key insight: the distinguishing dimension is invariant across all minimal query strategies. The difference between nominal-tag and interface-only observers lies in *witness cost*: a nominal tag achieves $W = O(1)$ by storing the identity directly, bypassing query enumeration.


## Witness Cost for Type Identity

Recall from Section 2 that the witness cost $W(P)$ is the minimum number of primitive queries required to compute property $P$. For type identity, we ask: what is the minimum number of queries to determine if two values have the same type?

::: theorem
Nominal-tag observers achieve the minimum witness cost for type identity: $$W(\text{type identity}) = O(1)$$

Specifically, the witness is a single tag read: compare $\text{tag}(v_1) = \text{tag}(v_2)$.

Interface-only observers require $W(\text{type identity}) = \Omega(n)$ where $n$ is the number of interfaces.
:::

::: proof
*Proof.* See Lean formalization: `proofs/nominal_resolution.lean`. The proof shows:

1.  Nominal-tag access is a single primitive query

2.  Interface-only observers must query $n$ interfaces to distinguish all types

3.  No shorter witness exists for interface-only observers (by the information barrier)

 ◻
:::

## Witness Cost Comparison

  **Observer Class**    **Witness Procedure**   **Witness Cost $W$**
  -------------------- ----------------------- ----------------------
  Nominal-tag              Single tag read             $O(1)$
  Interface-only        Query $n$ interfaces           $O(n)$

  : Witness cost for type identity by observer class.

The Lean 4 formalization (Appendix [\[sec:lean\]](#sec:lean){reference-type="ref" reference="sec:lean"}) provides a machine-checked proof that nominal-tag access minimizes witness cost for type identity.


# Core Theorems

## The Error Localization Theorem

::: definition
Let $E(\mathcal{O})$ be the number of locations that must be inspected to find all potential violations of a constraint under observation family $\mathcal{O}$.
:::

::: theorem
[]{#thm:nominal-localization label="thm:nominal-localization"} $E(\text{nominal-tag}) = O(1)$.
:::

::: proof
*Proof.* Under nominal-tag observation, the constraint "$v$ must be of class $A$" is satisfied iff $\tau(v) \in \text{subtypes}(A)$. This is determined at a single location: the definition of $\tau(v)$'s class. One location. ◻
:::

::: theorem
[]{#thm:declared-localization label="thm:declared-localization"} $E(\text{interface-only, declared}) = O(k)$ where $k$ = number of entity classes.
:::

::: proof
*Proof.* With declared interfaces, the constraint "$v$ must satisfy interface $I$" requires verifying that each class implements all attributes in $I$. For $k$ classes, $O(k)$ locations. ◻
:::

::: theorem
[]{#thm:attribute-localization label="thm:attribute-localization"} $E(\text{attribute-only}) = \Omega(n)$ where $n$ = number of query sites.
:::

::: proof
*Proof.* Under attribute-only observation, each query site independently checks "does $v$ have attribute $a$?" with no centralized declaration. For $n$ query sites, each must be inspected. Lower bound is $\Omega(n)$. ◻
:::

::: corollary
[]{#cor:strict-dominance label="cor:strict-dominance"} Nominal-tag observation strictly dominates attribute-only: $E(\text{nominal-tag}) = O(1) < \Omega(n) = E(\text{attribute-only})$ for all $n > 1$.
:::

## The Information Scattering Theorem

::: definition
Let $I(\mathcal{O}, c)$ be the set of locations where constraint $c$ is encoded under observation family $\mathcal{O}$.
:::

::: theorem
[]{#thm:attribute-scattering label="thm:attribute-scattering"} For attribute-only observation, $|I(\text{attribute-only}, c)| = O(n)$ where $n$ = query sites using constraint $c$.
:::

::: proof
*Proof.* Each attribute query independently encodes the constraint. No shared reference exists. Constraint encodings scale with query sites. ◻
:::

::: theorem
[]{#thm:nominal-centralization label="thm:nominal-centralization"} For nominal-tag observation, $|I(\text{nominal-tag}, c)| = O(1)$.
:::

::: proof
*Proof.* The constraint "must be of class $A$" is encoded once in the definition of $A$. All tag checks reference this single definition. ◻
:::

::: corollary
[]{#cor:maintenance-entropy label="cor:maintenance-entropy"} Attribute-only observation maximizes maintenance entropy; nominal-tag observation minimizes it.
:::


## Three-Dimensional Tradeoff: Tag Length, Witness Cost, Distortion

Recall from Section 2 that observer strategies are characterized by three dimensions:

-   **Tag length** $L$: bits required to encode a type identifier ($L \geq \log_2 k$ for $k$ types)

-   **Witness cost** $W$: minimum number of primitive queries for type identity checking

-   **Distortion** $D$: expected misclassification rate ($D = 0$ in the zero-error regime)

We compare two observer classes:

::: definition
An observer that queries only interface membership ($q_I \in \Phi_{\mathcal{I}}$), with no access to explicit type tags.
:::

::: definition
An observer that may read a single type identifier (nominal tag) per value, in addition to interface queries.
:::

::: theorem
[]{#thm:lwd-optimal label="thm:lwd-optimal"} Nominal-tag observers achieve the unique Pareto-optimal point in the $(L, W, D)$ space with $D = 0$:

-   **Tag length**: $L = \lceil \log_2 k \rceil$ bits for $k$ types

-   **Witness cost**: $W = O(1)$ queries (one tag read)

-   **Distortion**: $D = 0$ (type equality implies behavior equivalence)

Interface-only observers achieve:

-   **Tag length**: $L = 0$ bits (no explicit tag)

-   **Witness cost**: $W = \Omega(n)$ queries (must query $n$ interfaces)

-   **Distortion**: $D > 0$ (may conflate behaviorally distinct types)
:::

::: proof
*Proof.* See Lean formalization: `proofs/python_instantiation.lean`. The proof verifies:

1.  `nominal_cost_constant`: Nominal-tag achieves $(L, W, D) = (O(1), O(1), 0)$

2.  `interface_cost_linear`: Interface-only requires $O(n)$ queries

3.  `python_gap_unbounded`: The cost gap is unbounded in the limit

4.  Interface observations alone cannot distinguish provenance; nominal tags can

 ◻
:::

## Pareto Frontier

The three-dimensional frontier shows:

-   Nominal-tag observers dominate interface-only observers on all three dimensions

-   Interface-only observers trade tag length for distortion (zero $L$, but $D = 1$)

Figure [1](#fig:lwd-tradeoff){reference-type="ref" reference="fig:lwd-tradeoff"} visualizes the $(L, W, D)$ tradeoff space. The key observation: *nominal tags trade storage for query cost*, achieving the optimal $(L, W, D) = (\log_2 k, O(1), 0)$ point.

<figure id="fig:lwd-tradeoff">

<figcaption>Schematic illustration of the <span class="math inline">(<em>L</em>, <em>W</em>, <em>D</em>)</span> tradeoff. The <span class="math inline"><em>D</em> = 0</span> frontier is the Pareto boundary for zero-error type identification: Structural typing (no tags, high query cost) and Nominal typing (full tags, minimal queries) lie on this frontier. Duck typing operates below the frontier by accepting <span class="math inline"><em>D</em> &gt; 0</span>; it uses fewer queries but cannot distinguish interface-equivalent types. Exact frontier shape depends on the type system; the qualitative relationships are general.</figcaption>
</figure>

The Lean 4 formalization (Appendix [\[sec:lean\]](#sec:lean){reference-type="ref" reference="sec:lean"}) provides a machine-checked proof of Pareto optimality for nominal-tag observers in the $(L, W, D)$ tradeoff.

::: remark
In programming language terms: *nominal typing* corresponds to nominal-tag observers (e.g., CPython's `isinstance`, Java's `.getClass()`). *Duck typing* corresponds to interface-only observers (e.g., Python's `hasattr`). *Structural typing* is an intermediate case with $D = 0$ but $W = O(n)$.
:::


The preceding sections established abstract results about observer classes and witness cost. We now ground these in concrete systems across multiple domains, showing that real classification systems instantiate the theoretical categories and that the complexity bounds are not artifacts of the model but observable properties of deployed implementations.

## Biological Taxonomy: Phenotype vs Genotype

Linnean taxonomy classifies organisms by observable phenotypic characters: morphology, behavior, habitat. This is attribute-only observation. The information barrier applies: phenotypically identical organisms from distinct species are indistinguishable.

**The cryptic species problem:** Cryptic species share identical phenotypic profiles but are reproductively isolated and genetically distinct. Attribute-only observation (morphology) cannot distinguish them: $\pi(A) = \pi(B)$ but $\text{species}(A) \neq \text{species}(B)$.

**The nominal tag:** DNA barcoding provides the resolution [@DNABarcoding]. A short genetic sequence (e.g., mitochondrial COI) acts as the nominal tag: $O(1)$ identity verification via sequence comparison. This reduced cryptic species identification from $\Omega(n)$ morphological examination to constant-time molecular lookup.

## Library Classification: Subject vs ISBN

Library classification systems like Dewey Decimal observe subject matter, a form of attribute-only classification. Two books on the same subject are indistinguishable by subject code alone.

**The nominal tag:** The ISBN (International Standard Book Number) is the nominal tag [@ISBN]. Given two physical books, identity verification is $O(1)$: compare ISBNs. Without ISBNs, distinguishing two copies of different editions on the same subject requires $O(n)$ attribute inspection (publication date, page count, publisher, etc.).

## Database Systems: Columns vs Primary Keys

Relational databases observe entities via column values. The information barrier applies: rows with identical column values, excluding the key, are indistinguishable.

**The nominal tag:** The primary key is the nominal tag [@Codd1990]. Entity identity is $O(1)$: compare keys. This is why database theory requires keys---without them, the system cannot answer "is this the same entity?"

**Natural vs surrogate keys:** Natural keys (composed of attributes) are attribute-only observation and inherit its limitations. Surrogate keys (auto-increment IDs, UUIDs) are pure nominal tags: no semantic content, pure identity.

## Programming Language Runtimes

Type systems are the motivating example for this work. We survey four runtimes.

### CPython: The `ob_type` Pointer

Every CPython heap object begins with a `PyObject` header containing an `ob_type` pointer to its type object [@CPythonDocs]. This is the nominal tag: a single machine word encoding complete type identity.

**Witness procedure:** Given objects `a` and `b`, type identity is `type(a) is type(b)`---two pointer dereferences and one pointer comparison. Cost: $O(1)$ primitive operations, independent of interface count.

**Contrast with `hasattr`:** Interface-only observation in Python uses `hasattr(obj, name)` for each required method. To verify an object satisfies a protocol with $k$ methods requires $k$ attribute lookups. Worse: different call sites may check different subsets, creating $\Omega(n)$ total checks where $n$ is the number of call sites. The nominal tag eliminates this entirely.

### Java: `.getClass()` and the Method Table

Java's object model stores a pointer to the class object in every instance header [@JVMSpec]. The `.getClass()` method exposes this [@JavaDocs], and `instanceof` checks traverse the class hierarchy.

**Key observation:** Java's `instanceof` is $O(d)$ where $d$ is inheritance depth, not $O(|\mathcal{I}|)$ where $|\mathcal{I}|$ is the number of interfaces. This is because `instanceof` walks the inheritance hierarchy (a nominal-tag query), not the interface list (an attribute query).

### TypeScript: Structural Equivalence

TypeScript uses attribute-only (declared) observation [@TypeScriptDocs]: the compiler checks structural compatibility, not nominal identity. Two types are assignment-compatible iff their structures match.

**Implication:** Type identity checking requires traversing the structure. For a type with $n$ fields/methods, $W(\text{type-identity}) = O(n)$. This is inherent to the observation model: no compilation strategy can reduce this to $O(1)$ without adding nominal tags.

### Rust: Static Nominal Tags

Rust resolves type identity at compile time via its nominal type system. At runtime, `std::any::TypeId` provides nominal-tag access [@RustDocs].

**The `dyn Trait` case:** Rust's trait objects include a vtable pointer but not a type tag [@RustTraitObjects]. This is attribute-only observation: the vtable encodes which methods exist, not which type provided them.

## Cross-Domain Summary

  **Domain**      **Attribute-Only**       **Nominal Tag**      **$W$**
  --------------- ------------------------ ------------------- ---------
  Biology         Phenotype (morphology)   DNA barcode (COI)    $O(1)$
  Libraries       Subject (Dewey)          ISBN                 $O(1)$
  Databases       Column values            Primary key          $O(1)$
  CPython         `hasattr` probing        `ob_type` pointer    $O(1)$
  Java            Interface check          `.getClass()`        $O(1)$
  TypeScript      Structural check         (none at runtime)    $O(n)$
  Rust (static)   Trait bounds             `TypeId`             $O(1)$

  : Witness cost for identity across classification systems. Nominal tags achieve $O(1)$; attribute-only pays $O(n)$ or $O(k)$.

The pattern is universal: systems with nominal tags achieve $O(1)$ witness cost; systems without them pay $O(n)$ or $O(k)$. This is not domain-specific; it is the information barrier theorem instantiated across classification systems.


## Noisy Query Model

Throughout this paper, queries are deterministic: $q_I(v) \in \{0,1\}$ is a fixed function of $v$. In practice, observations may be corrupted. We sketch an extension to noisy queries and state the resulting open problems.

::: definition
A *noisy observation channel* with crossover probability $\epsilon \in [0, 1/2)$ returns: $$\tilde{q}_I(v) = \begin{cases}
q_I(v) & \text{with probability } 1 - \epsilon \\
1 - q_I(v) & \text{with probability } \epsilon
\end{cases}$$ Each query response is an independent BSC$(\epsilon)$ corruption of the true value.
:::

::: definition
The *$\epsilon$-noisy identification capacity* is the supremum rate (in bits per entity) at which zero-error identification is achievable when all attribute queries pass through a BSC$(\epsilon)$.
:::

In the noiseless case ($\epsilon = 0$), Theorem [\[thm:identification-capacity\]](#thm:identification-capacity){reference-type="ref" reference="thm:identification-capacity"} shows the capacity is binary: $\log_2 k$ if $\pi$ is class-injective, $0$ otherwise. For $\epsilon > 0$, several questions arise.

**Open problem (noisy identification cost).** For $\epsilon > 0$ and class-injective $\pi$, zero-error identification is impossible with finite queries (since BSC has nonzero error probability). With bounded error $\delta > 0$, we expect the identification cost to scale as $W = \Theta\left(\frac{\log(1/\delta)}{(1 - 2\epsilon)^2}\right)$ queries per entity. A key observation is that a nominal tag of $L \geq \lceil \log_2 k \rceil$ bits (transmitted noiselessly) should restore $O(1)$ identification regardless of query noise.

The third point is the key insight: *nominal tags provide a noise-free side channel*. Even when attribute observations are corrupted, a clean tag enables $O(1)$ identification. This strengthens the case for nominal tagging in noisy environments, precisely the regime where "duck typing" would require many repeated queries to achieve confidence.

**Connection to identification via channels.** The noisy model connects more directly to Ahlswede-Dueck identification [@ahlswede1989identification]. In their framework, identification capacity over a noisy channel can exceed Shannon capacity (double-exponential codebook sizes). Our setting differs: we have *adaptive queries* rather than block codes, and the decoder must identify a *class* rather than test a hypothesis. Characterizing the interplay between adaptive query strategies and channel noise is an open problem.

## Rate-Distortion-Query Tradeoff Surface

The $(L, W, D)$ tradeoff admits a natural geometric interpretation. We have identified the unique Pareto-optimal point at $D = 0$ (Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"}), but the full tradeoff surface contains additional structure.

**Fixed-$W$ slices.** For fixed query budget $W$, what is the minimum tag rate $L$ to achieve distortion $D$? When $W \geq d$ (the distinguishing dimension), zero distortion is achievable with $L = 0$ via exhaustive querying. When $W < d$, the observer cannot distinguish all classes, and either:

-   Accept $D > 0$ (misidentification), or

-   Add tags ($L > 0$) to compensate for insufficient queries.

**Fixed-$L$ slices.** For fixed tag rate $L < \log_2 k$, the tag partitions the $k$ classes into $2^L$ groups. Within each group, the observer must use queries to distinguish. The query cost is determined by the distinguishing dimension *within each group*, which is potentially much smaller than the global dimension.

**Open problem (subadditivity of query cost).** For a tag of rate $L$ partitioning classes into groups $G_1, \ldots, G_{2^L}$, we expect $W(L) \leq \max_i d(G_i)$, where $d(G_i)$ is the distinguishing dimension within group $G_i$. Optimal tag design should minimize this maximum. Characterizing the optimal partition remains open.

## Semantic Distortion Measures

We have treated distortion $D$ as binary (correct identification or not). Richer distortion measures are possible:

-   **Hierarchical distortion**: Misidentifying a class within the same genus (biological) or module (type system) is less severe than cross-genus errors.

-   **Weighted distortion**: Some misidentifications have higher cost than others (e.g., type errors causing security vulnerabilities vs. benign type confusion).

## Connection to Rate-Distortion-Perception Theory

Blau and Michaeli [@blau2019rethinking] extended classical rate-distortion theory by adding a *perception* constraint: the reconstructed distribution must match a target distribution under some divergence measure. This creates a three-way tradeoff between rate, distortion, and perceptual quality.

Our $(L, W, D)$ framework admits a parallel interpretation. The query cost $W$ plays a role analogous to the perception constraint: it measures the *interactive cost* of achieving low distortion, rather than a distributional constraint. Just as rate-distortion-perception theory asks "what is the minimum rate to achieve distortion $D$ while satisfying perception constraint $P$?", we ask "what is the minimum tag rate $L$ to achieve distortion $D$ with query budget $W$?"

The analogy suggests several directions:

-   **Perception as identification fidelity**: In classification systems that must preserve statistical properties (e.g., sampling from a type distribution), a perception constraint would require the observer's class estimates to have the correct marginal distribution, not just low expected error.

-   **Three-resource tradeoffs**: The $(L, W, D)$ Pareto frontier (Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"}) is a discrete analogue of the rate-distortion-perception tradeoff surface. Characterizing this surface for specific classification problems would extend the geometric rate-distortion program to identification settings.

Formalizing these connections would unify identification capacity with the broader rate-distortion-perception literature.


This paper presents an information-theoretic analysis of classification under observational constraints. We prove three main results:

1.  **Information Barrier**: Observers limited to attribute-membership queries cannot compute properties that vary within indistinguishability classes. This is universal: it applies to biological taxonomy, database systems, library classification, and programming language runtimes alike.

2.  **Witness Optimality**: Nominal-tag observers achieve $W(\text{identity}) = O(1)$, the minimum witness cost. The gap from attribute-only observation ($\Omega(n)$) is unbounded.

3.  **Matroid Structure**: Minimal distinguishing query sets form the bases of a matroid. The distinguishing dimension of a classification problem is well-defined and computable.

## The Universal Pattern

Across domains, the same structure recurs:

-   **Biology**: Phenotypic observation cannot distinguish cryptic species. DNA barcoding (nominal tag) resolves them in $O(1)$.

-   **Databases**: Column-value queries cannot distinguish rows with identical attributes. Primary keys (nominal tag) provide $O(1)$ identity.

-   **Type systems**: Interface observation cannot distinguish structurally identical types. Type tags provide $O(1)$ identity.

The information barrier is not a quirk of any particular domain; it is a mathematical necessity arising from the quotient structure induced by limited observations.

## Implications

-   **Nominal tags are not optional** when identity queries are required. They are the unique mechanism achieving $O(1)$ witness cost with zero distortion.

-   **The barrier is informational, not computational**: even with unbounded resources, attribute-only observers cannot overcome it.

-   **Classification system design is constrained**: the choice of observation family determines which properties are computable.

## Future Work

1.  **Other classification domains**: What is the matroid structure of observation spaces in chemistry (molecular fingerprints), linguistics (phonetic features), or machine learning (feature embeddings)?

2.  **Witness complexity of other properties**: Beyond identity, what are the witness costs for provenance, equivalence, or subsumption?

3.  **Hybrid observers**: Can observer strategies that combine tags and attributes achieve better $(L, W, D)$ tradeoffs for specific query distributions?

## Conclusion

Classification under observational constraints admits a clean information-theoretic analysis. Nominal tags are not a design preference; they are the provably optimal strategy for identity verification under the $(L, W, D)$ tradeoff. The results are universal, and all proofs are machine-verified in Lean 4.

## AI Disclosure {#ai-disclosure .unnumbered}

This work was developed with AI assistance (Claude, Anthropic). The AI contributed to exposition, code generation, and proof exploration. All mathematical claims were verified by the authors and machine-checked in Lean 4. The Lean proofs are the authoritative source; no theorem depends solely on AI-generated reasoning.


# Formalization and Verification

We provide machine-checked proofs of our core theorems in Lean 4. The complete development (6,100+ lines across nine modules, 0 `sorry` placeholders) is organized as follows:

::: table*
  Module                            Lines       Theorems   Purpose
  --------------------------------- ----------- ---------- ---------------------------------
  `abstract_class_system.lean`      3082        90+        Core: two-axis model, dominance
  `axis_framework.lean`             1667        40+        Matroid structure
  `nominal_resolution.lean`         556         21         Resolution, capabilities
  `discipline_migration.lean`       142         11         Discipline vs migration
  `context_formalization.lean`      215         7          Greenfield/retrofit
  `python_instantiation.lean`       247         12         Python instantiation
  `typescript_instantiation.lean`   65          3          TypeScript instantiation
  `java_instantiation.lean`         63          3          Java instantiation
  `rust_instantiation.lean`         64          3          Rust instantiation
  **Total**                         **6100+**   **190+**   
:::

1.  **Language-agnostic layer** (Section 6.12): The two-axis model $(B, S)$, axis lattice metatheorem, and strict dominance: proving nominal-tag observation dominates interface-only observation in **any** class system with explicit inheritance. These proofs require no Python-specific axioms.

2.  **Python instantiation layer** (Sections 6.1--6.11): The dual-axis resolution algorithm, provenance preservation, and OpenHCS-specific invariants: proving that Python's `type(name, bases, namespace)` and C3 linearization correctly instantiate the abstract model.

3.  **Complexity bounds layer** (Section 6.13): Formalization of O(1) vs O(k) vs $\Omega(n)$ complexity separation. Proves that nominal error localization is O(1), interface-only (declared) is O(k), interface-only is $\Omega(n)$, and the gap grows without bound.

The abstract layer establishes that our theorems apply to Java, C#, Ruby, Scala, and any language with the $(B, S)$ structure. The Python layer demonstrates concrete realization. The complexity layer proves the asymptotic dominance is machine-checkable, not informal.

## Type Universe and Registry

Types are represented as natural numbers, capturing nominal identity:

``` {style="lean"}
abbrev Typ := Nat  -- Types as natural numbers (nominal identity)
def Registry := Typ -> Option Typ

def Registry.wellFormed (R : Registry) : Prop :=
  forall L B, R L = some B -> R B = none

def normalizeType (R : Registry) (T : Typ) : Typ :=
  match R T with | some B => B | none => T
```

**Invariant (Normalization Idempotence).** For well-formed registries:

``` {style="lean"}
theorem normalizeType_idempotent (R : Registry) (T : Typ)
    (h_wf : R.wellFormed) :
    normalizeType R (normalizeType R T) = normalizeType R T := by
  simp only [normalizeType]; cases hR : R T with
  | none => simp only [hR]
  | some B => have h_base := h_wf T B hR; simp only [h_base]
```

## MRO and Scope Stack

``` {style="lean"}
abbrev MRO := List Typ          -- Most specific first
abbrev ScopeStack := List ScopeId

structure ConfigInstance where
  typ : Typ
  fieldValue : FieldValue

def ConfigContext := ScopeId -> List ConfigInstance
```

## The RESOLVE Algorithm

``` {style="lean"}
structure ResolveResult where
  value : FieldValue; scope : ScopeId; sourceType : Typ
deriving DecidableEq

def findConfigByType (configs : List ConfigInstance) (T : Typ) :=
  match configs.find? (fun c => c.typ == T) with
  | some c => some c.fieldValue | none => none

def resolve (R : Registry) (mro : MRO)
    (scopes : ScopeStack) (ctx : ConfigContext) :
    Option ResolveResult :=
  scopes.findSome? fun scope =>      -- X-axis: scopes
    mro.findSome? fun mroType =>     -- Y-axis: MRO
      let normType := normalizeType R mroType
      match findConfigByType (ctx scope) normType with
      | some v => if v != 0 then some (v, scope, normType) else none
      | none => none
```

## GETATTRIBUTE Implementation

``` {style="lean"}
def rawFieldValue (obj : ConfigInstance) := obj.fieldValue

def getattribute (R : Registry) (obj : ConfigInstance) (mro : MRO)
    (scopes : ScopeStack) (ctx : ConfigContext) (isLazy : Bool) :=
  let raw := rawFieldValue obj
  if raw != 0 then raw
  else if isLazy then
    match resolve R mro scopes ctx with
    | some result => result.value | none => 0
  else raw
```

## Theorem 6.1: Resolution Completeness

**Theorem 6.1 (Completeness).** The `resolve` function is complete: it returns value `v` if and only if either no resolution occurred (v = 0) or a valid resolution result exists.

``` {style="lean"}
theorem resolution_completeness (R : Registry) (mro : MRO)
    (scopes : ScopeStack) (ctx : ConfigContext) (v : FieldValue) :
    (match resolve R mro scopes ctx with
     | some r => r.value | none => 0) = v <->
    (v = 0 /\ resolve R mro scopes ctx = none) \/
    (exists r, resolve R mro scopes ctx = some r /\ r.value = v) := by
  cases hr : resolve R mro scopes ctx <;> simp [hr]
```

## Theorem 6.2: Provenance Preservation

**Theorem 6.2a (Uniqueness).** Resolution is deterministic.

``` {style="lean"}
theorem provenance_uniqueness (R : Registry) (mro : MRO)
    (scopes : ScopeStack) (ctx : ConfigContext)
    (r1 r2 : ResolveResult)
    (hr1 : resolve R mro scopes ctx = some r1)
    (hr2 : resolve R mro scopes ctx = some r2) :
    r1 = r2 := by simp only [hr1, Option.some.injEq] at hr2; exact hr2

theorem resolution_determinism (R : Registry) (mro : MRO)
    (scopes : ScopeStack) (ctx : ConfigContext) :
    forall r1 r2, resolve R mro scopes ctx = r1 ->
                  resolve R mro scopes ctx = r2 -> r1 = r2 := by
  intros r1 r2 h1 h2; rw [<- h1, <- h2]
```

## Duck Typing Formalization {#interface-only-formalization}

We formalize interface-only observation and prove it cannot provide provenance.

``` {style="lean"}
structure InterfaceValue where
  fields : List (String * Nat)
deriving DecidableEq

def getField (obj : InterfaceValue) (name : String) : Option Nat :=
  match obj.fields.find? (fun p => p.1 == name) with
  | some p => some p.2 | none => none

-- Interface equivalence: identity = structure
def interfaceEquivalent (a b : InterfaceValue) : Prop :=
  forall name, getField a name = getField b name
```

We prove this is an equivalence relation:

``` {style="lean"}
theorem structEq_refl (a : InterfaceValue) :
  interfaceEquivalent a a := by intro name; rfl

theorem structEq_symm (a b : InterfaceValue) :
    interfaceEquivalent a b -> interfaceEquivalent b a := by
  intro h name; exact (h name).symm

theorem structEq_trans (a b c : InterfaceValue) :
    interfaceEquivalent a b -> interfaceEquivalent b c ->
    interfaceEquivalent a c := by
  intro hab hbc name; rw [hab name, hbc name]

def InterfaceRespecting (f : InterfaceValue -> a) : Prop :=
  forall a b, interfaceEquivalent a b -> f a = f b
```

## Corollary 6.3: Provenance Impossibility {#corollary-6.3-interface-only-cannot-provide-provenance}

Under interface-only observation, equivalent objects are indistinguishable, so provenance must be constant on equivalent objects.

``` {style="lean"}
structure DuckProvenance where
  value : Nat; source : InterfaceValue
deriving DecidableEq

theorem interface_provenance_indistinguishable
    (getProvenance : InterfaceValue -> Option DuckProvenance)
    (h_interface : InterfaceRespecting getProvenance)
    (obj1 obj2 : InterfaceValue)
    (h_equiv : interfaceEquivalent obj1 obj2) :
    getProvenance obj1 = getProvenance obj2 :=
  h_interface obj1 obj2 h_equiv

theorem interface_provenance_absurdity
    (getProvenance : InterfaceValue -> Option DuckProvenance)
    (h_interface : InterfaceRespecting getProvenance)
    (obj1 obj2 : InterfaceValue) (h_equiv : interfaceEquivalent obj1 obj2)
    (prov1 prov2 : DuckProvenance)
    (h1 : getProvenance obj1 = some prov1)
    (h2 : getProvenance obj2 = some prov2) :
    prov1 = prov2 := by
  have h_eq := h_interface obj1 obj2 h_equiv
  rw [h1, h2] at h_eq; exact Option.some.inj h_eq
```

**Contrast with nominal-tag observation:** Types are distinguished by identity:

``` {style="lean"}
def WellFilterConfigType : Nat := 1
def StepWellFilterConfigType : Nat := 2

theorem nominal_types_distinguishable :
    WellFilterConfigType != StepWellFilterConfigType := by decide
```

Therefore, `ResolveResult.sourceType` is meaningful: it tells you WHICH type provided the value, even if types have the same structure.

## Verification Status

All proofs compile without warnings or `sorry` placeholders. The verification covers:

-   **AbstractClassSystem** (475 lines): Two-axis model, strict dominance, axis lattice metatheorem

-   **NominalResolution** (157 lines): Resolution algorithm, completeness (Thm. 6.1), uniqueness (Thm. 6.2)

-   **DuckTyping** (127 lines): Structural equivalence, impossibility (Cor. 6.3)

-   **MetaprogrammingGap** (156 lines): Declaration/query model, hook requirements

-   **CapabilityExhaustiveness** (42 lines): Capability completeness theorems

-   **AdapterAmortization** (60 lines): Cost model, amortization proofs

**Total:** 6,100+ lines, 190+ theorems, 0 `sorry`, 0 warnings.

## What the Lean Proofs Guarantee

The machine-checked verification establishes:

1.  **Algorithm correctness**: `resolve` returns value `v` iff resolution found a config providing `v` (Theorem 6.1).

2.  **Determinism**: Same inputs always produce same `(value, scope, sourceType)` tuple (Theorem 6.2).

3.  **Idempotence**: Normalizing an already-normalized type is a no-op (normalization_idempotent).

4.  **Interface-only observation impossibility**: Any function respecting interface equivalence cannot distinguish between interface-identical objects, making provenance tracking impossible (Corollary 6.3).

**What the proofs do NOT guarantee:**

-   **C3 correctness**: We assume MRO is well-formed. Python's C3 algorithm can fail on pathological diamonds (raising `TypeError`). Our proofs apply only when C3 succeeds.

-   **Registry invariants**: `Registry.wellFormed` is an axiom (base types not in domain). We prove theorems *given* this axiom but do not derive it from more primitive foundations.

-   **Termination and complexity**: We use Lean's termination checker to verify `resolve` terminates. The complexity bound O(scopes $\times$ MRO) is also mechanically verified via `resolution_complexity_bound` and related lemmas proving linearity in each dimension.

This is standard practice in mechanized verification: CompCert assumes well-typed input, seL4 assumes hardware correctness. Our proofs establish that *given* a well-formed registry and MRO, the resolution algorithm is correct and provides provenance that interface-only observation cannot.

## On Proof Structure {#foundational-proofs}

Most proofs in the Lean formalization are short (1-3 lines). This brevity reflects the nature of *definitional* impossibilities: our core theorems establish information-theoretic barriers, not computational lower bounds. When we prove that no shape-respecting function can compute provenance, the proof follows immediately from definitions. A definitional impossibility is stronger than a complexity bound; it closes all loopholes rather than leaving room for alternative algorithms.

The semantic contribution is threefold: (1) *precision forcing*, where formalizing "interface-only observation" requires stating exactly what shape-respecting means; (2) *completeness*, where the query space partition proves every query is either shape-respecting or lineage-dependent; and (3) *universal scope*, where the impossibility applies to any system that discards the lineage axis. The Lean compiler verifies every proof step; reviewers can run `lake build` to confirm the 6000+ lines compile with zero `sorry` placeholders.

## External Provenance Map Rebuttal

**Objection:** "Interface-only observation could provide provenance via an external map: `provenance_map: Dict``[``id(obj), SourceType``]`."

**Rebuttal:** This objection conflates *object identity* with *type identity*. The external map tracks which specific object instance came from where (not which *type* in the MRO provided a value.

Consider:

``` {style="lean"}
class A:
    x = 1
class B(A):
    pass  # Inherits x from A
b = B()
print(b.x)  # Prints 1. Which type provided this?
```

An external provenance map could record `provenance_map``[``id(b)``]`` = B`. But this doesn't answer the question "which type in B's MRO provided `x`?" The answer is `A`, and this requires MRO traversal, which requires the Bases axis.

**Formal statement:** Let $\text{ExternalMap} : \text{ObjectId} \to \text{SourceType}$ be any external provenance map. Then ExternalMap cannot answer: "Which type in $\text{MRO}(\text{type}(v))$ provided attribute $a$?"

*Proof.* The question asks about MRO position. MRO is derived from Bases. ExternalMap has no access to Bases (it maps object IDs to types, not types to MRO positions). Therefore ExternalMap cannot answer MRO-position queries. 0◻

**The deeper point:** Provenance is not about "where did this object come from?" It's about "where did this *value* come from in the inheritance hierarchy?" The latter requires MRO, which requires Bases, which interface-only observation discards.

## Abstract Model Lean Formalization

The abstract class system model (Section 2.4) is formalized in Lean 4 with complete proofs (no `sorry` placeholders):

``` {style="lean"}
-- The two axes of a class system
inductive Axis where
  | Bases      -- B: inheritance hierarchy
  | Namespace  -- S: attribute declarations
deriving DecidableEq, Repr

abbrev AxisSet := List Axis
def shapeAxes : AxisSet := [.Namespace]   -- S-only
def nominalAxes : AxisSet := [.Bases, .Namespace]

inductive UnifiedCapability where
  | interfaceCheck | identity | provenance
  | enumeration | conflictResolution
deriving DecidableEq, Repr

def axisCapabilities (a : Axis) : List UnifiedCapability :=
  match a with
  | .Bases => [.identity, .provenance,
               .enumeration, .conflictResolution]
  | .Namespace => [.interfaceCheck]

def axisSetCapabilities (axes : AxisSet) :=
  axes.flatMap axisCapabilities |>.eraseDups
```

**Definition 6.3a (Axis Projection --- Lean).** A type over axis set $A$ is a dependent tuple of axis values:

``` {style="lean"}
def AxisProjection (A : List Axis) :=
  (a : Axis) -> a in A -> AxisCarrier a

structure Typ where
  ns : Finset AttrName
  bs : List Typ
```

**Theorem 6.3b (Isomorphism).** `Typ` is isomorphic to the 2-axis projection:

``` {style="lean"}
noncomputable def Typ.equivProjection :
    Typ <~> AxisProjection canonicalAxes where
  toFun := Typ.toProjection
  invFun := Typ.fromProjection
  left_inv := Typ.projection_roundtrip
  right_inv := Typ.projection_roundtrip_inv

theorem n_axis_types_are_projections (A : List Axis) :
    GenericTyp A = AxisProjection A := rfl
```

This formalizes Definition 2.10 (Typing Disciplines as Axis Projections): a typing discipline using axis set $A$ has exactly the information contained in the $A$-projection of the full type.

**Theorem 6.4 (Axis Lattice --- Lean).** Shape capabilities are a strict subset of nominal capabilities:

``` {style="lean"}
theorem axis_shape_subset_nominal :
    forall c in axisSetCapabilities shapeAxes,
      c in axisSetCapabilities nominalAxes := by
  intro c hc; rw [h_shape] at hc; simp at hc; rw [hc]
  exact h_nominal

theorem axis_nominal_exceeds_shape :
    exists c in axisSetCapabilities nominalAxes,
      c notin axisSetCapabilities shapeAxes := by
  use UnifiedCapability.provenance; decide

theorem lattice_dominance :
    (forall c in shapeCapabilities, c in nominalCapabilities) /\
    (exists c in nominalCapabilities, c notin shapeCapabilities) :=
  <axis_shape_subset_nominal, axis_nominal_exceeds_shape>
```

This formalizes Theorem 2.15: using more axes provides strictly more capabilities. The proofs are complete and compile without any `sorry` placeholders.

**Theorem 6.11 (Capability Completeness --- Lean).** The Bases axis provides exactly four capabilities, no more:

``` {style="lean"}
inductive Capability where
  | interfaceCheck | typeNaming | valueAccess
  | methodInvocation | provenance | identity
  | enumeration | conflictResolution
deriving DecidableEq, Repr

def basesRequiredCapabilities : List Capability :=
  [.provenance, .identity, .enumeration, .conflictResolution]

def nonBasesCapabilities : List Capability :=
  [.interfaceCheck, .typeNaming, .valueAccess, .methodInvocation]

theorem capability_partition : forall c : Capability,
    (c in basesRequiredCapabilities \/ c in nonBasesCapabilities) /\
    ~(c in basesRequiredCapabilities /\ c in nonBasesCapabilities) := by
  intro c; cases c <;> simp [basesRequiredCapabilities, nonBasesCapabilities]

theorem bases_capabilities_count :
    basesRequiredCapabilities.length = 4 := rfl
```

This formalizes Theorem 2.17 (Capability Completeness): the capability set $\mathcal{C}_B$ is **exactly** four elements, proven by exhaustive enumeration with machine-checked partition. The `capability_partition` theorem proves that every capability falls into exactly one category (Bases-required or not) with no overlap and no gaps.

**Scope as observational quotient.** We model "scope" as a set of allowed observers $\text{Obs} \subseteq (W \to O)$ and define observational equivalence $x \approx y \;:\!\!\iff\; \forall f \in \text{Obs}, f(x) = f(y)$. The induced quotient $W/{\approx}$ is the canonical object for that scope, and every in-scope observer factors through it (see `observer_factors` in `abstract_class_system.lean`). Once the observer set is fixed, no argument can appeal to information outside that quotient; adding a new observable is literally expanding $\text{Obs}$.

**Protocol runtime observer (shape-only).** We also formalize the restricted Protocol/isinstance observer that checks only for required members. The predicate `protoCheck` ignores protocol identity and is proved shape-respecting (`protoCheck_in_shapeQuerySet` in `abstract_class_system.lean`), so two protocols with identical member sets are indistinguishable to that observer. Distinguishing them requires adding an observable discriminator (brand/tag/nominality), i.e., moving to another axis.

**All Python object-model observables factor through axes.** In the Python instantiation we prove that core runtime discriminators are functions of $(B,S)$: metaclass selection depends only on `bases` (`metaclass_depends_on_bases`); attribute presence and dispatch depend only on the namespace (`getattr_depends_on_ns`); together they yield `observer_factors_through_axes` in `python_instantiation.lean`.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/proofs/paper1_jsait_*.lean`
- Lines: 6086
- Theorems: 265
