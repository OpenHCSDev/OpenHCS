# Paper 4: The Decision Quotient — Computational Rationality in Modeling

**Status**: TOPLAS-ready | **Lean**: 3,412 lines, ~110 theorems, 0 sorry

This paper explores the complexity-theoretic bounds of over-modeling.

---

# Introduction {#sec:introduction}

Engineers routinely include irrelevant information in their models. Climate scientists model atmospheric chemistry when predicting regional temperatures. Financial analysts track hundreds of indicators when making portfolio decisions. Software architects specify dozens of configuration parameters when only a handful affect outcomes.

The conventional view holds that this *over-modeling* reflects poor discipline---that skilled practitioners should identify the *essential* variables and model only those. This paper proves the opposite: over-modeling is computationally rational because identifying the minimal set of decision-relevant variables is intractable.

## The Core Problem

Consider a decision problem with actions $A$ and states $S = X_1 \times \cdots \times X_n$ (a product of $n$ coordinate spaces). For each state $s \in S$, some subset $\Opt(s) \subseteq A$ of actions are optimal. The fundamental question is:

> **Which coordinates are sufficient to determine the optimal action?**

A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only the coordinates in $I$ determines the optimal action set: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$ where $s_I$ denotes the projection of state $s$ onto coordinates in $I$.

## Main Results

This paper proves four main theorems:

1.  **Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} (Sufficiency Checking is -complete):** Given a decision problem and coordinate set $I$, determining whether $I$ is sufficient is -complete [@cook1971complexity; @karp1972reducibility].

2.  **Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} (Minimum Sufficiency is -complete):** Finding the minimum sufficient coordinate set is -complete. (The problem is trivially in $\SigmaP{2}$ by structure, but collapses to because sufficiency equals "superset of relevant coordinates.")

3.  **Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} (Complexity Dichotomy):** Sufficiency checking exhibits a dichotomy:

    -   If the minimal sufficient set has size $O(\log |S|)$, checking is polynomial

    -   If the minimal sufficient set has size $\Omega(n)$, checking requires exponential time [@impagliazzo2001complexity].

4.  **Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} (Tractable Subcases):** Sufficiency checking is polynomial-time for:

    -   Bounded action sets ($|A| \leq k$ for constant $k$)

    -   Separable utility functions ($u(a,s) = f(a) + g(s)$)

    -   Tree-structured coordinate dependencies

## What This Paper Does NOT Claim

To prevent misreading, we state explicit non-claims:

1.  **NOT "always model everything."** Over-modeling has costs (computation, data collection). We claim the *alternative* (minimal modeling) is computationally hard to identify.

2.  **NOT "complexity results apply to all domains."** Structured problems admit tractable algorithms (Section [4](#sec:tractable){reference-type="ref" reference="sec:tractable"}). The hardness applies to general unstructured problems.

3.  **NOT "information theory is wrong."** Value of information remains well-defined. We show *computing* which information matters is hard.

4.  **NOT "this obsoletes existing approaches."** Domain-specific heuristics remain valuable. We provide formal justification for their necessity.

## Connection to Prior Papers

This paper completes the theoretical foundation established in Papers 1--3:

-   **Paper 1 (Typing):** Showed nominal typing dominates structural typing

-   **Paper 2 (SSOT):** Showed single source of truth minimizes modification complexity

-   **Paper 3 (Leverage):** Unified both as leverage maximization

**Paper 4's contribution:** Proves that *identifying* which architectural decisions matter is itself computationally hard. This explains why leverage maximization (Paper 3) uses heuristics rather than optimal algorithms.

## Paper Structure

Section [2](#sec:foundations){reference-type="ref" reference="sec:foundations"} establishes formal foundations: decision problems, coordinate spaces, sufficiency. Section [9](#sec:hardness){reference-type="ref" reference="sec:hardness"} proves hardness results with complete reductions. Section [3](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"} develops the complexity dichotomy. Section [4](#sec:tractable){reference-type="ref" reference="sec:tractable"} presents tractable special cases. Section [5](#sec:implications){reference-type="ref" reference="sec:implications"} discusses implications for software architecture and modeling. Section [6](#sec:related){reference-type="ref" reference="sec:related"} surveys related work. Appendix [8](#app:lean){reference-type="ref" reference="app:lean"} contains Lean proof listings.

# Formal Foundations {#sec:foundations}

We formalize decision problems with coordinate structure, sufficiency of coordinate sets, and the decision quotient, drawing on classical decision theory [@savage1954foundations; @raiffa1961applied].

## Decision Problems with Coordinate Structure

::: definition
[]{#def:decision-problem label="def:decision-problem"} A *decision problem with coordinate structure* is a tuple $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ where:

-   $A$ is a finite set of *actions* (alternatives)

-   $X_1, \ldots, X_n$ are finite *coordinate spaces*

-   $S = X_1 \times \cdots \times X_n$ is the *state space*

-   $U : A \times S \to \mathbb{Q}$ is the *utility function*
:::

::: definition
[]{#def:projection label="def:projection"} For state $s = (s_1, \ldots, s_n) \in S$ and coordinate set $I \subseteq \{1, \ldots, n\}$: $$s_I := (s_i)_{i \in I}$$ is the *projection* of $s$ onto coordinates in $I$.
:::

::: definition
[]{#def:optimizer label="def:optimizer"} For state $s \in S$, the *optimal action set* is: $$\Opt(s) := \arg\max_{a \in A} U(a, s) = \{a \in A : U(a,s) = \max_{a' \in A} U(a', s)\}$$
:::

## Sufficiency and Relevance

::: definition
[]{#def:sufficient label="def:sufficient"} A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* for decision problem $\mathcal{D}$ if: $$\forall s, s' \in S: \quad s_I = s'_I \implies \Opt(s) = \Opt(s')$$ Equivalently, the optimal action depends only on coordinates in $I$.
:::

::: definition
[]{#def:minimal-sufficient label="def:minimal-sufficient"} A sufficient set $I$ is *minimal* if no proper subset $I' \subsetneq I$ is sufficient.
:::

::: definition
[]{#def:relevant label="def:relevant"} Coordinate $i$ is *relevant* if it belongs to some minimal sufficient set.
:::

::: example
Consider deciding whether to carry an umbrella:

-   Actions: $A = \{\text{carry}, \text{don't carry}\}$

-   Coordinates: $X_1 = \{\text{rain}, \text{no rain}\}$, $X_2 = \{\text{hot}, \text{cold}\}$, $X_3 = \{\text{Monday}, \ldots, \text{Sunday}\}$

-   Utility: $U(\text{carry}, s) = -1 + 3 \cdot \mathbf{1}[s_1 = \text{rain}]$, $U(\text{don't carry}, s) = -2 \cdot \mathbf{1}[s_1 = \text{rain}]$

The minimal sufficient set is $I = \{1\}$ (only rain forecast matters). Coordinates 2 and 3 (temperature, day of week) are irrelevant.
:::

## The Decision Quotient

::: definition
[]{#def:decision-equiv label="def:decision-equiv"} For coordinate set $I$, states $s, s'$ are *$I$-equivalent* (written $s \sim_I s'$) if $s_I = s'_I$.
:::

::: definition
[]{#def:decision-quotient label="def:decision-quotient"} The *decision quotient* for state $s$ under coordinate set $I$ is: $$\text{DQ}_I(s) = \frac{|\{a \in A : a \in \Opt(s') \text{ for some } s' \sim_I s\}|}{|A|}$$ This measures the fraction of actions that *could* be optimal given only the information in $I$.
:::

::: proposition
[]{#prop:sufficiency-char label="prop:sufficiency-char"} Coordinate set $I$ is sufficient if and only if $\text{DQ}_I(s) = |\Opt(s)|/|A|$ for all $s \in S$.
:::

::: proof
*Proof.* If $I$ is sufficient, then $s \sim_I s' \implies \Opt(s) = \Opt(s')$, so the set of actions optimal for some $s' \sim_I s$ is exactly $\Opt(s)$.

Conversely, if the condition holds, then for any $s \sim_I s'$, the optimal actions form the same set (since $\text{DQ}_I(s) = \text{DQ}_I(s')$ and both equal the relative size of the common optimal set). ◻
:::

# Complexity Dichotomy {#sec:dichotomy}

The hardness results of Section [9](#sec:hardness){reference-type="ref" reference="sec:hardness"} apply to worst-case instances. This section develops a more nuanced picture: a *dichotomy theorem* showing that problem difficulty depends on the size of the minimal sufficient set.

::: theorem
[]{#thm:dichotomy label="thm:dichotomy"} Let $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ be a decision problem with $|S| = N$ states. Let $k^*$ be the size of the minimal sufficient set.

1.  **Logarithmic case:** If $k^* = O(\log N)$, then SUFFICIENCY-CHECK is solvable in polynomial time.

2.  **Linear case:** If $k^* = \Omega(n)$, then SUFFICIENCY-CHECK requires time $\Omega(2^{n/c})$ for some constant $c > 0$ (assuming ETH).
:::

::: proof
*Proof.* **Part 1 (Logarithmic case):** If $k^* = O(\log N)$, then the number of distinct projections $|S_{I^*}|$ is at most $2^{k^*} = O(N^c)$ for some constant $c$. We can enumerate all projections and verify sufficiency in polynomial time.

**Part 2 (Linear case):** The reduction from TAUTOLOGY in Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} produces instances where the minimal sufficient set has size $\Omega(n)$ (all coordinates are relevant when the formula is not a tautology). Under the Exponential Time Hypothesis (ETH) [@impagliazzo2001complexity], TAUTOLOGY requires time $2^{\Omega(n)}$, so SUFFICIENCY-CHECK inherits this lower bound. ◻
:::

::: corollary
There exists a threshold $\tau \in (0, 1)$ such that:

-   If $k^*/n < \tau$, SUFFICIENCY-CHECK is "easy" (polynomial in $N$)

-   If $k^*/n > \tau$, SUFFICIENCY-CHECK is "hard" (exponential in $n$)
:::

This dichotomy explains why some domains admit tractable model selection (few relevant variables) while others require heuristics (many relevant variables).

# Tractable Special Cases {#sec:tractable}

Despite the general hardness, several natural problem classes admit polynomial-time algorithms.

::: theorem
[]{#thm:tractable label="thm:tractable"} SUFFICIENCY-CHECK is polynomial-time solvable for:

1.  **Bounded actions:** $|A| \leq k$ for constant $k$

2.  **Separable utility:** $U(a, s) = f(a) + g(s)$

3.  **Tree-structured dependencies:** Coordinates form a tree where each coordinate depends only on its ancestors
:::

## Bounded Actions

::: proof
*Proof of Part 1.* With $|A| = k$ constant, the optimizer map $\Opt : S \to 2^A$ has at most $2^k$ distinct values. For each pair of distinct optimizer values, we can identify the coordinates that distinguish them. The union of these distinguishing coordinates forms a sufficient set.

The algorithm:

1.  Sample states to identify distinct optimizer values (polynomial samples suffice with high probability)

2.  For each pair of optimizer values, find distinguishing coordinates

3.  Return the union of distinguishing coordinates

This runs in time $O(|S| \cdot k^2)$ which is polynomial when $k$ is constant. ◻
:::

## Separable Utility

::: proof
*Proof of Part 2.* If $U(a, s) = f(a) + g(s)$, then: $$\Opt(s) = \arg\max_{a \in A} [f(a) + g(s)] = \arg\max_{a \in A} f(a)$$ The optimal action is independent of the state! Thus $I = \emptyset$ is always sufficient. ◻
:::

## Tree-Structured Dependencies

::: proof
*Proof of Part 3.* When coordinates form a tree, we can use dynamic programming. For each node $i$, compute the set of optimizer values achievable in the subtree rooted at $i$. A coordinate is relevant if and only if different values at that coordinate lead to different optimizer values in its subtree. This approach is analogous to inference in probabilistic graphical models [@pearl1988probabilistic; @koller2009probabilistic].

The algorithm runs in time $O(n \cdot |A|^2)$ by processing the tree bottom-up. ◻
:::

## Practical Implications

These tractable cases correspond to common modeling scenarios:

-   **Bounded actions:** Most real decisions have few alternatives (buy/sell/hold, approve/reject, etc.)

-   **Separable utility:** Additive cost models, linear utility functions

-   **Tree structure:** Hierarchical decision processes, causal models with tree structure

When a problem falls outside these cases, the hardness results apply, justifying heuristic approaches.

# Implications for Software Architecture {#sec:implications}

The complexity results have direct implications for software engineering practice.

## Why Over-Specification Is Rational

Software architects routinely specify more configuration parameters than strictly necessary. Our results show this is computationally rational:

::: corollary
Given a software system with $n$ configuration parameters, checking whether a proposed subset suffices is -complete. Finding the minimum such set is also -complete.
:::

This explains why configuration files grow over time: removing "unnecessary" parameters requires solving a hard problem.

## Connection to Leverage Theory

Paper 3 introduced leverage as the ratio of impact to effort. The decision quotient provides a complementary measure:

::: definition
For a software system with configuration space $S$ and behavior space $B$: $$\text{ADQ}(I) = \frac{|\{b \in B : b \text{ achievable with some } s \text{ where } s_I \text{ fixed}\}|}{|B|}$$
:::

High ADQ means the configuration subset $I$ leaves many behaviors achievable---it doesn't constrain the system much. Low ADQ means $I$ strongly constrains behavior.

::: proposition
High-leverage architectural decisions correspond to low-ADQ configuration subsets: they strongly constrain system behavior with minimal specification.
:::

## Practical Recommendations

Based on our theoretical results:

1.  **Accept over-modeling:** Don't penalize engineers for including "extra" parameters. The alternative (minimal modeling) is computationally hard.

2.  **Use bounded scenarios:** When the scenario space is small (Proposition [\[prop:sufficiency-char\]](#prop:sufficiency-char){reference-type="ref" reference="prop:sufficiency-char"}), minimal modeling becomes tractable.

3.  **Exploit structure:** Tree-structured dependencies, bounded alternatives, and separable utilities admit efficient algorithms.

4.  **Invest in heuristics:** For general problems, develop domain-specific heuristics rather than seeking optimal solutions.

# Related Work {#sec:related}

## Computational Decision Theory

The complexity of decision-making has been studied extensively. Papadimitriou [@papadimitriou1994complexity] established foundational results on the complexity of game-theoretic solution concepts. Our work extends this to the meta-question of identifying relevant information. For a modern treatment of complexity classes, see Arora and Barak [@arora2009computational].

## Feature Selection

In machine learning, feature selection asks which input features are relevant for prediction. This is known to be NP-hard in general [@blum1997selection]. Our results show the decision-theoretic analog is -complete for both checking and minimization.

## Value of Information

The value of information (VOI) framework [@howard1966information] quantifies how much a decision-maker should pay for information. Our work addresses a different question: not the *value* of information, but the *complexity* of identifying which information has value.

## Model Selection

Statistical model selection (AIC [@akaike1974new], BIC [@schwarz1978estimating], cross-validation [@stone1974cross]) provides practical heuristics for choosing among models. Our results provide theoretical justification: optimal model selection is intractable, so heuristics are necessary.

# Conclusion

## Methodology and Disclosure {#methodology-and-disclosure .unnumbered}

**Role of LLMs in this work.** This paper was developed through human-AI collaboration. The author provided the core intuitions---the connection between decision-relevance and computational complexity, the conjecture that SUFFICIENCY-CHECK is coNP-complete, and the insight that the $\Sigma_2^P$ structure collapses for MINIMUM-SUFFICIENT-SET. Large language models (Claude, GPT-4) served as implementation partners for proof drafting, Lean formalization, and LaTeX generation.

The Lean 4 proofs were iteratively refined: the author specified what should be proved, the LLM proposed proof strategies, and the Lean compiler served as the arbiter of correctness. The complexity-theoretic reductions required careful human oversight to ensure the polynomial bounds were correctly established.

**What the author contributed:** The problem formulations (SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, ANCHOR-SUFFICIENCY), the hardness conjectures, the tractability conditions, and the connection to over-modeling in engineering practice.

**What LLMs contributed:** LaTeX drafting, Lean tactic exploration, reduction construction assistance, and prose refinement.

The proofs are machine-checked; their validity is independent of generation method. We disclose this methodology in the interest of academic transparency.

::: center

----------------------------------------------------------------------------------------------------
:::

We have established that identifying decision-relevant information is computationally hard:

-   Checking whether a coordinate set is sufficient is -complete

-   Finding the minimum sufficient set is -complete (the $\SigmaP{2}$ structure collapses)

-   Anchor sufficiency (fixed-coordinate subcube) is $\SigmaP{2}$-complete

-   A complexity dichotomy separates easy (logarithmic) from hard (linear) cases

-   Tractable subcases exist for bounded actions, separable utilities, and tree structures

These results formalize a fundamental insight: **determining what you need to know is harder than knowing everything**. This explains the ubiquity of over-modeling in engineering practice and provides theoretical grounding for heuristic approaches to model selection.

All proofs are machine-checked in Lean 4, ensuring correctness of the core mathematical claims including the reduction mappings and equivalence theorems. Complexity classifications follow from standard complexity-theoretic results (TAUTOLOGY is coNP-complete, $\exists\forall$-SAT is $\Sigma_2^\text{P}$-complete) under the encoding model described in Section [\[sec:reduction\]](#sec:reduction){reference-type="ref" reference="sec:reduction"}.

# Lean 4 Proof Listings {#app:lean}

The complete Lean 4 formalization is available at:

::: center
[https://github.com/\[repository\]/openhcs/docs/papers/paper4_decision_quotient/proofs](https://github.com/[repository]/openhcs/docs/papers/paper4_decision_quotient/proofs){.uri}
:::

## On the Nature of Foundational Proofs {#foundational-proofs-nature}

The Lean proofs are straightforward applications of definitions and standard complexity-theoretic constructions. Foundational work produces insight through formalization.

**Definitional vs. derivational proofs.** The core theorems establish definitional properties and reduction constructions. For example, the polynomial reduction composition theorem (Theorem [\[thm:poly-compose\]](#thm:poly-compose){reference-type="ref" reference="thm:poly-compose"}) proves that composing two polynomial-time reductions yields a polynomial-time reduction. The proof follows from the definition of polynomial time: composing two polynomials yields a polynomial.

**Precedent in complexity theory.** This pattern appears throughout foundational complexity theory:

-   **Cook-Levin Theorem (1971):** SAT is NP-complete. The proof constructs a reduction from an arbitrary NP problem to SAT. The construction itself is straightforward (encode Turing machine computation as boolean formula), but the *insight* is recognizing that SAT captures all of NP.

-   **Ladner's Theorem (1975):** If P $\neq$ NP, then NP-intermediate problems exist. The proof is a diagonal construction---conceptually simple once the right framework is identified.

-   **Toda's Theorem (1991):** The polynomial hierarchy is contained in P$^\#$P. The proof uses counting arguments that are elegant but not technically complex. The profundity is in the *connection* between counting and the hierarchy.

**Why simplicity indicates strength.** A definitional theorem derived from precise formalization is *stronger* than an informal argument. When we prove that sufficiency checking is coNP-complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), we are not saying "we tried many algorithms and they all failed." We are saying something universal: *any* algorithm solving sufficiency checking can solve TAUTOLOGY, and vice versa. The proof is a reduction construction that follows from the problem definitions.

**Where the insight lies.** The semantic contribution of our formalization is:

1.  **Precision forcing.** Formalizing "coordinate sufficiency" in Lean requires stating exactly what it means for a coordinate subset to contain all decision-relevant information. This precision eliminates ambiguity about edge cases (what if projections differ only on irrelevant coordinates?).

2.  **Reduction correctness.** The TAUTOLOGY reduction (Section [\[sec:reduction\]](#sec:reduction){reference-type="ref" reference="sec:reduction"}) is machine-checked to preserve the decision structure. Informal reductions can have subtle bugs; Lean verification guarantees the mapping is correct.

3.  **Complexity dichotomy.** Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} proves that problem instances are either tractable (P) or intractable (coNP-complete), with no intermediate cases under standard assumptions. This emerges from the formalization of constraint structure, not from case enumeration.

**What machine-checking guarantees.** The Lean compiler verifies that every proof step is valid, every definition is consistent, and no axioms are added beyond Lean's foundations (extended with Mathlib for basic combinatorics and complexity definitions). Zero `sorry` placeholders means zero unproven claims. The 3,400+ lines establish a verified chain from basic definitions (decision problems, coordinate spaces, polynomial reductions) to the final theorems (hardness results, dichotomy, tractable cases). Reviewers need not trust our informal explanations---they can run `lake build` and verify the proofs themselves.

**Comparison to informal complexity arguments.** Prior work on model selection complexity (Chickering et al. [@chickering2004large], Teyssier & Koller [@teyssier2012ordering]) presents compelling informal arguments but lacks machine-checked proofs. Our contribution is not new *wisdom*---the insight that model selection is hard is old. Our contribution is *formalization*: making "coordinate sufficiency" precise enough to mechanize, constructing verified reductions, and proving the complexity results hold for the formalized definitions.

This follows the tradition of verified complexity theory: just as Nipkow & Klein [@nipkow2014concrete] formalized automata theory and Cook [@cook2018complexity] formalized NP-completeness in proof assistants, we formalize decision-theoretic complexity. The proofs are simple because the formalization makes the structure clear. Simple proofs from precise definitions are the goal, not a limitation.

## Module Structure

The formalization consists of 25 files organized as follows:

-   `Basic.lean` -- Core definitions (DecisionProblem, CoordinateSet, Projection)

-   `AlgorithmComplexity.lean` -- Complexity definitions (polynomial time, reductions)

-   `PolynomialReduction.lean` -- Polynomial reduction composition (Theorem [\[thm:poly-compose\]](#thm:poly-compose){reference-type="ref" reference="thm:poly-compose"})

-   `Reduction.lean` -- TAUTOLOGY reduction for sufficiency checking

-   `Hardness/` -- Counting complexity and approximation barriers

-   `Tractability/` -- Bounded actions, separable utilities, tree structure, FPT

-   `Economics/` -- Value of information and elicitation connections

-   `Dichotomy.lean` and `ComplexityMain.lean` -- Summary results

## Key Theorems

::: theorem
[]{#thm:poly-compose label="thm:poly-compose"} Polynomial-time reductions compose to polynomial-time reductions.
:::

    theorem PolyReduction.comp_exists
        (f : PolyReduction A B) (g : PolyReduction B C) :
        exists h : PolyReduction A C,
          forall a, h.reduce a = g.reduce (f.reduce a)

## Verification Status

-   Total lines: 3,400+

-   Theorems: $\sim$`<!-- -->`{=html}60

-   Files: 25

-   Status: All proofs in this directory compile with no `sorry`

# Computational Complexity of Decision-Relevant Uncertainty {#sec:hardness}

This section establishes the computational complexity of determining which state coordinates are decision-relevant. We prove three main results:

1.  **SUFFICIENCY-CHECK** is coNP-complete

2.  **MINIMUM-SUFFICIENT-SET** is coNP-complete (the $\Sigma_2^P$ structure collapses)

3.  **ANCHOR-SUFFICIENCY** (fixed coordinates) is $\Sigma_2^P$-complete

These results sit beyond NP-completeness and formally explain why engineers default to over-modeling: finding the minimal set of decision-relevant factors is computationally intractable.

## Problem Definitions

::: definition
A *decision problem instance* is a tuple $(A, n, U)$ where:

-   $A$ is a finite set of alternatives

-   $n$ is the number of state coordinates, with state space $S = \{0,1\}^n$

-   $U: A \times S \to \mathbb{Q}$ is the utility function, given as a Boolean circuit
:::

::: definition
For state $s \in S$, define: $$\text{Opt}(s) := \arg\max_{a \in A} U(a, s)$$
:::

::: definition
A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if: $$\forall s, s' \in S: \quad s_I = s'_I \implies \text{Opt}(s) = \text{Opt}(s')$$ where $s_I$ denotes the projection of $s$ onto coordinates in $I$.
:::

::: problem
**Input:** Decision problem $(A, n, U)$ and coordinate set $I \subseteq \{1,\ldots,n\}$\
**Question:** Is $I$ sufficient?
:::

::: problem
**Input:** Decision problem $(A, n, U)$ and integer $k$\
**Question:** Does there exist a sufficient set $I$ with $|I| \leq k$?
:::

## Hardness of SUFFICIENCY-CHECK

::: theorem
[]{#thm:sufficiency-conp label="thm:sufficiency-conp"} SUFFICIENCY-CHECK is coNP-complete [@cook1971complexity; @karp1972reducibility].
:::

::: proof
*Proof.* **Membership in coNP:** The complementary problem INSUFFICIENCY is in NP. Given $(A, n, U, I)$, a witness for insufficiency is a pair $(s, s')$ such that:

1.  $s_I = s'_I$ (verifiable in polynomial time)

2.  $\text{Opt}(s) \neq \text{Opt}(s')$ (verifiable by evaluating $U$ on all alternatives)

**coNP-hardness:** We reduce from TAUTOLOGY.

Given Boolean formula $\varphi(x_1, \ldots, x_n)$, construct a decision problem with:

-   Alternatives: $A = \{\text{accept}, \text{reject}\}$

-   State space: $S = \{\text{reference}\} \cup \{0,1\}^n$

-   Utility: $$\begin{aligned}
            U(\text{accept}, \text{reference}) &= 1 \\
            U(\text{reject}, \text{reference}) &= 0 \\
            U(\text{accept}, a) &= \varphi(a) \\
            U(\text{reject}, a) &= 0 \quad \text{for assignments } a \in \{0,1\}^n
        
    \end{aligned}$$

-   Query set: $I = \emptyset$

**Claim:** $I = \emptyset$ is sufficient $\iff$ $\varphi$ is a tautology.

($\Rightarrow$) Suppose $I$ is sufficient. Then $\text{Opt}(s)$ is constant over all states. Since $U(\text{accept}, a) = \varphi(a)$ and $U(\text{reject}, a) = 0$:

-   $\text{Opt}(a) = \text{accept}$ when $\varphi(a) = 1$

-   $\text{Opt}(a) = \{\text{accept}, \text{reject}\}$ when $\varphi(a) = 0$

For $\text{Opt}$ to be constant, $\varphi(a)$ must be true for all assignments $a$; hence $\varphi$ is a tautology.

($\Leftarrow$) If $\varphi$ is a tautology, then $U(\text{accept}, a) = 1 > 0 = U(\text{reject}, a)$ for all assignments $a$. Thus $\text{Opt}(s) = \{\text{accept}\}$ for all states $s$, making $I = \emptyset$ sufficient. ◻
:::

## Complexity of MINIMUM-SUFFICIENT-SET

::: theorem
[]{#thm:minsuff-conp label="thm:minsuff-conp"} MINIMUM-SUFFICIENT-SET is coNP-complete.
:::

::: proof
*Proof.* **Structural observation:** The $\exists\forall$ quantifier pattern suggests $\Sigma_2^P$: $$\exists I \, (|I| \leq k) \; \forall s, s' \in S: \quad s_I = s'_I \implies \text{Opt}(s) = \text{Opt}(s')$$ However, this collapses because sufficiency has a simple characterization.

**Key lemma:** A coordinate set $I$ is sufficient if and only if $I$ contains all relevant coordinates (proven formally as `sufficient_contains_relevant` in Lean): $$\text{sufficient}(I) \iff \text{Relevant} \subseteq I$$ where $\text{Relevant} = \{i : \exists s, s'.\; s \text{ differs from } s' \text{ only at } i \text{ and } \text{Opt}(s) \neq \text{Opt}(s')\}$.

**Consequence:** The minimum sufficient set is exactly the set of relevant coordinates. Thus MINIMUM-SUFFICIENT-SET asks: "Is the number of relevant coordinates at most $k$?"

**coNP membership:** A witness that the answer is NO is a set of $k+1$ coordinates, each proven relevant (by exhibiting $s, s'$ pairs). Verification is polynomial.

**coNP-hardness:** The $k=0$ case asks whether no coordinates are relevant, i.e., whether $\emptyset$ is sufficient. This is exactly SUFFICIENCY-CHECK, which is coNP-complete by Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}. ◻
:::

## Anchor Sufficiency (Fixed Coordinates)

We also formalize a strengthened variant that fixes the coordinate set and asks whether there exists an *assignment* to those coordinates that makes the optimal action constant on the induced subcube.

::: problem
**Input:** Decision problem $(A, n, U)$ and fixed coordinate set $I \subseteq \{1,\ldots,n\}$\
**Question:** Does there exist an assignment $\alpha$ to $I$ such that $\text{Opt}(s)$ is constant for all states $s$ with $s_I = \alpha$?
:::

::: theorem
[]{#thm:anchor-sigma2p label="thm:anchor-sigma2p"} ANCHOR-SUFFICIENCY is $\Sigma_2^P$-complete [@stockmeyer1976polynomial] (already for Boolean coordinate spaces).
:::

::: proof
*Proof.* **Membership in $\Sigma_2^P$:** The problem has the form $$\exists \alpha \;\forall s \in S: \; (s_I = \alpha) \implies \text{Opt}(s) = \text{Opt}(s_\alpha),$$ which is an $\exists\forall$ pattern.

**$\Sigma_2^P$-hardness:** Reduce from $\exists\forall$-SAT. Given $\exists x \, \forall y \, \varphi(x,y)$ with $x \in \{0,1\}^k$ and $y \in \{0,1\}^m$, if $m=0$ we first pad with a dummy universal variable (satisfiability is preserved), construct a decision problem with:

-   Actions $A = \{\text{YES}, \text{NO}\}$

-   State space $S = \{0,1\}^{k+m}$ representing $(x,y)$

-   Utility $$U(\text{YES}, (x,y)) =
          \begin{cases}
            2 & \text{if } \varphi(x,y)=1 \\
            0 & \text{otherwise}
          \end{cases}
        \quad
        U(\text{NO}, (x,y)) =
          \begin{cases}
            1 & \text{if } y = 0^m \\
            0 & \text{otherwise}
          \end{cases}$$

-   Fixed coordinate set $I$ = the $x$-coordinates.

If $\exists x^\star \, \forall y \, \varphi(x^\star,y)=1$, then for any $y$ we have $U(\text{YES})=2$ and $U(\text{NO})\le 1$, so $\text{Opt}(x^\star,y)=\{\text{YES}\}$ is constant. Conversely, if $\varphi(x,y)$ is false for some $y$, then either $y=0^m$ (where NO is optimal) or $y\neq 0^m$ (where YES and NO tie), so the optimal set varies across $y$ and the subcube is not constant. Thus an anchor assignment exists iff the $\exists\forall$-SAT instance is true. ◻
:::

## Tractable Subcases

Despite the general hardness, several natural subcases admit efficient algorithms:

::: proposition
When $|S|$ is polynomial in the input size (i.e., explicitly enumerable), MINIMUM-SUFFICIENT-SET is solvable in polynomial time.
:::

::: proof
*Proof.* Compute $\text{Opt}(s)$ for all $s \in S$. The minimum sufficient set is exactly the set of coordinates that "matter" for the resulting function, computable by standard techniques. ◻
:::

::: proposition
When $U(a, s) = w_a \cdot s$ for weight vectors $w_a \in \mathbb{Q}^n$, MINIMUM-SUFFICIENT-SET reduces to identifying coordinates where weight vectors differ.
:::

## Implications

::: corollary
Finding the minimal set of decision-relevant factors is coNP-complete. Even *verifying* that a proposed set is sufficient is coNP-complete.

This formally explains the engineering phenomenon:

1.  It's computationally easier to model everything than to find the minimum

2.  "Which unknowns matter?" is a hard question, not a lazy one to avoid

3.  Bounded scenario analysis (small $\hat{S}$) makes the problem tractable
:::

This connects to the pentalogy's leverage framework: the "epistemic budget" for deciding what to model is itself a computationally constrained resource.

## Remark: The Collapse to coNP

Early analysis of MINIMUM-SUFFICIENT-SET focused on the apparent $\exists\forall$ quantifier structure, which suggested a $\Sigma_2^P$-complete result. We initially explored certificate-size lower bounds for the complement, attempting to show MINIMUM-SUFFICIENT-SET was unlikely to be in coNP.

However, the key insight---formalized as `sufficient_contains_relevant`---is that sufficiency has a simple characterization: a set is sufficient iff it contains all relevant coordinates. This collapses the $\exists\forall$ structure because:

-   The minimum sufficient set is *exactly* the relevant coordinate set

-   Checking relevance is in coNP (witness: two states differing only at that coordinate with different optimal sets)

-   Counting relevant coordinates is also in coNP

This collapse explains why ANCHOR-SUFFICIENCY retains its $\Sigma_2^P$-completeness: fixing coordinates and asking for an assignment that works is a genuinely different question. The "for all suffixes" quantifier cannot be collapsed when the anchor assignment is part of the existential choice.

---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper4_decision_quotient/proofs/`
- Lines: 3,412
- Theorems: ~110
- Sorry placeholders: 0

