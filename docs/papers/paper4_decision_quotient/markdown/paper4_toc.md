# Paper: Computational Complexity of Sufficiency in Decision Problems

**Status**: Theory of Computing-ready | **Lean**: 7071 lines, 310 theorems

---

## Abstract

We characterize the computational complexity of coordinate sufficiency in decision problems within the formal model. Given action set $A$, state space $S = X_1 \times \cdots \times X_n$, and utility $U: A \times S \to \mathbb{Q}$, a coordinate set $I$ is *sufficient* if $s_I = s'_I \implies \Opt(s) = \Opt(s')$.

**The landscape in the formal model:**

-   **General case:** SUFFICIENCY-CHECK is -complete; ANCHOR-SUFFICIENCY is $\SigmaP{2}$-complete.

-   **Tractable cases:** Polynomial-time for bounded action sets under the explicit-state encoding; separable utilities ($U = f + g$) under any encoding; and tree-structured utility with explicit local factors.

-   **Encoding-regime separation:** Polynomial-time under the explicit-state encoding (polynomial in $|S|$). Under ETH, there exist succinctly encoded worst-case instances witnessed by a strengthened gadget construction (mechanized in Lean; see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}) with $k^*=n$ for which SUFFICIENCY-CHECK requires $2^{\Omega(n)}$ time.

The tractable cases are stated with explicit encoding assumptions (Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}). Together, these results answer the question "when is decision-relevant information identifiable efficiently?" within the stated regimes. At the structural level, the apparent $\exists\forall$ form of MINIMUM-SUFFICIENT-SET collapses to a characterization via the criterion $\text{sufficient}(I) \iff \text{Relevant} \subseteq I$.

The contribution has two levels: (i) a complete complexity landscape for the core decision-relevant problems in the formal model (coNP/$\Sigma_2^P$ completeness and tractable regimes under explicit encoding assumptions), and (ii) a formal regime-typing framework that separates structural complexity from representational hardness and yields theorem-indexed engineering corollaries.

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 (7071 lines, 310 theorem/lemma statements); complexity classifications follow by composition with standard results (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}).

**Keywords:** computational complexity, decision theory, polynomial hierarchy, tractability dichotomy, Lean 4


# Introduction {#sec:introduction}

Consider a decision problem with actions $A$ and states $S = X_1 \times \cdots \times X_n$. A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only coordinates in $I$ determines the optimal action: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$

This paper characterizes the efficient cases of coordinate sufficiency within the formal model:

Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"} fixes the computational model and input encodings used for all complexity claims. Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"} gives the model contract and regime tags used to type every strong claim.

::: center
  **Problem**              **Complexity**          **When Tractable**
  ------------------------ ----------------------- ------------------------------------------------------------------------------
  SUFFICIENCY-CHECK        -complete               Bounded actions (explicit-state), separable utility, tree-structured utility
  MINIMUM-SUFFICIENT-SET   -complete               Same conditions
  ANCHOR-SUFFICIENCY       $\SigmaP{2}$-complete   Open
:::

The tractable cases are stated with explicit encoding assumptions (Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}). Outside those regimes, the succinct model yields hardness.

## Hardness--Recovery Reading Map

Theorems in this paper are intended to be read as hardness/recovery pairs for the same fixed decision relation:

1.  **Sufficiency checking:** \[S\] coNP-complete in the general succinct regime (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), paired with polynomial-time recovery under explicit-state and structured-access regimes (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

2.  **Minimal sufficient sets:** \[S\] coNP-complete in general (Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}), paired with the collapse criterion and relevance-computation recovery route (Theorems [\[thm:minsuff-collapse\]](#thm:minsuff-collapse){reference-type="ref" reference="thm:minsuff-collapse"}, [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

3.  **Anchor sufficiency:** $\SigmaP{2}$-complete in the general anchored formulation (Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"}); no general polynomial-time recovery condition is established in this model.

*(Lean anchors for this map: `ClaimClosure.sufficiency_conp_complete_conditional`, `ClaimClosure.minsuff_conp_complete_conditional`, `ClaimClosure.minsuff_collapse_core`, `ClaimClosure.anchor_sigma2p_complete_conditional`, `ClaimClosure.tractable_subcases_conditional`, `Sigma2PHardness.min_sufficient_set_iff_relevant_card`.)*

An operational criterion follows later from the same chain: once decision-site count exceeds the amortization threshold $n^*$, avoiding structural identification is more expensive than paying the one-time centralization cost (Theorem [\[thm:amortization\]](#thm:amortization){reference-type="ref" reference="thm:amortization"}). *(Lean: `HardnessDistribution.complete_model_dominates_after_threshold`, `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`.)*

## Landscape Summary

**When is sufficiency checking tractable?** We identify three sufficient conditions:

1.  **Bounded actions** ($|A| \leq k$) under explicit-state encoding: with constantly many actions, we enumerate action pairs over the explicit utility table.

2.  **Separable utility** ($U(a,s) = f(a) + g(s)$): The optimal action depends only on $f$, making all coordinates irrelevant to the decision.

3.  **Tree-structured utility**: With explicit local factors over a tree, dynamic programming yields polynomial algorithms in the input length.

Each condition is stated with its encoding assumption. Outside these regimes, the general problem remains -hard (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}).

**When is it intractable?** The general problem is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), with a separation between explicit-state tractability and succinct worst-case hardness:

-   In the explicit-state model: SUFFICIENCY-CHECK is solvable in polynomial time in $|S|$ by explicitly computing $\Opt(s)$ for all $s\in S$ and checking all pairs $(s,s')$ with equal $I$-projection. In particular, instances with $k^* = O(\log |S|)$ are tractable in this model.

-   In the succinct model: under ETH there exist worst-case instances produced by our strengthened gadget in which the minimal sufficient set has size $\Omega(n)$ (indeed $n$) and SUFFICIENCY-CHECK requires $2^{\Omega(n)}$ time.

The lower-bound statement does not address intermediate regimes.

## Main Theorems

1.  **Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}:** SUFFICIENCY-CHECK is -complete via reduction from TAUTOLOGY.

2.  **Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}:** MINIMUM-SUFFICIENT-SET is -complete (the $\SigmaP{2}$ structure collapses).

3.  **Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"}:** ANCHOR-SUFFICIENCY is $\SigmaP{2}$-complete via reduction from $\exists\forall$-SAT.

4.  **Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}:** Encoding-regime separation: explicit-state polynomial-time (polynomial in $|S|$), and under ETH a succinct worst-case lower bound witnessed by a hard family with $k^* = n$.

5.  **Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}:** Polynomial algorithms for bounded actions, separable utility, tree structure.

## Machine-Checked Proofs

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 [@moura2021lean4] (7071 lines, 310 theorem/lemma statements). The formalization verifies that the TAUTOLOGY reduction correctly maps tautologies to sufficient coordinate sets. Complexity class membership (coNP-completeness, $\Sigma_2^P$-completeness) follows by composition with standard complexity-theoretic results.

#### What is new.

We contribute (i) formal definitions of decision-theoretic sufficiency in Lean; (ii) machine-checked proofs of reduction correctness for the TAUTOLOGY and $\exists\forall$-SAT reductions; (iii) a complete complexity landscape for coordinate sufficiency with explicit encoding assumptions; and (iv) a formal separation between structural complexity and representational hardness used to derive theorem-indexed engineering corollaries. Prior work establishes hardness informally; we formalize the constructions and their regime-typed consequences.

## Paper Structure

The primary contribution is theoretical: a formalized reduction framework and a complete characterization of the core decision-relevant problems in the formal model (coNP/$\Sigma_2^P$ completeness and tractable cases stated under explicit encoding assumptions). A second contribution is formal claim typing: Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"} introduces the structural/representational and integrity/competence splits that type-check the applied corollaries.

Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"}: decision-problem foundations and encoding model. Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"}: structural vs representational hardness; integrity vs competence. Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}: hardness proofs. Section [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"}: regime separation. Section [\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"}: tractable cases. Section [\[sec:engineering-justification\]](#sec:engineering-justification){reference-type="ref" reference="sec:engineering-justification"}: engineering corollaries by regime. Section [\[sec:implications\]](#sec:implications){reference-type="ref" reference="sec:implications"}: software architecture corollaries. Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"}: complexity redistribution corollary. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"}: related work. Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}: Lean listings.


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

::: definition
[]{#def:exact-identifiability label="def:exact-identifiability"} For a decision problem $\mathcal{D}$ and candidate coordinate set $I$, we say $I$ is *exactly relevance-identifying* if $$\forall i \in \{1,\ldots,n\}:\quad i \in I \iff i \text{ is relevant for } \mathcal{D}.$$ Equivalently, $I$ is exactly relevance-identifying iff $I$ equals the full relevant-coordinate set.
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
[]{#def:decision-quotient label="def:decision-quotient"} The *decision quotient* for state $s$ under coordinate set $I$ is: $$\text{DQ}_I(s) = \frac{|\{a \in A : a \in \Opt(s') \text{ for some } s' \sim_I s\}|}{|A|}$$ This measures the fraction of actions that are optimal for at least one state consistent with $I$.
:::

::: proposition
[]{#prop:sufficiency-char label="prop:sufficiency-char"} Coordinate set $I$ is sufficient if and only if $\text{DQ}_I(s) = |\Opt(s)|/|A|$ for all $s \in S$. *(Lean finite-model form: `ClaimClosure.sufficiency_iff_dq_ratio`, `ClaimClosure.sufficiency_iff_projectedOptCover_eq_opt`)*
:::

::: proof
*Proof.* If $I$ is sufficient, then $s \sim_I s' \implies \Opt(s) = \Opt(s')$, so the set of actions optimal for some $s' \sim_I s$ is exactly $\Opt(s)$.

Conversely, if the condition holds, then for any $s \sim_I s'$, the optimal actions form the same set (since $\text{DQ}_I(s) = \text{DQ}_I(s')$ and both equal the relative size of the common optimal set). ◻
:::

## Computational Model and Input Encoding {#sec:encoding}

We fix the computational model used by the complexity claims.

#### Succinct encoding (primary for hardness).

This succinct circuit encoding is the standard representation for decision problems in complexity theory; hardness is stated with respect to the input length of the circuit description [@arora2009computational]. An instance is encoded as:

-   a finite action set $A$ given explicitly,

-   coordinate domains $X_1,\ldots,X_n$ given by their sizes in binary,

-   a Boolean or arithmetic circuit $C_U$ that on input $(a,s)$ outputs $U(a,s)$.

The input length is $L = |A| + \sum_i \log |X_i| + |C_U|$. Polynomial time and all complexity classes (, $\Sigma_2^P$, ETH) are measured in $L$. All hardness results in Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} use this encoding.

#### Explicit-state encoding (used for enumeration algorithms and experiments).

The utility is given as a full table over $A \times S$. The input length is $L_{\text{exp}} = \Theta(|A||S|)$ (up to the bitlength of utilities). Polynomial time is measured in $L_{\text{exp}}$. Results stated in terms of $|S|$ use this encoding.

Unless explicitly stated otherwise, "polynomial time" refers to the succinct encoding.

## Model Contract and Regime Tags {#sec:model-contract}

All theorem statements in this paper are typed by the following model contract:

-   **C1 (finite actions):** $A$ is finite.

-   **C2 (finite coordinate domains):** each $X_i$ is finite, so $S=\prod_i X_i$ is finite.

-   **C3 (evaluable utility):** $U(a,s)$ is computable from the declared input encoding.

-   **C4 (fixed decision semantics):** optimality is defined by $\Opt(s)=\arg\max_a U(a,s)$.

We use short regime tags for applied corollaries:

-   **\[E\]** explicit-state encoding,

-   **\[S\]** succinct encoding,

-   **\[S+ETH\]** succinct encoding with ETH,

-   **\[S_bool\]** mechanized Boolean-coordinate submodel.

This tagging is a claim-typing convention: each strong statement is attached to the regime where it is proven.

## Adjacent Objective Regimes and Bridge

::: definition
[]{#def:adjacent-sequential-regime label="def:adjacent-sequential-regime"} An adjacent sequential objective instance consists of:

-   finite action set $A$,

-   finite coordinate state space $S = X_1 \times \cdots \times X_n$,

-   horizon $T \in \mathbb{N}_{\ge 1}$ and history-dependent policy class,

-   reward process $r_t$ and objective functional $J(\pi)$ (e.g., cumulative reward or regret).
:::

::: proposition
[]{#prop:one-step-bridge label="prop:one-step-bridge"} Consider an instance of Definition [\[def:adjacent-sequential-regime\]](#def:adjacent-sequential-regime){reference-type="ref" reference="def:adjacent-sequential-regime"} satisfying:

1.  $T=1$,

2.  deterministic rewards $r_1(a,s)=U(a,s)$ for some evaluable $U$,

3.  objective $J(\pi)=U(\pi(s),s)$ (single-step maximization),

4.  no post-decision state update relevant to the objective.

Then the induced optimization problem is exactly the static decision problem of Definition [\[def:decision-problem\]](#def:decision-problem){reference-type="ref" reference="def:decision-problem"}, and coordinate sufficiency in the sequential formulation is equivalent to Definition [\[def:sufficient\]](#def:sufficient){reference-type="ref" reference="def:sufficient"}. *(Lean bridge core: `ClaimClosure.one_step_bridge`)*
:::

::: proof
*Proof.* Under (1)--(3), optimizing $J$ at state $s$ is identical to choosing an action in $\arg\max_{a\in A} U(a,s)=\Opt(s)$. Condition (4) removes any dependence on future transition effects. Therefore the optimal-policy relation in the adjacent formulation coincides pointwise with $\Opt$ from Definition [\[def:optimizer\]](#def:optimizer){reference-type="ref" reference="def:optimizer"}, and the invariance condition "same projection implies same optimal choice set" is exactly Definition [\[def:sufficient\]](#def:sufficient){reference-type="ref" reference="def:sufficient"}. ◻
:::

::: remark
Beyond Proposition [\[prop:one-step-bridge\]](#prop:one-step-bridge){reference-type="ref" reference="prop:one-step-bridge"} (multi-step horizon, stochastic transitions/rewards, or regret objectives), the governing complexity objects change. Those regimes are natural extensions, but they are distinct formal classes from the static sufficiency class analyzed in this paper.
:::

# Interpretive Foundations: Hardness and Solver Claims {#sec:interpretive-foundations}

The claims in later applied sections are theorem-indexed consequences of this section and Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}--[\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"}.

## Structural Complexity vs Representational Hardness

::: definition
[]{#def:structural-complexity label="def:structural-complexity"} For a fixed formal decision relation (e.g., "$I$ is sufficient for $\mathcal{D}$"), *structural complexity* means its placement in standard complexity classes within the formal model (coNP, $\Sigma_2^P$, etc.), as established by class-membership arguments and reductions.
:::

::: definition
[]{#def:representational-hardness label="def:representational-hardness"} For a fixed decision relation and an encoding regime $E$ (Section [1.4](#sec:encoding){reference-type="ref" reference="sec:encoding"}), *representational hardness* is the worst-case computational cost incurred by solvers whose input access is restricted to $E$.
:::

::: remark
This paper keeps the decision relation fixed and varies the encoding regime explicitly. Thus, later separations are read as changes in representational hardness under fixed structural complexity, not as changes to the underlying sufficiency semantics.
:::

## Solver Integrity and Regime Competence

To keep practical corollaries type-safe, we separate *integrity* (what a solver is allowed to assert) from *competence* (what it can cover under a declared regime), following the certifying-algorithms schema [@mcconnell2010certifying].

::: definition
[]{#def:certifying-solver label="def:certifying-solver"} Fix a decision relation $\mathcal{R} \subseteq \mathcal{X}\times\mathcal{Y}$ and an encoding regime $E$ over $\mathcal{X}$. A *certifying solver* is a pair $(Q,V)$ where:

-   $Q$ maps each input $x\in\mathcal{X}$ to either $\mathsf{ABSTAIN}$ or a candidate pair $(y,w)$,

-   $V$ is a polynomial-time checker (in $|{\rm enc}_E(x)|$) with output in $\{0,1\}$.
:::

::: definition
[]{#def:solver-integrity label="def:solver-integrity"} A certifying solver $(Q,V)$ has *integrity* for relation $\mathcal{R}$ if:

-   (assertion soundness) $Q(x)=(y,w)\implies V(x,y,w)=1$,

-   (checker soundness) $V(x,y,w)=1\implies (x,y)\in\mathcal{R}$.

The output $\mathsf{ABSTAIN}$ (equivalently, $\mathsf{UNKNOWN}$) is first-class and carries no assertion about membership in $\mathcal{R}$.
:::

::: definition
[]{#def:competence-regime label="def:competence-regime"} Fix a regime $\Gamma=(\mathcal{X}_\Gamma,E_\Gamma,\mathcal{C}_\Gamma)$ with instance family $\mathcal{X}_\Gamma\subseteq\mathcal{X}$, encoding assumptions $E_\Gamma$, and resource bound $\mathcal{C}_\Gamma$. A certifying solver $(Q,V)$ is *competent* on $\Gamma$ for relation $\mathcal{R}$ if:

-   it has integrity for $\mathcal{R}$ (Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"}),

-   (coverage) $\forall x\in\mathcal{X}_\Gamma,\;Q(x)\neq\mathsf{ABSTAIN}$,

-   (resource bound) runtime$_Q(x)\le \mathcal{C}_\Gamma(|{\rm enc}_{E_\Gamma}(x)|)$ for all $x\in\mathcal{X}_\Gamma$.
:::

::: proposition
[]{#prop:integrity-competence-separation label="prop:integrity-competence-separation"} Integrity and competence are distinct predicates: integrity constrains asserted outputs, while competence adds non-abstaining coverage under resource bounds.
:::

::: proof
*Proof.* Take the always-abstain solver $Q_\bot(x)=\mathsf{ABSTAIN}$ with any polynomial-time checker $V$. Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"} holds vacuously, so $(Q_\bot,V)$ is integrity-preserving, but it fails Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"} whenever $\mathcal{X}_\Gamma\neq\emptyset$ because coverage fails. Hence integrity does not imply competence. The converse is immediate because competence includes integrity as a conjunct. ◻
:::

This separation is load-bearing for the regime-conditional trilemma used later: if exact competence is blocked by hardness in a declared regime, integrity forces one of three responses---abstain, weaken guarantees, or change regime assumptions.

#### Mechanized status.

This separation is machine-checked in `DecisionQuotient/IntegrityCompetence.lean` via: `competence_implies_integrity` and `integrity_not_competent_of_nonempty_scope`.


# Computational Complexity of Decision-Relevant Uncertainty {#sec:hardness}

This section establishes the computational complexity of determining which state coordinates are decision-relevant. We prove three main results:

1.  **SUFFICIENCY-CHECK** is coNP-complete

2.  **MINIMUM-SUFFICIENT-SET** is coNP-complete (the $\Sigma_2^P$ structure collapses)

3.  **ANCHOR-SUFFICIENCY** (fixed coordinates) is $\Sigma_2^P$-complete

Under the model contract of Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"} and the succinct encoding of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}, these results place exact relevance identification beyond NP-completeness: in the worst case, finding (or certifying) minimal decision-relevant sets is computationally intractable.

#### Reading convention for this section.

Each hardness theorem below is paired with a recovery boundary for the same decision relation: when structural-access assumptions in Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} hold, polynomial-time exact procedures are recovered; when they fail in \[S\], the stated hardness applies. *(Lean map handles: `ClaimClosure.sufficiency_conp_complete_conditional`, `ClaimClosure.minsuff_conp_complete_conditional`, `ClaimClosure.anchor_sigma2p_complete_conditional`, `ClaimClosure.tractable_subcases_conditional`.)*

## Problem Definitions

::: definition
A *decision problem instance* is a tuple $(A, X_1, \ldots, X_n, U)$ where:

-   $A$ is a finite set of alternatives

-   $X_1, \ldots, X_n$ are the coordinate domains, with state space $S = X_1 \times \cdots \times X_n$

-   $U: A \times S \to \mathbb{Q}$ is the utility function (in the succinct encoding, $U$ is given as a Boolean circuit)
:::

::: definition
For state $s \in S$, define: $$\text{Opt}(s) := \arg\max_{a \in A} U(a, s)$$
:::

::: definition
A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if: $$\forall s, s' \in S: \quad s_I = s'_I \implies \text{Opt}(s) = \text{Opt}(s')$$ where $s_I$ denotes the projection of $s$ onto coordinates in $I$.
:::

::: problem
**Input:** Decision problem $(A, X_1, \ldots, X_n, U)$ and coordinate set $I \subseteq \{1,\ldots,n\}$\
**Question:** Is $I$ sufficient?
:::

::: problem
**Input:** Decision problem $(A, X_1, \ldots, X_n, U)$ and integer $k$\
**Question:** Does there exist a sufficient set $I$ with $|I| \leq k$?
:::

## Hardness of SUFFICIENCY-CHECK

::: theorem
[]{#thm:sufficiency-conp label="thm:sufficiency-conp"} SUFFICIENCY-CHECK is coNP-complete [@cook1971complexity; @karp1972reducibility]. *(Lean handles: `ClaimClosure.sufficiency_conp_reduction_core`, `ClaimClosure.sufficiency_conp_complete_conditional`, `tautology_iff_sufficient`.)*
:::

::: center
  Source                 Target               Key property preserved
  ---------------------- -------------------- --------------------------------------
  TAUTOLOGY              SUFFICIENCY-CHECK    Tautology iff $\emptyset$ sufficient
  $\exists\forall$-SAT   ANCHOR-SUFFICIENCY   Witness anchors iff formula true
:::

::: proof
*Proof.* **Membership in coNP:** The complementary problem INSUFFICIENCY is in NP. Given a decision problem $(A, X_1, \ldots, X_n, U)$ and coordinate set $I$, a witness for insufficiency is a pair $(s, s')$ such that:

1.  $s_I = s'_I$ (verifiable in polynomial time)

2.  $\text{Opt}(s) \neq \text{Opt}(s')$ (verifiable by evaluating $U$ on all alternatives)

**coNP-hardness:** We reduce from TAUTOLOGY.

Given Boolean formula $\varphi(x_1, \ldots, x_n)$, construct a decision problem with:

-   Alternatives: $A = \{\text{accept}, \text{reject}\}$

-   State space: $S = \{\text{reference}\} \cup \{0,1\}^n$ (equivalently, encode this as a product space with one extra coordinate $r \in \{0,1\}$ indicating whether the state is the reference state)

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

#### Immediate recovery boundary (SUFFICIENCY-CHECK).

Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} is the \[S\] general-case hardness statement. For the same sufficiency relation, Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} gives polynomial-time recovery under explicit-state, separable, and tree-structured regimes. *(Lean bridge handles: `ClaimClosure.sufficiency_conp_complete_conditional`, `ClaimClosure.tractable_subcases_conditional`, `ClaimClosure.tractable_bounded_core`, `ClaimClosure.tractable_separable_core`, `ClaimClosure.tractable_tree_core`.)*

#### Mechanized strengthening (all coordinates relevant).

The reduction above establishes coNP-hardness using a single witness set $I=\emptyset$. For the ETH-based lower bound in Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}, we additionally need worst-case instances where the minimal sufficient set has *linear* size.

We formalized a strengthened reduction in Lean 4: given a Boolean formula $\varphi$ over $n$ variables, construct a decision problem with $n$ coordinates such that if $\varphi$ is not a tautology then *every* coordinate is decision-relevant (so $k^* = n$). Intuitively, the construction places a copy of the base gadget at each coordinate and makes the global "accept" condition hold only when every coordinate's local test succeeds; a single falsifying assignment at one coordinate therefore changes the global optimal set, witnessing that coordinate's relevance. This strengthening is mechanized in Lean; see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}.

## Complexity of MINIMUM-SUFFICIENT-SET

::: theorem
[]{#thm:minsuff-conp label="thm:minsuff-conp"} MINIMUM-SUFFICIENT-SET is coNP-complete. *(Lean handles: `ClaimClosure.minsuff_collapse_core`, `ClaimClosure.minsuff_conp_complete_conditional`.)*
:::

::: proof
*Proof.* **Structural observation:** The $\exists\forall$ quantifier pattern suggests $\Sigma_2^P$: $$\exists I \, (|I| \leq k) \; \forall s, s' \in S: \quad s_I = s'_I \implies \text{Opt}(s) = \text{Opt}(s')$$ However, this collapses because sufficiency has a simple characterization.

**Key lemma:** A coordinate set $I$ is sufficient if and only if $I$ contains all relevant coordinates (proven formally as `sufficient_contains_relevant` in Lean): $$\text{sufficient}(I) \iff \text{Relevant} \subseteq I$$ where $\text{Relevant} = \{i : \exists s, s'.\; s \text{ differs from } s' \text{ only at } i \text{ and } \text{Opt}(s) \neq \text{Opt}(s')\}$.

**Consequence:** The minimum sufficient set is exactly the set of relevant coordinates. Thus MINIMUM-SUFFICIENT-SET asks: "Is the number of relevant coordinates at most $k$?"

**coNP membership:** A witness that the answer is NO is a set of $k+1$ coordinates, each proven relevant (by exhibiting $s, s'$ pairs). Verification is polynomial.

**coNP-hardness:** The $k=0$ case asks whether no coordinates are relevant, i.e., whether $\emptyset$ is sufficient. This is exactly SUFFICIENCY-CHECK, which is coNP-complete by Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}. ◻
:::

#### Immediate recovery boundary (MINIMUM-SUFFICIENT-SET).

Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} pairs with Theorem [\[thm:minsuff-collapse\]](#thm:minsuff-collapse){reference-type="ref" reference="thm:minsuff-collapse"}: exact minimization complexity is governed by relevance-cardinality once the collapse is applied. Recovery then depends on computing relevance efficiently, with structured-access assumptions from Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} giving the corresponding route for the underlying sufficiency computations. *(Lean bridge handles: `ClaimClosure.minsuff_conp_complete_conditional`, `ClaimClosure.minsuff_collapse_core`, `ClaimClosure.minsuff_collapse_to_conp_conditional`, `Sigma2PHardness.min_sufficient_set_iff_relevant_card`, `ClaimClosure.tractable_subcases_conditional`.)*

## Anchor Sufficiency (Fixed Coordinates)

We also formalize a strengthened variant that fixes the coordinate set and asks whether there exists an *assignment* to those coordinates that makes the optimal action constant on the induced subcube.

::: problem
**Input:** Decision problem $(A, X_1, \ldots, X_n, U)$ and fixed coordinate set $I \subseteq \{1,\ldots,n\}$\
**Question:** Does there exist an assignment $\alpha$ to $I$ such that $\text{Opt}(s)$ is constant for all states $s$ with $s_I = \alpha$?
:::

::: theorem
[]{#thm:anchor-sigma2p label="thm:anchor-sigma2p"} ANCHOR-SUFFICIENCY is $\Sigma_2^P$-complete [@stockmeyer1976polynomial] (already for Boolean coordinate spaces). *(Lean handles: `ClaimClosure.anchor_sigma2p_reduction_core`, `ClaimClosure.anchor_sigma2p_complete_conditional`, `anchor_sufficiency_sigma2p`.)*
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

If $\exists x^\star \, \forall y \, \varphi(x^\star,y)=1$, then for any $y$ we have $U(\text{YES})=2$ and $U(\text{NO})\le 1$, so $\text{Opt}(x^\star,y)=\{\text{YES}\}$ is constant. Conversely, fix $x$ and suppose $\exists y_f$ with $\varphi(x,y_f)=0$.

-   If $\varphi(x,0^m)=1$, then $\text{Opt}(x,0^m)=\{\text{YES}\}$. The falsifying assignment must satisfy $y_f\neq 0^m$, where $U(\text{YES})=U(\text{NO})=0$, so $\text{Opt}(x,y_f)=\{\text{YES},\text{NO}\}$.

-   If $\varphi(x,0^m)=0$, then $\text{Opt}(x,0^m)=\{\text{NO}\}$. After padding we have $m>0$, so choose any $y'\neq 0^m$: either $\varphi(x,y')=1$ (then $\text{Opt}(x,y')=\{\text{YES}\}$) or $\varphi(x,y')=0$ (then $\text{Opt}(x,y')=\{\text{YES},\text{NO}\}$). In both subcases the optimal set differs from $\{\text{NO}\}$.

Hence the subcube for this $x$ is not constant. Thus an anchor assignment exists iff the $\exists\forall$-SAT instance is true. ◻
:::

#### Immediate boundary statement (ANCHOR-SUFFICIENCY).

Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"} remains a second-level hardness statement in the anchored formulation; unlike MINIMUM-SUFFICIENT-SET, no general collapse to relevance counting is established here, so the corresponding tractability status remains open in this model. *(Lean anchor handles: `ClaimClosure.anchor_sigma2p_reduction_core`, `ClaimClosure.anchor_sigma2p_complete_conditional`, `anchor_sufficiency_sigma2p`.)*

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
Under the succinct encoding, exact minimization of sufficient coordinate sets is coNP-hard via the $k=0$ case, and fixed-anchor minimization is $\Sigma_2^P$-complete. *(Lean handles: `ClaimClosure.minsuff_conp_complete_conditional`, `ClaimClosure.anchor_sigma2p_complete_conditional`)*
:::

::: proof
*Proof.* The $k=0$ case of MINIMUM-SUFFICIENT-SET is SUFFICIENCY-CHECK (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), giving coNP-hardness for exact minimization. The fixed-anchor variant is exactly Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"}. ◻
:::

The modeling budget for deciding what to model is therefore a computationally constrained resource under this encoding.

## Quantifier Collapse for MINIMUM-SUFFICIENT-SET

::: theorem
[]{#thm:minsuff-collapse label="thm:minsuff-collapse"} The apparent second-level predicate $$\exists I \, (|I| \leq k) \; \forall s,s' \in S:\; s_I = s'_I \implies \Opt(s)=\Opt(s')$$ is equivalent to the coNP predicate $|\text{Relevant}| \le k$, where $$\text{Relevant} = \{i : \exists s,s'.\; s \text{ differs from } s' \text{ only at } i \text{ and } \Opt(s)\neq\Opt(s')\}.$$ Consequently, MINIMUM-SUFFICIENT-SET is governed by coNP certificates rather than a genuine $\Sigma_2^P$ alternation. *(Lean handles: `ClaimClosure.minsuff_collapse_core`, `ClaimClosure.minsuff_collapse_to_conp_conditional`, `Sigma2PHardness.min_sufficient_set_iff_relevant_card`.)*
:::

::: proof
*Proof.* By the formal lemma `sufficient_contains_relevant`, a coordinate set $I$ is sufficient iff $\text{Relevant}\subseteq I$. Therefore: $$\exists I \; (|I|\le k \wedge \text{sufficient}(I))
\iff
\exists I \; (|I|\le k \wedge \text{Relevant}\subseteq I)
\iff
|\text{Relevant}| \le k.$$ So the existential-over-universal presentation collapses to counting the relevant coordinates.

A NO certificate for $|\text{Relevant}| \le k$ is a list of $k+1$ distinct relevant coordinates, each witnessed by two states that differ only on that coordinate and yield different optimal sets; this is polynomially verifiable. Hence the resulting predicate is in coNP, matching Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}.

This also clarifies why ANCHOR-SUFFICIENCY remains $\Sigma_2^P$-complete: once an anchor assignment is existentially chosen, the universal quantifier over the residual subcube does not collapse to a coordinate-counting predicate. ◻
:::


# Encoding-Regime Separation {#sec:dichotomy}

The hardness results of Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} apply to worst-case instances under the succinct encoding. This section states an encoding-regime separation: an explicit-state upper bound versus a succinct-encoding worst-case lower bound.

#### Model note.

Part 1 is \[E\] (time polynomial in $|S|$). Part 2 is \[S+ETH\] (time exponential in $n$). The encodings are defined in Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. These two parts are stated in different encodings and are not directly comparable as functions of a single input length.

::: theorem
[]{#thm:dichotomy label="thm:dichotomy"} Let $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ be a decision problem with $|S| = N$ states. Let $k^*$ be the size of the minimal sufficient set.

1.  **\[E\] Explicit-state upper bound:** Under the explicit-state encoding, SUFFICIENCY-CHECK is solvable in time polynomial in $N$ (e.g. $O(N^2|A|)$).

2.  **\[S+ETH\] Succinct lower bound (worst case):** Assuming ETH, there exists a family of succinctly encoded instances with $n$ coordinates and minimal sufficient set size $k^* = n$ such that SUFFICIENCY-CHECK requires time $2^{\Omega(n)}$.

*(Lean handles: `ClaimClosure.dichotomy_conditional`, `ClaimClosure.explicit_state_upper_core`, `ClaimClosure.hard_family_all_coords_core`.)*
:::

::: proof
*Proof.* **Part 1 (Explicit-state upper bound):** Under the explicit-state encoding, SUFFICIENCY-CHECK is decidable in time polynomial in $N$ by direct enumeration: compute $\Opt(s)$ for all $s\in S$ and then check all pairs $(s,s')$ with $s_I=s'_I$.

Equivalently, for any fixed $I$, the projection map $s\mapsto s_I$ has image size $|S_I|\le |S|=N$, so any algorithm that iterates over projection classes (or over all state pairs) runs in polynomial time in $N$. Thus, in particular, when $k^*=O(\log N)$, SUFFICIENCY-CHECK is solvable in polynomial time under the explicit-state encoding.

#### Remark (bounded coordinate domains).

In the general model $S=\prod_i X_i$, for a fixed $I$ one always has $|S_I|\le \prod_{i\in I}|X_i|$ (and $|S_I|\le N$). If the coordinate domains are uniformly bounded, $|X_i|\le d$ for all $i$, then $|S_I|\le d^{|I|}$.

**Part 2 (Succinct ETH lower bound, worst case):** A strengthened version of the TAUTOLOGY reduction used in Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} produces a family of instances in which the minimal sufficient set has size $k^* = n$: given a Boolean formula $\varphi$ over $n$ variables, we construct a decision problem with $n$ coordinates such that if $\varphi$ is not a tautology then *every* coordinate is decision-relevant (thus $k^*=n$). This strengthening is mechanized in Lean (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}). Under the Exponential Time Hypothesis (ETH) [@impagliazzo2001complexity], TAUTOLOGY requires time $2^{\Omega(n)}$ in the succinct encoding, so SUFFICIENCY-CHECK inherits a $2^{\Omega(n)}$ worst-case lower bound via this reduction. ◻
:::

::: corollary
There is a clean separation between explicit-state tractability and succinct worst-case hardness (with respect to the encodings in Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}):

-   Under the explicit-state encoding, SUFFICIENCY-CHECK is polynomial in $N=|S|$.

-   Under ETH, there exist succinctly encoded instances with $k^* = \Omega(n)$ (indeed $k^*=n$) for which SUFFICIENCY-CHECK requires $2^{\Omega(n)}$ time.

For Boolean coordinate spaces ($N = 2^n$), the explicit-state bound is polynomial in $2^n$ (exponential in $n$), while under ETH the succinct lower bound yields $2^{\Omega(n)}$ time for the hard family in which $k^* = \Omega(n)$.
:::

::: remark
Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} keeps the structural problem fixed (same sufficiency relation) and separates representational hardness by encoding regime: explicit-state access exposes the boundary $s \mapsto \Opt(s)$, while succinct access can hide it enough to force ETH-level worst-case cost on a hard family.
:::

This encoding-regime separation identifies exactly where exact minimization is tractable (\[E\]) and where worst-case intractability appears (\[S+ETH\]) for the same underlying decision relation.


# Tractable Special Cases: When You Can Solve It {#sec:tractable}

We distinguish the encodings of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. The tractability results below state the model assumption explicitly. Structural insight: hardness dissolves exactly when the full decision boundary $s \mapsto \Opt(s)$ is recoverable in polynomial time from the input representation; the three cases below instantiate this single principle. Concretely, each tractable regime corresponds to a specific structural insight (explicit boundary exposure, additive separability, or tree factorization) that removes the hardness witness; this supports reading the general-case hardness as missing structural access in the current representation rather than as an intrinsic semantic barrier.

::: theorem
[]{#thm:tractable label="thm:tractable"} SUFFICIENCY-CHECK is polynomial-time solvable in the following cases:

1.  **Explicit-state encoding:** The input contains the full utility table over $A \times S$. SUFFICIENCY-CHECK runs in $O(|S|^2|A|)$ time; if $|A|$ is constant, $O(|S|^2)$.

2.  **Separable utility (any encoding):** $U(a, s) = f(a) + g(s)$.

3.  **Tree-structured utility with explicit local factors (succinct structured encoding):** There exists a rooted tree on coordinates and local functions $u_i$ such that $$U(a,s) = \sum_i u_i\bigl(a, s_i, s_{\mathrm{parent}(i)}\bigr),$$ with the root term depending only on $(a, s_{\mathrm{root}})$ and all $u_i$ given explicitly as part of the input.

*(Lean handles: `ClaimClosure.tractable_bounded_core`, `ClaimClosure.tractable_separable_core`, `ClaimClosure.tractable_tree_core`, `ClaimClosure.tractable_subcases_conditional`.)*
:::

## Explicit-State Encoding

::: proof
*Proof of Part 1.* Given the full table of $U(a,s)$, compute $\Opt(s)$ for all $s \in S$ in $O(|S||A|)$ time. For SUFFICIENCY-CHECK on a given $I$, verify that for all pairs $(s,s')$ with $s_I = s'_I$, we have $\Opt(s) = \Opt(s')$. This takes $O(|S|^2|A|)$ time by direct enumeration and is polynomial in the explicit input length. If $|A|$ is constant, the runtime is $O(|S|^2)$. ◻
:::

## Separable Utility

::: proof
*Proof of Part 2.* If $U(a, s) = f(a) + g(s)$, then: $$\Opt(s) = \arg\max_{a \in A} [f(a) + g(s)] = \arg\max_{a \in A} f(a)$$ The optimal action is independent of the state. Thus $I = \emptyset$ is always sufficient. ◻
:::

## Tree-Structured Utility

::: proof
*Proof of Part 3.* Assume the tree decomposition and explicit local tables as stated. For each node $i$ and each value of its parent coordinate, compute the set of actions that are optimal for some assignment of the subtree rooted at $i$. This is a bottom-up dynamic program that combines local tables with child summaries; each table lookup is explicit in the input. A coordinate is relevant if and only if varying its value changes the resulting optimal action set. The total runtime is polynomial in $n$, $|A|$, and the size of the local tables. ◻
:::

## Practical Implications

::: center
  **Condition**             **Examples**
  ------------------------- ----------------------------------------
  Explicit-state encoding   Small or fully enumerated state spaces
  Separable utility         Additive costs, linear models
  Tree-structured utility   Hierarchies, causal trees
:::


# Engineering Corollaries by Regime {#sec:engineering-justification}

This section derives regime-typed engineering corollaries from the core complexity theorems. Theorem [\[thm:config-reduction\]](#thm:config-reduction){reference-type="ref" reference="thm:config-reduction"} maps configuration simplification to SUFFICIENCY-CHECK; Theorems [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}, and [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} then yield exact minimization consequences under \[S\] and \[S+ETH\].

Regime tags used below follow Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"}: \[S\], \[S+ETH\], \[E\], \[S_bool\]. Any prescription that requires exact minimization is constrained by these theorem-level bounds. Theorem [\[thm:overmodel-diagnostic\]](#thm:overmodel-diagnostic){reference-type="ref" reference="thm:overmodel-diagnostic"} implies that persistent failure to isolate a minimal sufficient set is a boundary-characterization signal in the current model, not a universal irreducibility claim.

::: remark
All claims in this section are formal corollaries under the declared model assumptions.

-   Competence claims are indexed by the regime tuple of Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}; prescriptions are meaningful only relative to feasible resources under that regime (bounded-rationality feasibility discipline) [@sep_bounded_rationality].

-   Integrity (Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"}) forbids overclaiming beyond certifiable outputs; $\mathsf{ABSTAIN}$/$\mathsf{UNKNOWN}$ is first-class when certification is unavailable.

-   Therefore, hardness results imply a regime-conditional trilemma: abstain, weaken guarantees (heuristics/approximation), or change encoding/structural assumptions to recover competence.
:::

## Configuration Simplification is SUFFICIENCY-CHECK

Real engineering problems reduce directly to the decision problems studied in this paper.

::: theorem
[]{#thm:config-reduction label="thm:config-reduction"} Given a software system with configuration parameters $P = \{p_1, \ldots, p_n\}$ and observed behaviors $B = \{b_1, \ldots, b_m\}$, the problem of determining whether parameter subset $I \subseteq P$ preserves all behaviors is equivalent to SUFFICIENCY-CHECK. *(Lean: `ConfigReduction.config_sufficiency_iff_behavior_preserving`)*
:::

::: proof
*Proof.* Construct decision problem $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ where:

-   Actions $A = B \cup \{\bot\}$, where $\bot$ is a sentinel "no-observed-behavior" action

-   Coordinates $X_i$ = domain of parameter $p_i$

-   State space $S = X_1 \times \cdots \times X_n$

-   For $b\in B$, utility $U(b, s) = 1$ if behavior $b$ occurs under configuration $s$, else $0$

-   Sentinel utility $U(\bot,s)=1$ iff no behavior in $B$ occurs under configuration $s$, else $0$

Then $$\Opt(s)=
\begin{cases}
\{b \in B : b \text{ occurs under configuration } s\}, & \text{if this set is nonempty},\\
\{\bot\}, & \text{otherwise}.
\end{cases}$$ So the optimizer map exactly encodes observed-behavior equivalence classes, including the empty-behavior case.

Coordinate set $I$ is sufficient iff: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$

This holds iff configurations agreeing on parameters in $I$ exhibit identical behaviors.

Therefore, "does parameter subset $I$ preserve all behaviors?" is exactly SUFFICIENCY-CHECK for the constructed decision problem. ◻
:::

::: remark
The reduction above requires only:

1.  a finite behavior set,

2.  parameters with finite domains, and

3.  an evaluable behavior map from configurations to achieved behaviors.

These are exactly the model-contract premises C1--C3 instantiated for configuration systems.
:::

::: theorem
[]{#thm:overmodel-diagnostic label="thm:overmodel-diagnostic"} By contraposition of Theorem [\[thm:config-reduction\]](#thm:config-reduction){reference-type="ref" reference="thm:config-reduction"}, if no coordinate set can be certified as exactly relevance-identifying (Definition [\[def:exact-identifiability\]](#def:exact-identifiability){reference-type="ref" reference="def:exact-identifiability"}) for the modeled system, then the decision boundary is not completely characterized by the current parameterization. *(Lean model-level contrapositive: `ClaimClosure.no_exact_identifier_implies_not_boundary_characterized`, `ClaimClosure.boundaryCharacterized_iff_exists_sufficient_subset`)*
:::

::: proof
*Proof.* Assume the decision boundary were completely characterized by the current parameterization. Then, via Theorem [\[thm:config-reduction\]](#thm:config-reduction){reference-type="ref" reference="thm:config-reduction"}, the corresponding sufficiency instance admits exact relevance membership, hence a coordinate set that satisfies Definition [\[def:exact-identifiability\]](#def:exact-identifiability){reference-type="ref" reference="def:exact-identifiability"}. Contraposition gives the claim: persistent failure of exact relevance identification signals incomplete characterization of decision relevance in the model. ◻
:::

## Cost Asymmetry Under ETH

We now prove a cost asymmetry result under the stated cost model and complexity constraints.[^1]

::: theorem
[]{#thm:cost-asymmetry-eth label="thm:cost-asymmetry-eth"} Consider an engineer specifying a system configuration with $n$ parameters. Let:

-   $C_{\text{over}}(k)$ = cost of maintaining $k$ extra parameters beyond minimal

-   $C_{\text{find}}(n)$ = cost of finding minimal sufficient parameter set

-   $C_{\text{under}}$ = expected cost of production failures from underspecification

Assume ETH in the succinct encoding model of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. Then:

1.  Exact identification of minimal sufficient sets has worst-case finding cost $C_{\text{find}}(n)=2^{\Omega(n)}$. (Under ETH, SUFFICIENCY-CHECK has a $2^{\Omega(n)}$ lower bound in the succinct model, and exact minimization subsumes this decision task.)

2.  Maintenance cost is linear: $C_{\text{over}}(k) = O(k)$.

3.  Under ETH, exponential finding cost dominates linear maintenance cost for sufficiently large $n$.

Therefore, there exists $n_0$ such that for all $n > n_0$, the finding-vs-maintenance asymmetry satisfies: $$C_{\text{over}}(k) < C_{\text{find}}(n) + C_{\text{under}}$$

Within \[S+ETH\], persistent over-specification is consistent with unresolved boundary characterization rather than a proof that all included parameters are intrinsically necessary. *(Lean handles: `ClaimClosure.cost_asymmetry_eth_conditional`, `HardnessDistribution.linear_lt_exponential_plus_constant_eventually`.)*
:::

::: proof
*Proof.* Under ETH, the TAUTOLOGY reduction used in Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} yields a $2^{\Omega(n)}$ worst-case lower bound for SUFFICIENCY-CHECK in the succinct encoding. Any exact algorithm that outputs a minimum sufficient set can decide whether the optimum size is $0$ by checking whether the returned set is empty; this is exactly the SUFFICIENCY-CHECK query for $I=\emptyset$. Hence exact minimal-set finding inherits the same exponential worst-case lower bound.

Maintaining $k$ extra parameters incurs:

-   Documentation cost: $O(k)$ entries

-   Testing cost: $O(k)$ test cases

-   Migration cost: $O(k)$ parameters to update

Total maintenance cost is $C_{\text{over}}(k) = O(k)$.

The eventual dominance step is mechanized in `HardnessDistribution.linear_lt_exponential_plus_constant_eventually`: for fixed linear-overhead parameter $k$ and additive constant $C_{\text{under}}$ there is $n_0$ such that $k < 2^n + C_{\text{under}}$ for all $n \ge n_0$. Therefore: $$C_{\text{over}}(k) \ll C_{\text{find}}(n)$$

For any fixed nonnegative $C_{\text{under}}$, the asymptotic dominance inequality remains and only shifts the finite threshold $n_0$. ◻
:::

::: corollary
[]{#cor:no-auto-minimize label="cor:no-auto-minimize"} Assuming $\Pclass \neq \coNP$, there exists no polynomial-time algorithm that:

1.  Takes an arbitrary configuration file with $n$ parameters

2.  Identifies the minimal sufficient parameter subset

3.  Guarantees correctness (no false negatives)

*(Lean conditional closure: `ClaimClosure.no_auto_minimize_of_p_neq_conp`)*
:::

::: proof
*Proof.* Such an algorithm would solve MINIMUM-SUFFICIENT-SET in polynomial time, contradicting Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} (assuming $\Pclass \neq \coNP$). ◻
:::

::: remark
Corollary [\[cor:no-auto-minimize\]](#cor:no-auto-minimize){reference-type="ref" reference="cor:no-auto-minimize"} is a formal boundary statement: an always-correct polynomial-time minimizer for arbitrary succinct inputs would collapse $\Pclass$ and $\coNP$.
:::

::: remark
The practical force of worst-case hardness depends on instance structure, especially $k^*$. If SUFFICIENCY-CHECK is FPT in parameter $k^*$, then small-$k^*$ families can remain tractable even under succinct encodings. The strengthened mechanized gadget (`all_coords_relevant_of_not_tautology`) still proves existence of hard families with $k^*=n$; what is typical in deployed systems is an empirical question outside this formal model.
:::

## Regime-Conditional Operational Corollaries

Theorems [\[thm:overmodel-diagnostic\]](#thm:overmodel-diagnostic){reference-type="ref" reference="thm:overmodel-diagnostic"} and [\[thm:cost-asymmetry-eth\]](#thm:cost-asymmetry-eth){reference-type="ref" reference="thm:cost-asymmetry-eth"} yield the following conditional operational consequences:

**1. Conservative retention under unresolved relevance.** If irrelevance cannot be certified efficiently under the active regime, retaining a superset of parameters is a sound conservative policy.

**2. Heuristic selection as weakened-guarantee mode.** Under \[S+ETH\], exact global minimization can be exponentially costly in the worst case (Theorem [\[thm:cost-asymmetry-eth\]](#thm:cost-asymmetry-eth){reference-type="ref" reference="thm:cost-asymmetry-eth"}); methods such as AIC/BIC/cross-validation therefore fit the "weaken guarantees" branch of Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}.

**3. Full-parameter inclusion as an $O(n)$ upper-bound strategy.** Under \[S+ETH\], if exact minimization is unresolved, including all $n$ parameters incurs linear maintenance overhead while avoiding false irrelevance claims.

These corollaries are direct consequences of the hardness/tractability landscape: to move beyond them, one must either shift to tractable regimes from Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} or adopt explicit approximation commitments.

[^1]: Naive subset enumeration still gives an intuitive baseline of $O(2^n)$ checks, but that is an algorithmic upper bound; the theorem below uses ETH for the lower-bound argument.


# Applied Corollaries for Software Architecture {#sec:implications}

Regime for this section: the mechanized Boolean-coordinate model \[S_bool\] plus the architecture cost model defined below.

## Over-Specification as Diagnostic Signal

::: corollary
[]{#cor:overmodel-diagnostic-implication label="cor:overmodel-diagnostic-implication"} In the mechanized Boolean-coordinate model, if a coordinate is relevant and omitted from a candidate set $I$, then $I$ is not sufficient. *(Lean: `Sigma2PHardness.sufficient_iff_relevant_subset`)*
:::

::: proof
*Proof.* This is the contrapositive of `Sigma2PHardness.sufficient_iff_relevant_subset`. ◻
:::

::: corollary
[]{#cor:exact-identifiability label="cor:exact-identifiability"} In the mechanized Boolean-coordinate model, for any candidate set $I$: $$I \text{ is exactly relevance-identifying}
\iff
\bigl(I \text{ is sufficient and } I \subseteq R_{\mathrm{rel}}\bigr),$$ where $R_{\mathrm{rel}}$ is the full relevant-coordinate set. *(Lean: `Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`)*
:::

::: proof
*Proof.* This is exactly `Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`, with $R_{\mathrm{rel}}=\texttt{relevantFinset}$. ◻
:::

## Architectural Decision Quotient

::: definition
For a software system with configuration space $S$ and behavior space $B$: $$\text{ADQ}(I) = \frac{|\{b \in B : b \text{ achievable with some } s \text{ where } s_I \text{ fixed}\}|}{|B|}$$
:::

::: proposition
[]{#prop:adq-ordering label="prop:adq-ordering"} For coordinate sets $I,J$ in the same system, if $\mathrm{ADQ}(I) < \mathrm{ADQ}(J)$, then fixing $I$ leaves a strictly smaller achievable-behavior set than fixing $J$. *(Lean finite-cardinality form: `ClaimClosure.adq_ordering`)*
:::

::: proof
*Proof.* The denominator $|B|$ is shared. Thus $\mathrm{ADQ}(I) < \mathrm{ADQ}(J)$ is equivalent to a strict inequality between the corresponding achievable-behavior set cardinalities. ◻
:::

## Corollaries for Practice

::: corollary
[]{#cor:practice-diagnostic label="cor:practice-diagnostic"} In the mechanized Boolean-coordinate model, existence of a sufficient set of size at most $k$ is equivalent to the relevance set having cardinality at most $k$. *(Lean: `Sigma2PHardness.min_sufficient_set_iff_relevant_card`)*
:::

::: proof
*Proof.* By `Sigma2PHardness.min_sufficient_set_iff_relevant_card`, sufficiency of size $\le k$ is equivalent to a relevance-cardinality bound $\le k$ in the Boolean-coordinate model. ◻
:::

::: corollary
[]{#cor:practice-bounded label="cor:practice-bounded"} When the bounded-action or explicit-state conditions of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} hold, minimal modeling can be solved in polynomial time in the stated input size. *(Lean: `sufficiency_poly_bounded_actions`)*
:::

::: proof
*Proof.* This is the bounded-regime branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as `sufficiency_poly_bounded_actions`. ◻
:::

::: corollary
[]{#cor:practice-structured label="cor:practice-structured"} When utility is separable with explicit factors, sufficiency checking is polynomial in the explicit-state regime. *(Lean: `sufficiency_poly_separable`)*
:::

::: proof
*Proof.* This is the separable-utility branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as `sufficiency_poly_separable`. ◻
:::

::: corollary
[]{#cor:practice-tree label="cor:practice-tree"} When utility factors form a tree structure with explicit local factors, sufficiency checking is polynomial in the explicit-state regime. *(Lean: `sufficiency_poly_tree_structured`)*
:::

::: proof
*Proof.* This is the tree-factor branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as `sufficiency_poly_tree_structured`. ◻
:::

::: corollary
[]{#cor:practice-unstructured label="cor:practice-unstructured"} There is a machine-checked family of reduction instances where, for non-tautological source formulas, every coordinate is relevant ($k^*=n$), exhibiting worst-case boundary complexity. *(Lean: `all_coords_relevant_of_not_tautology`)*
:::

::: proof
*Proof.* The strengthened reduction proves that non-tautological source formulas induce instances where every coordinate is relevant; this is mechanized as `all_coords_relevant_of_not_tautology`. ◻
:::

## Hardness Distribution: Right Place vs Wrong Place {#sec:hardness-distribution}

::: definition
[]{#def:hardness-distribution label="def:hardness-distribution"} Let $P$ be a problem family under the succinct encoding of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. In this section, baseline hardness $H(P;n)$ denotes worst-case computational step complexity on instances with $n$ coordinates (equivalently, as a function of succinct input length $L$) in the fixed encoding regime. A *solution architecture* $S$ partitions this baseline hardness into:

-   $H_{\text{central}}(S)$: hardness paid once, at design time or in a shared component

-   $H_{\text{distributed}}(S)$: hardness paid per use site

For $n$ use sites, total realized hardness is: $$H_{\text{total}}(S) = H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)$$
:::

::: proposition
[]{#prop:hardness-conservation label="prop:hardness-conservation"} For any problem family $P$ measured by $H(P;n)$ above, any solution architecture $S$ and any number of use sites $n \ge 1$, if $H_{\text{total}}(S)$ is measured in the same worst-case step units over the same input family, then: $$H_{\text{total}}(S) = H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S) \geq H(P;n).$$ For SUFFICIENCY-CHECK, Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} provides the baseline on the hard succinct family: $H(\text{SUFFICIENCY-CHECK};n)=2^{\Omega(n)}$ under ETH. *(Lean structural core: `HardnessDistribution.totalDOF_ge_intrinsic`)*
:::

::: proof
*Proof.* By definition, $H(P;n)$ is a worst-case lower bound for correct solutions in this encoding regime and cost metric. Any such solution architecture decomposes total realized work as $H_{\text{central}} + n\cdot H_{\text{distributed}}$, so that total cannot fall below the baseline. ◻
:::

::: definition
[]{#def:hardness-efficiency label="def:hardness-efficiency"} The *hardness efficiency* of solution $S$ with $n$ use sites is: $$\eta(S, n) = \frac{H_{\text{central}}(S)}{H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)}$$ *(Lean ratio identity when denominator is positive: `HardnessDistribution.hardnessEfficiency_eq_central_share`)*
:::

::: proposition
[]{#prop:hardness-efficiency-interpretation label="prop:hardness-efficiency-interpretation"} For fixed $n$ and positive total hardness, larger $\eta(S,n)$ is equivalent to a larger central share of realized hardness. *(Lean definitional step: `HardnessDistribution.hardnessEfficiency_eq_central_share`)*
:::

::: proof
*Proof.* From Definition [\[def:hardness-efficiency\]](#def:hardness-efficiency){reference-type="ref" reference="def:hardness-efficiency"}, $\eta(S,n)$ is exactly the fraction of total realized hardness paid centrally. ◻
:::

::: definition
[]{#def:right-wrong-placement label="def:right-wrong-placement"} For a solution architecture $S$ in this linear model: $$\text{right hardness} \iff H_{\mathrm{distributed}}(S)=0,\qquad
\text{wrong hardness} \iff H_{\mathrm{distributed}}(S)>0.$$ *(Lean: `HardnessDistribution.isRightHardness`, `HardnessDistribution.isWrongHardness`)*
:::

::: theorem
[]{#thm:centralization-dominance label="thm:centralization-dominance"} Let $S_{\mathrm{right}}, S_{\mathrm{wrong}}$ be architectures over the same problem family with $$H_{\mathrm{distributed}}(S_{\mathrm{right}})=0,\quad
H_{\mathrm{central}}(S_{\mathrm{right}})>0,\quad
H_{\mathrm{distributed}}(S_{\mathrm{wrong}})>0,$$ and let $n > \max\!\bigl(1, H_{\mathrm{central}}(S_{\mathrm{right}})\bigr)$. Then:

1.  Lower total realized hardness: $$H_{\text{total}}(S_{\mathrm{right}}) < H_{\text{total}}(S_{\mathrm{wrong}})$$

2.  Fewer error sites: errors in centralized components affect 1 location; errors in distributed components affect $n$ locations

3.  Quantified leverage: moving one unit of work from distributed to central saves exactly $n-1$ units of total realized hardness

*(Lean: `HardnessDistribution.centralization_dominance_bundle`, `HardnessDistribution.centralization_step_saves_n_minus_one`)*
:::

::: proof
*Proof.* (1) and (2) are exactly the bundled theorem `HardnessDistribution.centralization_dominance_bundle`. (3) is exactly `HardnessDistribution.centralization_step_saves_n_minus_one`. ◻
:::

::: corollary
[]{#cor:right-wrong-hardness label="cor:right-wrong-hardness"} In the linear model, a right-hardness architecture strictly dominates a wrong-hardness architecture once use-site count exceeds central one-time hardness. Formally, for architectures $S_{\mathrm{right}}, S_{\mathrm{wrong}}$ over the same problem family, if $S_{\mathrm{right}}$ has right hardness, $S_{\mathrm{wrong}}$ has wrong hardness, and $n > H_{\mathrm{central}}(S_{\mathrm{right}})$, then $$H_{\mathrm{central}}(S_{\mathrm{right}}) + n\,H_{\mathrm{distributed}}(S_{\mathrm{right}})
<
H_{\mathrm{central}}(S_{\mathrm{wrong}}) + n\,H_{\mathrm{distributed}}(S_{\mathrm{wrong}}).$$ *(Lean: `HardnessDistribution.right_dominates_wrong`)*
:::

::: proof
*Proof.* This is the mechanized theorem `HardnessDistribution.right_dominates_wrong`. ◻
:::

::: proposition
[]{#prop:dominance-modes label="prop:dominance-modes"} This section uses two linear-model dominance modes plus generalized nonlinear dominance and boundary modes:

1.  **Strict threshold dominance:** Corollary [\[cor:right-wrong-hardness\]](#cor:right-wrong-hardness){reference-type="ref" reference="cor:right-wrong-hardness"} gives strict inequality once $n > H_{\mathrm{central}}(S_{\mathrm{right}})$.

2.  **Global weak dominance:** under the decomposition identity used in `HardnessDistribution.centralized_higher_leverage`, centralized hardness placement is never worse for all $n\ge 1$.

3.  **Generalized nonlinear dominance:** under bounded-vs-growing site-cost assumptions (Theorem [\[thm:generalized-dominance\]](#thm:generalized-dominance){reference-type="ref" reference="thm:generalized-dominance"}), right placement strictly dominates beyond a finite threshold without assuming linear per-site cost.

4.  **Generalized boundary mode:** without those growth-separation assumptions, strict dominance is not guaranteed (Proposition [\[prop:generalized-assumption-boundary\]](#prop:generalized-assumption-boundary){reference-type="ref" reference="prop:generalized-assumption-boundary"}).
:::

::: proof
*Proof.* Part (1) is Corollary [\[cor:right-wrong-hardness\]](#cor:right-wrong-hardness){reference-type="ref" reference="cor:right-wrong-hardness"}. Part (2) is exactly `HardnessDistribution.centralized_higher_leverage`. Part (3) is Theorem [\[thm:generalized-dominance\]](#thm:generalized-dominance){reference-type="ref" reference="thm:generalized-dominance"}. Part (4) is Proposition [\[prop:generalized-assumption-boundary\]](#prop:generalized-assumption-boundary){reference-type="ref" reference="prop:generalized-assumption-boundary"}. ◻
:::

**Illustrative Instantiation (Type Systems).** Consider a capability $C$ (e.g., provenance tracking) with one-time central cost $H_{\text{central}}$ and per-site manual cost $H_{\text{distributed}}$:

::: center
  **Approach**                  $H_{\text{central}}$     $H_{\text{distributed}}$
  ---------------------------- ----------------------- -----------------------------
  Native type system support    High (learning cost)    Low (type checker enforces)
  Manual implementation         Low (no new concepts)   High (reimplement per site)
:::

The table is schematic; the formal statement is Corollary [\[cor:type-system-threshold\]](#cor:type-system-threshold){reference-type="ref" reference="cor:type-system-threshold"}.

::: corollary
[]{#cor:type-system-threshold label="cor:type-system-threshold"} For the formal native-vs-manual architecture instance, native support has lower total realized cost for all $$n > H_{\mathrm{baseline}}(P),$$ where $H_{\mathrm{baseline}}(P)$ corresponds to the Lean identifier `intrinsicDOF`(P) in module `HardnessDistribution`. *(Lean: `HardnessDistribution.native_dominates_manual`)*
:::

::: proof
*Proof.* Immediate from `HardnessDistribution.native_dominates_manual`. ◻
:::

## Extension: Non-Additive Site-Cost Models {#sec:nonadditive-site-costs}

::: definition
[]{#def:generalized-site-accumulation label="def:generalized-site-accumulation"} Let $C_S : \mathbb{N} \to \mathbb{N}$ be a per-site accumulation function for architecture $S$. Define generalized total realized hardness by $$H_{\text{total}}^{\mathrm{gen}}(S,n) = H_{\text{central}}(S) + C_S(n).$$
:::

::: definition
[]{#def:eventual-saturation label="def:eventual-saturation"} A cost function $f : \mathbb{N}\to\mathbb{N}$ is *eventually saturating* if there exists $N$ such that for all $n\ge N$, $f(n)=f(N)$.
:::

::: theorem
[]{#thm:generalized-dominance label="thm:generalized-dominance"} Let $$H_{\text{total}}^{\mathrm{gen}}(S,n)=H_{\text{central}}(S)+C_S(n).$$ For two architectures $S_{\mathrm{right}},S_{\mathrm{wrong}}$, suppose there exists $B\in\mathbb{N}$ such that:

1.  $C_{S_{\mathrm{right}}}(m)\le B$ for all $m$ (bounded right-side per-site accumulation),

2.  $m \le C_{S_{\mathrm{wrong}}}(m)$ for all $m$ (identity-lower-bounded wrong-side growth).

Then for every $$n > H_{\text{central}}(S_{\mathrm{right}})+B,$$ one has $$H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{right}},n)
<
H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{wrong}},n).$$ *(Lean: `HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`)*
:::

::: proof
*Proof.* This is exactly the mechanized theorem `HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`. ◻
:::

::: corollary
[]{#cor:generalized-eventual-dominance label="cor:generalized-eventual-dominance"} If condition (1) above holds and there exists $N$ such that condition (2) holds for all $m\ge N$, then there exists $N_0$ such that for all $n\ge N_0$, $$H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{right}},n)
<
H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{wrong}},n).$$ *(Lean: `HardnessDistribution.generalized_right_eventually_dominates_wrong`)*
:::

::: proof
*Proof.* Immediate from `HardnessDistribution.generalized_right_eventually_dominates_wrong`. ◻
:::

::: proposition
[]{#prop:generalized-assumption-boundary label="prop:generalized-assumption-boundary"} In the generalized model, strict right-vs-wrong dominance is not unconditional. There are explicit counterexamples:

1.  If wrong-side growth lower bounds are dropped, right-side strict dominance can fail for all $n$.

2.  If right-side boundedness is dropped, strict dominance can fail for all $n$ even when wrong-side growth is linear.

*(Lean: `HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`, `HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`)*
:::

::: proof
*Proof.* This is exactly the pair of mechanized boundary theorems listed above. ◻
:::

::: theorem
[]{#thm:linear-saturation-iff-zero label="thm:linear-saturation-iff-zero"} In the linear model of this section, $$H_{\text{total}}(S,n)=H_{\text{central}}(S)+n\cdot H_{\text{distributed}}(S),$$ the function $n\mapsto H_{\text{total}}(S,n)$ is eventually saturating if and only if $H_{\text{distributed}}(S)=0$. *(Lean: `HardnessDistribution.totalDOF_eventually_constant_iff_zero_distributed`)*
:::

::: proof
*Proof.* This is exactly the mechanized equivalence theorem above. ◻
:::

::: theorem
[]{#thm:generalized-saturation-possible label="thm:generalized-saturation-possible"} There exists a generalized site-cost model with eventual saturation. In particular, for $$C_K(n)=\begin{cases}
n, & n\le K\\
K, & n>K,
\end{cases}$$ both $C_K$ and $n\mapsto H_{\text{central}}+C_K(n)$ are eventually saturating. *(Lean: `HardnessDistribution.saturatingSiteCost_eventually_constant`, `HardnessDistribution.generalizedTotal_with_saturation_eventually_constant`)*
:::

::: proof
*Proof.* This is the explicit construction mechanized in Lean. ◻
:::

::: corollary
[]{#cor:linear-positive-no-saturation label="cor:linear-positive-no-saturation"} No positive-slope linear per-site model can represent the saturating family above for all $n$. *(Lean: `HardnessDistribution.no_positive_slope_linear_represents_saturating`)*
:::

::: proof
*Proof.* This follows from the mechanized theorem that any linear representation of the saturating family must have zero slope. ◻
:::

#### Mechanized strengthening reference.

The strengthened all-coordinates-relevant reduction is presented in Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} ("Mechanized strengthening") and formalized in `Reduction_AllCoords.lean` via `all_coords_relevant_of_not_tautology`.

The next section develops the major practical consequence of this framework: the Simplicity Tax Theorem.


# Corollary: Complexity Redistribution Under Incomplete Models {#sec:simplicity-tax}

The load-bearing fact in this section is not the set identity itself; it is the difficulty of shrinking the required set $R(P)$ in the first place. By Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} (and Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} for minimization), exact relevance identification is intractable in the worst case under succinct encoding. The identities below therefore quantify how unresolved relevance is redistributed between central and per-site work.

::: definition
Let $R(P)$ be the required dimensions (those affecting $\Opt$) and $A(M)$ the dimensions model $M$ handles natively. The *expressive gap* is $\text{Gap}(M,P) = R(P) \setminus A(M)$.
:::

::: definition
[]{#def:simplicity-tax label="def:simplicity-tax"} The *simplicity tax* is the size of the expressive gap: $$\text{SimplicityTax}(M,P) := |\text{Gap}(M,P)|.$$
:::

::: theorem
[]{#thm:tax-conservation label="thm:tax-conservation"} $|\text{Gap}(M, P)| + |R(P) \cap A(M)| = |R(P)|$. The total cannot be reduced---only redistributed between "handled natively" and "handled externally." *(Lean: `HardnessDistribution.gap_conservation_card`)*
:::

::: proof
*Proof.* In the finite-coordinate model this is the exact set-cardinality identity $$|R\setminus A| + |R\cap A| = |R|,$$ formalized as `HardnessDistribution.gap_conservation_card`. ◻
:::

::: remark
The algebraic identity in Theorem [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"} is elementary. Its force comes from upstream hardness: reducing $|R(P)|$ by exact relevance minimization is worst-case intractable under the succinct encoding, so redistribution is often the only tractable lever available.
:::

::: theorem
[]{#thm:tax-grows label="thm:tax-grows"} For $n$ decision sites: $$\text{TotalExternalWork} = n \times \text{SimplicityTax}(M, P).$$ *(Lean: `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`)*
:::

::: proof
*Proof.* This is by definition of per-site externalization and is mechanized as `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`. ◻
:::

::: theorem
[]{#thm:amortization label="thm:amortization"} Let $H_{\text{central}}$ be the one-time cost of using a complete model. There exists $$n^* = \left\lfloor \frac{H_{\text{central}}}{\text{SimplicityTax}(M,P)} \right\rfloor$$ such that for $n > n^*$, the complete model has lower total cost. *(Lean: `HardnessDistribution.complete_model_dominates_after_threshold`)*
:::

::: proof
*Proof.* For positive per-site tax, the threshold inequality $$n > \left\lfloor \frac{H_{\text{central}}}{\text{SimplicityTax}} \right\rfloor
\implies
H_{\text{central}} < n\cdot \text{SimplicityTax}$$ is mechanized as `HardnessDistribution.complete_model_dominates_after_threshold`. ◻
:::

::: corollary
[]{#cor:gap-externalization label="cor:gap-externalization"} If $\text{Gap}(M,P)\neq\emptyset$, then external handling cost scales linearly with the number of decision sites. *(Lean: `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`, `HardnessDistribution.simplicityTax_grows`)*
:::

::: proof
*Proof.* The exact linear form is `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`. When the gap is nonempty (positive tax), monotone growth with $n$ is `HardnessDistribution.simplicityTax_grows`. ◻
:::

::: corollary
[]{#cor:gap-minimization-hard label="cor:gap-minimization-hard"} For mechanized Boolean-coordinate instances, "there exists a sufficient set of size at most $k$" is equivalent to "the relevant-coordinate set has cardinality at most $k$." *(Lean: `Sigma2PHardness.min_sufficient_set_iff_relevant_card`)*
:::

::: proof
*Proof.* This is `Sigma2PHardness.min_sufficient_set_iff_relevant_card`. ◻
:::

Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} provides theorem statements and module paths for the corresponding Lean formalization.


# Related Work {#sec:related}

## Computational Decision Theory

The complexity of decision-making has been studied extensively. Papadimitriou [@papadimitriou1994complexity] established foundational results on the complexity of game-theoretic solution concepts. Our work extends this to the meta-question of identifying relevant information. For a modern treatment of complexity classes, see Arora and Barak [@arora2009computational].

#### Closest prior work and novelty.

Closest to our contribution is the feature-selection/model-selection hardness literature, which proves NP-hardness and inapproximability for predictive subset selection [@blum1997selection; @amaldi1998complexity]. Our contribution is stronger on two axes not provided by those works: (i) machine-checked reductions (TAUTOLOGY and $\exists\forall$-SAT mappings with explicit polynomial bounds), and (ii) a complete hardness/tractability landscape for decision relevance under explicit encoding assumptions. We study decision relevance rather than predictive compression, and we formalize the core reductions in Lean 4 rather than leaving them only on paper.

## Feature Selection

In machine learning, feature selection asks which input features are relevant for prediction. This is known to be NP-hard in general [@blum1997selection]. Our results show the decision-theoretic analog is -complete for both checking and minimization.

## Value of Information

The value of information (VOI) framework [@howard1966information] quantifies the maximum rational payment for information. Our work addresses a different question: not the *value* of information, but the *complexity* of identifying which information has value.

## Model Selection

Statistical model selection (AIC [@akaike1974new], BIC [@schwarz1978estimating], cross-validation [@stone1974cross]) provides practical heuristics for choosing among models. Our results formalize the regime-level reason heuristic selection appears: without added structural assumptions, exact optimal model selection inherits worst-case intractability, so heuristic methods implement explicit weakened-guarantee policies for unresolved structure.

## Certifying Outputs and Proof-Carrying Claims

Our integrity layer matches the certifying-algorithms pattern: algorithms emit candidate outputs together with certificates that can be checked quickly, separating *producing* claims from *verifying* claims [@mcconnell2010certifying]. In this paper, Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"} is exactly that soundness discipline.

At the systems level, this is the same architecture as proof-carrying code: a producer ships evidence and a consumer runs a small checker before accepting the claim [@necula1997proof]. Our competence definition adds the regime-specific coverage/resource requirement that certifying soundness alone does not provide.

The feasibility qualifier in Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"} also aligns with bounded-rationality normativity: what agents *should* do is constrained by what is computationally feasible under the declared resource model [@sep_bounded_rationality].


# Conclusion

## Methodology and Disclosure {#methodology-and-disclosure .unnumbered}

**Role of LLMs in this work.** This paper was developed through human-AI collaboration. The author provided the core intuitions---the connection between decision-relevance and computational complexity, the conjecture that SUFFICIENCY-CHECK is -complete, and the insight that the $\SigmaP{2}$ structure collapses for MINIMUM-SUFFICIENT-SET. Large language models (Claude, GPT-4) served as implementation partners for proof drafting, Lean formalization, and LaTeX generation.

The Lean 4 proofs were iteratively refined: the author specified the target statements, the LLM proposed proof strategies, and the Lean compiler served as the arbiter of correctness. The complexity-theoretic reductions required careful human oversight to ensure the polynomial bounds were correctly established.

**What the author contributed:** The problem formulations (SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, ANCHOR-SUFFICIENCY), the hardness conjectures, the tractability conditions, and the connection to over-modeling in engineering practice.

**What LLMs contributed:** LaTeX drafting, Lean tactic exploration, reduction construction assistance, and prose refinement.

The proofs are machine-checked; their validity is independent of generation method. We disclose this methodology in the interest of academic transparency.

::: center

----------------------------------------------------------------------------------------------------
:::

## Summary of Results {#summary-of-results .unnumbered}

This paper establishes the computational complexity of coordinate sufficiency problems:

-   **SUFFICIENCY-CHECK** is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"})

-   **MINIMUM-SUFFICIENT-SET** is -complete (Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"})

-   **ANCHOR-SUFFICIENCY** is $\SigmaP{2}$-complete (Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"})

-   An encoding-regime separation contrasts explicit-state polynomial-time (polynomial in $|S|$) with a succinct worst-case ETH lower bound witnessed by a hard family with $k^*=n$ (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"})

-   Tractable subcases exist for explicit-state encoding, separable utility, and tree-structured utility with explicit local factors (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"})

These results place the problem of identifying decision-relevant coordinates at the first and second levels of the polynomial hierarchy.

Beyond classification, the paper contributes a formal claim-typing framework (Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"}): structural complexity is a property of the fixed decision relation, while representational hardness is regime-conditional access cost. This is why encoding-regime changes can move practical hardness without changing the underlying semantics.

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} for proof listings). The formalization verifies that the TAUTOLOGY reduction correctly maps tautologies to sufficient coordinate sets; complexity classifications (coNP-completeness, $\SigmaP{2}$-completeness) follow by composition with standard complexity-theoretic results (TAUTOLOGY is -complete, $\exists\forall$-SAT is $\SigmaP{2}$-complete). The strengthened gadget showing that non-tautologies yield instances with *all coordinates relevant* is also formalized.

## Complexity Characterization {#complexity-characterization .unnumbered}

The results provide precise complexity characterizations within the formal model:

1.  **Exact bounds.** SUFFICIENCY-CHECK is -complete---both -hard and in .

2.  **Constructive reductions.** The reductions from TAUTOLOGY and $\exists\forall$-SAT are explicit and machine-checked.

3.  **Encoding-regime separation.** Under the explicit-state encoding, SUFFICIENCY-CHECK is polynomial in $|S|$. Under ETH, there exist succinctly encoded worst-case instances (witnessed by a strengthened gadget family with $k^*=n$) requiring $2^{\Omega(n)}$ time. Intermediate regimes are not ruled out by the lower-bound statement.

## The Complexity Redistribution Corollary {#the-complexity-redistribution-corollary .unnumbered}

Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} develops a quantitative consequence: when a problem requires $k$ dimensions and a model handles only $j < k$ natively, the remaining $k - j$ dimensions must be handled externally at each decision site. For $n$ sites, total external work is $(k-j) \times n$.

The set identity is elementary; its operational content comes from composition with the hardness results on exact relevance minimization. This redistribution corollary is formalized in Lean 4 (`HardnessDistribution.lean`), proving:

-   Redistribution identity: complexity burden cannot be eliminated by omission, only moved between native handling and external handling

-   Dominance: complete models have lower total work than incomplete models

-   Amortization: there exists a threshold $n^*$ beyond which higher-dimensional models have lower total cost

## Open Questions {#open-questions .unnumbered}

Several questions remain for future work:

-   **Fixed-parameter tractability (primary):** Is SUFFICIENCY-CHECK FPT when parameterized by the minimal sufficient-set size $k^*$, or is it W\[2\]-hard under this parameterization?

-   **Sequential/stochastic bridge extension:** Characterize the exact frontier where adjacent sequential objectives reduce to the static class via Proposition [\[prop:one-step-bridge\]](#prop:one-step-bridge){reference-type="ref" reference="prop:one-step-bridge"}, and where genuinely new complexity objects (e.g., horizon/sample/regret complexity) must replace the present coNP/$\Sigma_2^P$ analysis.

-   **Average-case complexity:** What is the complexity under natural distributions on decision problems?

-   **Learning cost formalization:** Can central cost $H_{\text{central}}$ be formalized as the rank of a concept matroid, making the amortization threshold precisely computable?

## Practical Corollaries {#practical-corollaries .unnumbered}

The practical corollaries are regime-indexed and theorem-indexed:

-   **\[E\] and structured regimes:** polynomial-time exact procedures exist (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

-   **\[S+ETH\] hard families:** exact minimization inherits exponential worst-case cost (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} together with Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}).

-   **\[S_bool\] mechanized criterion:** minimization reduces to relevance-cardinality constraints (Corollary [\[cor:practice-diagnostic\]](#cor:practice-diagnostic){reference-type="ref" reference="cor:practice-diagnostic"}).

-   **Redistribution consequences:** omitted native coverage externalizes work with explicit growth/amortization laws (Theorems [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"}--[\[thm:amortization\]](#thm:amortization){reference-type="ref" reference="thm:amortization"}).

Hence the design choice is typed: enforce a tractable regime, or adopt weakened guarantees with explicit verification boundaries.


# Lean 4 Proof Listings {#app:lean}

The complete Lean 4 formalization is available in the companion artifact (Zenodo DOI listed on the title page). The mechanization consists of 7071 lines across 42 files, with 310 theorem/lemma statements.

## What Is Machine-Checked

The Lean formalization establishes:

1.  **Correctness of the TAUTOLOGY reduction:** The theorem `tautology_iff_sufficient` proves that the mapping from Boolean formulas to decision problems preserves the decision structure (accept iff the formula is a tautology).

2.  **Decision problem definitions:** Formal definitions of sufficiency, optimality, and the decision quotient.

3.  **Economic theorems:** Simplicity Tax redistribution identities and hardness distribution results.

**Complexity classifications** (coNP-completeness, $\Sigma_2^P$-completeness) follow by conditional composition with standard results (e.g., TAUTOLOGY coNP-completeness and $\exists\forall$-SAT $\Sigma_2^P$-completeness), represented explicitly as hypotheses in the conditional transfer theorems listed below. The Lean proofs verify the reduction constructions and the transfer closures under those hypotheses.

## Polynomial-Time Reduction Definition

We use Mathlib's Turing machine framework to define polynomial-time computability:

    /-- Polynomial-time computable function using Turing machines -/
    def PolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) 
        (f : α → β) : Prop :=
      Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

    /-- Polynomial-time many-one (Karp) reduction -/
    def ManyOneReducesPoly {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
        (A : Set α) (B : Set β) : Prop :=
      ∃ f : α → β, PolyTime ea eb f ∧ ∀ x, x ∈ A ↔ f x ∈ B

This uses the standard definition: a reduction is polynomial-time computable via Turing machines and preserves membership.

## The Main Reduction Theorem

::: theorem
The reduction from TAUTOLOGY to SUFFICIENCY-CHECK is correct:
:::

    theorem tautology_iff_sufficient (φ : Formula n) :
        φ.isTautology ↔ (reductionProblem φ).isSufficient Finset.empty

This theorem is proven by showing both directions:

-   If $\varphi$ is a tautology, then the empty coordinate set is sufficient

-   If the empty coordinate set is sufficient, then $\varphi$ is a tautology

The proof verifies that the utility construction in `reductionProblem` creates the appropriate decision structure where:

-   At reference states, `accept` is optimal with utility 1

-   At assignment states, `accept` is optimal iff $\varphi(a) = \text{true}$

## Economic Results

The hardness distribution theorems (Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"}) are fully formalized:

    theorem simplicityTax_conservation (P : SpecificationProblem)
        (S : SolutionArchitecture P) :
        S.centralDOF + simplicityTax P S ≥ P.intrinsicDOF

    theorem simplicityTax_grows (P : SpecificationProblem)
        (S : SolutionArchitecture P) (n₁ n₂ : ℕ)
        (hn : n₁ < n₂) (htax : simplicityTax P S > 0) :
        totalDOF S n₁ < totalDOF S n₂

    theorem native_dominates_manual (P : SpecificationProblem) (n : Nat)
        (hn : n > P.intrinsicDOF) :
        totalDOF (nativeTypeSystem P) n < totalDOF (manualApproach P) n

    theorem totalDOF_eventually_constant_iff_zero_distributed
        (S : SolutionArchitecture P) :
        IsEventuallyConstant (fun n => totalDOF S n) ↔ S.distributedDOF = 0

    theorem no_positive_slope_linear_represents_saturating
        (c d K : ℕ) (hd : d > 0) :
        ¬ (∀ n, c + n * d = generalizedTotalDOF c (saturatingSiteCost K) n)

**Identifier note.** Lean identifiers retain internal naming (`intrinsicDOF`, `simplicityTax_conservation`); in paper terminology these correspond to *baseline hardness* and the *redistribution lower-bound identity*, respectively.

## Complete Claim Coverage Matrix

  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  **Paper handle**                            **Status**           **Lean support**                                                                                                                                                                                                                                                                                                                                       **Notes**
  ------------------------------------------- -------------------- ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ -------------------------------------------------------------------------------------------------------------------------
  `cor:exact-identifiability`                 Full                 `Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`                                                                                                                                                                                                                                                                   Direct theorem mapping.

  `cor:gap-externalization`                   Full                 `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`, `HardnessDistribution.simplicityTax_grows`                                                                                                                                                                                                                                                  Composite from two mechanized theorems.

  `cor:gap-minimization-hard`                 Full                 `Sigma2PHardness.min_sufficient_set_iff_relevant_card`                                                                                                                                                                                                                                                                                                 Direct theorem mapping.

  `cor:generalized-eventual-dominance`        Full                 `HardnessDistribution.generalized_right_eventually_dominates_wrong`                                                                                                                                                                                                                                                                                    Direct theorem mapping.

  `cor:linear-positive-no-saturation`         Full                 `HardnessDistribution.no_positive_slope_linear_represents_saturating`                                                                                                                                                                                                                                                                                  Direct theorem mapping.

  `cor:no-auto-minimize`                      Full (conditional)   `ClaimClosure.no_auto_minimize_of_p_neq_conp`                                                                                                                                                                                                                                                                                                          Mechanized conditional closure: non-collapse plus collapse-implication yields impossibility.

  `cor:overmodel-diagnostic-implication`      Full                 `Sigma2PHardness.sufficient_iff_relevant_subset`                                                                                                                                                                                                                                                                                                       Contrapositive of mechanized theorem.

  `cor:practice-bounded`                      Full                 `sufficiency_poly_bounded_actions`                                                                                                                                                                                                                                                                                                                     Direct theorem mapping.

  `cor:practice-diagnostic`                   Full                 `Sigma2PHardness.min_sufficient_set_iff_relevant_card`                                                                                                                                                                                                                                                                                                 Direct theorem mapping.

  `cor:practice-structured`                   Full                 `sufficiency_poly_separable`                                                                                                                                                                                                                                                                                                                           Direct theorem mapping.

  `cor:practice-tree`                         Full                 `sufficiency_poly_tree_structured`                                                                                                                                                                                                                                                                                                                     Direct theorem mapping.

  `cor:practice-unstructured`                 Full                 `all_coords_relevant_of_not_tautology`                                                                                                                                                                                                                                                                                                                 Direct theorem mapping.

  `cor:right-wrong-hardness`                  Full                 `HardnessDistribution.right_dominates_wrong`                                                                                                                                                                                                                                                                                                           Direct theorem mapping.

  `cor:type-system-threshold`                 Full                 `HardnessDistribution.native_dominates_manual`                                                                                                                                                                                                                                                                                                         Direct theorem mapping.

  `prop:adq-ordering`                         Full                 `ClaimClosure.adq_ordering`                                                                                                                                                                                                                                                                                                                            Strict ordering theorem for shared nonempty behavior denominator.

  `prop:dominance-modes`                      Full                 `HardnessDistribution.right_dominates_wrong`, `HardnessDistribution.centralized_higher_leverage`, `HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`, `HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`, `HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`   Compositional index proposition.

  `prop:generalized-assumption-boundary`      Full                 `HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`, `HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`                                                                                                                                                                                            Direct pair mapping.

  `prop:hardness-conservation`                Full                 `HardnessDistribution.totalDOF_ge_intrinsic`                                                                                                                                                                                                                                                                                                           Direct structural core theorem.

  `prop:hardness-efficiency-interpretation`   Full                 `HardnessDistribution.hardnessEfficiency_eq_central_share`                                                                                                                                                                                                                                                                                             Direct definitional equivalence.

  `prop:integrity-competence-separation`      Full                 `IntegrityCompetence.competence_implies_integrity`, `IntegrityCompetence.integrity_not_competent_of_nonempty_scope`                                                                                                                                                                                                                                    Direct pair mapping.

  `prop:one-step-bridge`                      Full                 `ClaimClosure.one_step_bridge`                                                                                                                                                                                                                                                                                                                         One-step deterministic bridge is mechanized as an equivalence of sufficiency predicates.

  `prop:sufficiency-char`                     Full                 `ClaimClosure.sufficiency_iff_dq_ratio`, `ClaimClosure.sufficiency_iff_projectedOptCover_eq_opt`                                                                                                                                                                                                                                                       Finite-model quotient characterization mechanized in both ratio form and projected-cover form.

  `thm:amortization`                          Full                 `HardnessDistribution.complete_model_dominates_after_threshold`                                                                                                                                                                                                                                                                                        Direct theorem mapping.

  `thm:anchor-sigma2p`                        Full (conditional)   `ClaimClosure.anchor_sigma2p_reduction_core`, `ClaimClosure.anchor_sigma2p_complete_conditional`, `anchor_sufficiency_sigma2p`                                                                                                                                                                                                                         Reduction core is mechanized; completeness lift is mechanized as a conditional transfer on standard source-class facts.

  `thm:centralization-dominance`              Full                 `HardnessDistribution.centralization_dominance_bundle`, `HardnessDistribution.centralization_step_saves_n_minus_one`                                                                                                                                                                                                                                   Direct pair mapping.

  `thm:config-reduction`                      Full                 `ConfigReduction.config_sufficiency_iff_behavior_preserving`                                                                                                                                                                                                                                                                                           Direct theorem mapping.

  `thm:cost-asymmetry-eth`                    Full (conditional)   `ClaimClosure.cost_asymmetry_eth_conditional`, `HardnessDistribution.linear_lt_exponential_plus_constant_eventually`                                                                                                                                                                                                                                   Asymptotic dominance and ETH-conditioned lift are both mechanized.

  `thm:dichotomy`                             Full (conditional)   `ClaimClosure.dichotomy_conditional`, `ClaimClosure.hard_family_all_coords_core`, `ClaimClosure.explicit_state_upper_core`                                                                                                                                                                                                                             Upper-branch core and hard-family core are mechanized; ETH lower branch is mechanized as conditional transfer.

  `thm:generalized-dominance`                 Full                 `HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`                                                                                                                                                                                                                                                                  Direct theorem mapping.

  `thm:generalized-saturation-possible`       Full                 `HardnessDistribution.saturatingSiteCost_eventually_constant`, `HardnessDistribution.generalizedTotal_with_saturation_eventually_constant`                                                                                                                                                                                                             Direct construction mapping.

  `thm:linear-saturation-iff-zero`            Full                 `HardnessDistribution.totalDOF_eventually_constant_iff_zero_distributed`                                                                                                                                                                                                                                                                               Direct theorem mapping.

  `thm:minsuff-collapse`                      Full (conditional)   `ClaimClosure.minsuff_collapse_core`, `ClaimClosure.minsuff_collapse_to_conp_conditional`, `Sigma2PHardness.min_sufficient_set_iff_relevant_card`                                                                                                                                                                                                      Quantifier collapse core and coNP-reading lift are mechanized.

  `thm:minsuff-conp`                          Full (conditional)   `ClaimClosure.minsuff_collapse_core`, `ClaimClosure.minsuff_conp_complete_conditional`                                                                                                                                                                                                                                                                 coNP-completeness transfer is mechanized conditionally from the collapse core.

  `thm:overmodel-diagnostic`                  Full                 `ClaimClosure.no_exact_identifier_implies_not_boundary_characterized`, `ClaimClosure.boundaryCharacterized_iff_exists_sufficient_subset`, `ConfigReduction.config_sufficiency_iff_behavior_preserving`                                                                                                                                                 Contrapositive diagnostic step mechanized under explicit boundary-characterization definition.

  `thm:sufficiency-conp`                      Full (conditional)   `ClaimClosure.sufficiency_conp_reduction_core`, `ClaimClosure.sufficiency_conp_complete_conditional`, `tautology_iff_sufficient`                                                                                                                                                                                                                       Reduction core and coNP-completeness transfer are mechanized conditionally.

  `thm:tax-conservation`                      Full                 `HardnessDistribution.gap_conservation_card`                                                                                                                                                                                                                                                                                                           Direct theorem mapping.

  `thm:tax-grows`                             Full                 `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`                                                                                                                                                                                                                                                                                              Direct theorem mapping.

  `thm:tractable`                             Full (conditional)   `ClaimClosure.tractable_bounded_core`, `ClaimClosure.tractable_separable_core`, `ClaimClosure.tractable_tree_core`, `ClaimClosure.tractable_subcases_conditional`                                                                                                                                                                                      All three tractable branch cores and assembly closure are mechanized.
  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

## Claims Not Fully Mechanized

**Status:** all theorem/proposition/corollary handles in this paper now have Lean backing. Entries marked **Full (conditional)** are explicitly mechanized transfer theorems that depend on standard external complexity facts (e.g., source-class completeness or ETH assumptions), with those dependencies represented as hypotheses in Lean.

## Module Structure

-   `Basic.lean` -- Core definitions (DecisionProblem, sufficiency, optimality)

-   `Sufficiency.lean` -- Sufficiency checking algorithms and properties

-   `Reduction.lean` -- TAUTOLOGY reduction construction and correctness

-   `Hardness/ConfigReduction.lean` -- Sentinel-action configuration reduction theorem

-   `Complexity.lean` -- Polynomial-time reduction definitions using mathlib

-   `HardnessDistribution.lean` -- Simplicity Tax redistribution and amortization theorems

-   `IntegrityCompetence.lean` -- Solver integrity vs regime competence separation

-   `ClaimClosure.lean` -- Mechanized closure of paper-level bridge and diagnostic claims

-   `Tractability/` -- Bounded actions, separable utilities, tree structure

## Verification

The proofs compile with Lean 4 and contain no `sorry` placeholders. Run `lake build` in the proof directory to verify.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper4_decision_quotient/proofs/`
- Lines: 7071
- Theorems: 310
- `sorry` placeholders: 0
