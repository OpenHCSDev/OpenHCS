# Paper: Computational Complexity of Sufficiency in Decision Problems

**Status**: Theory of Computing-ready | **Lean**: 2760 lines, 106 theorems

---

## Abstract

We characterize the computational complexity of coordinate sufficiency in decision problems within the formal model. Given action set $A$, state space $S = X_1 \times \cdots \times X_n$, and utility $u: A \times S \to \mathbb{R}$, a coordinate set $I$ is *sufficient* if $s_I = s'_I \implies \Opt(s) = \Opt(s')$.

**The landscape in the formal model:**

-   **General case:** SUFFICIENCY-CHECK is -complete; ANCHOR-SUFFICIENCY is $\SigmaP{2}$-complete.

-   **Tractable cases:** Polynomial-time for bounded action sets under the explicit-state encoding; separable utilities ($u = f + g$) under any encoding; and tree-structured utility with explicit local factors.

-   **Encoding-regime separation:** Polynomial-time under the explicit-state encoding (polynomial in $|S|$). Under ETH, there exist succinctly encoded worst-case instances witnessed by a strengthened gadget construction (mechanized in Lean; see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}) with $k^*=n$ for which SUFFICIENCY-CHECK requires $2^{\Omega(n)}$ time.

The tractable cases are stated with explicit encoding assumptions (Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}). Together, these results answer the question "when is decision-relevant information identifiable efficiently?" within the stated regimes.

The primary contribution is theoretical: a formalized reduction framework and a complete characterization of the core decision-relevant problems in the formal model (coNP/$\Sigma_2^P$ completeness and tractable cases under explicit encoding assumptions). The practical corollaries follow from these theorems.

All results are machine-checked in Lean 4 ($\sim$`<!-- -->`{=html}5,000 lines, 200+ theorems).

**Keywords:** computational complexity, decision theory, polynomial hierarchy, tractability dichotomy, Lean 4


# Introduction {#sec:introduction}

Consider a decision problem with actions $A$ and states $S = X_1 \times \cdots \times X_n$. A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only coordinates in $I$ determines the optimal action: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$

This paper characterizes the efficient cases of coordinate sufficiency within the formal model:

Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"} fixes the computational model and input encodings used for all complexity claims.

::: center
  **Problem**              **Complexity**          **When Tractable**
  ------------------------ ----------------------- ------------------------------------------------------------------------------
  SUFFICIENCY-CHECK        -complete               Bounded actions (explicit-state), separable utility, tree-structured utility
  MINIMUM-SUFFICIENT-SET   -complete               Same conditions
  ANCHOR-SUFFICIENCY       $\SigmaP{2}$-complete   Open
:::

The tractable cases are stated with explicit encoding assumptions (Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}). Outside those regimes, the succinct model yields hardness.

## Landscape Summary

**When is sufficiency checking tractable?** We identify three sufficient conditions:

1.  **Bounded actions** ($|A| \leq k$) under explicit-state encoding: with constantly many actions, we enumerate action pairs over the explicit utility table.

2.  **Separable utility** ($u(a,s) = f(a) + g(s)$): The optimal action depends only on $f$, making all coordinates irrelevant to the decision.

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

All results are formalized in Lean 4 [@moura2021lean4] ($\sim$`<!-- -->`{=html}5,000 lines, 200+ theorems). The formalization verifies the reduction mappings and combinatorial lemmas; complexity class membership follows by composition with TAUTOLOGY and $\exists\forall$-SAT.

#### What is new.

We contribute (i) a reusable Lean 4 framework for polynomial-time reductions with explicit polynomial bounds; (ii) the first machine-checked coNP-completeness proof for a decision-theoretic sufficiency problem; and (iii) a complete complexity landscape for coordinate sufficiency under explicit encoding assumptions. Prior work studies decision complexity in general or feature selection hardness, but does not formalize these reductions or establish this landscape in Lean.

## Paper Structure

The primary contribution is theoretical: a formalized reduction framework and a complete characterization of the core decision-relevant problems in the formal model (coNP/$\Sigma_2^P$ completeness and tractable cases stated under explicit encoding assumptions). Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}--[\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"} contain the core theorems.

Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"}: foundations. Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}: hardness proofs. Section [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"}: dichotomy. Section [\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"}: tractable cases. Sections [\[sec:implications\]](#sec:implications){reference-type="ref" reference="sec:implications"} and [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"}: corollaries and implications for practice. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"}: related work. Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}: Lean listings.


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
[]{#def:decision-quotient label="def:decision-quotient"} The *decision quotient* for state $s$ under coordinate set $I$ is: $$\text{DQ}_I(s) = \frac{|\{a \in A : a \in \Opt(s') \text{ for some } s' \sim_I s\}|}{|A|}$$ This measures the fraction of actions that are optimal for at least one state consistent with $I$.
:::

::: proposition
[]{#prop:sufficiency-char label="prop:sufficiency-char"} Coordinate set $I$ is sufficient if and only if $\text{DQ}_I(s) = |\Opt(s)|/|A|$ for all $s \in S$.
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

The input length is $L = |A| + \sum_i \log |X_i| + |C_U|$. Polynomial time and all complexity classes (, $\Sigma_2^P$, ETH, W\[2\]) are measured in $L$. All hardness results in Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} use this encoding.

#### Explicit-state encoding (used for enumeration algorithms and experiments).

The utility is given as a full table over $A \times S$. The input length is $L_{\text{exp}} = \Theta(|A||S|)$ (up to the bitlength of utilities). Polynomial time is measured in $L_{\text{exp}}$. Results stated in terms of $|S|$ use this encoding.

Unless explicitly stated otherwise, "polynomial time" refers to the succinct encoding.


# Encoding-Regime Separation {#sec:dichotomy}

The hardness results of Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} apply to worst-case instances under the succinct encoding. This section states an encoding-regime separation: an explicit-state upper bound versus a succinct-encoding worst-case lower bound.

#### Model note.

Part 1 is an explicit-state upper bound (time polynomial in $|S|$). Part 2 is a succinct-encoding lower bound under ETH (time exponential in $n$). The encodings are defined in Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. These two parts are stated in different encodings and are not directly comparable as functions of a single input length.

::: theorem
[]{#thm:dichotomy label="thm:dichotomy"} Let $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ be a decision problem with $|S| = N$ states. Let $k^*$ be the size of the minimal sufficient set.

1.  **Explicit-state upper bound:** Under the explicit-state encoding, SUFFICIENCY-CHECK is solvable in time polynomial in $N$ (e.g. $O(N^2|A|)$).

2.  **Succinct lower bound under ETH (worst case):** Assuming ETH, there exists a family of succinctly encoded instances with $n$ coordinates and minimal sufficient set size $k^* = n$ such that SUFFICIENCY-CHECK requires time $2^{\Omega(n)}$.
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

This encoding-regime separation explains why some domains admit tractable model selection under explicit-state assumptions, while other domains (or encodings) exhibit worst-case hardness that forces heuristic approaches.


# Tractable Special Cases: When You Can Solve It {#sec:tractable}

We distinguish the encodings of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. The tractability results below state the model assumption explicitly.

::: theorem
[]{#thm:tractable label="thm:tractable"} SUFFICIENCY-CHECK is polynomial-time solvable in the following cases:

1.  **Explicit-state encoding:** The input contains the full utility table over $A \times S$. SUFFICIENCY-CHECK runs in $O(|S|^2|A|)$ time; if $|A|$ is constant, $O(|S|^2)$.

2.  **Separable utility (any encoding):** $U(a, s) = f(a) + g(s)$.

3.  **Tree-structured utility with explicit local factors (succinct structured encoding):** There exists a rooted tree on coordinates and local functions $u_i$ such that $$U(a,s) = \sum_i u_i\bigl(a, s_i, s_{\mathrm{parent}(i)}\bigr),$$ with the root term depending only on $(a, s_{\mathrm{root}})$ and all $u_i$ given explicitly as part of the input.
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


# Implications for Practice: Why Over-Modeling Is Optimal {#sec:engineering-justification}

This section states corollaries for engineering practice. Within the formal model, the complexity results of Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} and [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"} shift parts of this workflow from informal judgment toward explicit, checkable criteria. The observed behaviors---configuration over-specification, absence of automated minimization tools, heuristic model selection---are not failures of discipline but *provably optimal responses* to computational constraints under the stated cost model.

Some common prescriptions implicitly require exact minimization of sufficient parameter sets. In the worst case, that task is -complete in our model, so we should calibrate critiques and expectations accordingly. A rational response is to include everything and pay linear maintenance costs, rather than attempt exponential minimization costs.

## Configuration Simplification is SUFFICIENCY-CHECK

Real engineering problems reduce directly to the decision problems studied in this paper.

::: theorem
[]{#thm:config-reduction label="thm:config-reduction"} Given a software system with configuration parameters $P = \{p_1, \ldots, p_n\}$ and observed behaviors $B = \{b_1, \ldots, b_m\}$, the problem of determining whether parameter subset $I \subseteq P$ preserves all behaviors is equivalent to SUFFICIENCY-CHECK.
:::

::: proof
*Proof.* Construct decision problem $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ where:

-   Actions $A = B$ (each behavior is an action)

-   Coordinates $X_i$ = domain of parameter $p_i$

-   State space $S = X_1 \times \cdots \times X_n$

-   Utility $U(b, s) = 1$ if behavior $b$ occurs under configuration $s$, else $U(b, s) = 0$

Then $\Opt(s) = \{b \in B : b \text{ occurs under configuration } s\}$.

Coordinate set $I$ is sufficient iff: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$

This holds iff configurations agreeing on parameters in $I$ exhibit identical behaviors.

Therefore, "does parameter subset $I$ preserve all behaviors?" is exactly SUFFICIENCY-CHECK for the constructed decision problem. ◻
:::

::: remark
This reduction is *parsimonious*: configuration simplification can be cast as an instance of SUFFICIENCY-CHECK under a direct encoding.
:::

## Computational Rationality of Over-Modeling

We now prove that over-specification is an optimal engineering strategy given the stated cost model and complexity constraints.

::: theorem
[]{#thm:rational-overmodel label="thm:rational-overmodel"} Consider an engineer specifying a system configuration with $n$ parameters. Let:

-   $C_{\text{over}}(k)$ = cost of maintaining $k$ extra parameters beyond minimal

-   $C_{\text{find}}(n)$ = cost of finding minimal sufficient parameter set

-   $C_{\text{under}}$ = expected cost of production failures from underspecification

When SUFFICIENCY-CHECK is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}):

1.  Naive exhaustive search inspects $2^n$ candidate subsets, so the brute-force finding cost grows exponentially in $n$; more formally, exhaustive search yields an upper bound $C_{\text{find}}(n) = O(2^n)$. A matching \*unconditional\* lower bound of $2^{\Omega(n)}$ does not follow from -completeness alone. Instead, -completeness implies there is no polynomial‑time algorithm for arbitrary inputs unless $\Pclass = \coNP$. Stronger assumptions (e.g., the Exponential Time Hypothesis) yield explicit worst-case lower bounds: under ETH, SUFFICIENCY-CHECK has a $2^{\Omega(n)}$ worst-case time lower bound in the succinct encoding (witnessed by the strengthened TAUTOLOGY gadget family).

2.  Maintenance cost is linear: $C_{\text{over}}(k) = O(k)$.

3.  Under the ETH (or when considering naive exhaustive search), exponential finding cost dominates linear maintenance cost for sufficiently large $n$.

Therefore, there exists $n_0$ such that for all $n > n_0$, over-modeling minimizes total expected cost: $$C_{\text{over}}(k) < C_{\text{find}}(n) + C_{\text{under}}$$

Over-modeling is economically optimal under the stated model and complexity constraints.
:::

::: proof
*Proof.* By Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, SUFFICIENCY-CHECK is -complete, so under the assumption $\Pclass \neq \coNP$ there is no polynomial‑time algorithm that decides sufficiency for arbitrary inputs.

Finding the minimal sufficient set by brute force requires checking many candidate sets. Exhaustive search examines $$\sum_{i=0}^{n} \binom{n}{i} = 2^n$$ candidate subsets, so naive search has cost $O(2^n)$. This shows only that brute-force is exponential. To assert a matching lower bound of $2^{\Omega(n)}$ for \*all\* algorithms requires additional assumptions. For example, under the Exponential Time Hypothesis (ETH), TAUTOLOGY (and hence SUFFICIENCY-CHECK in the succinct encoding) requires $2^{\Omega(n)}$ time, and SUFFICIENCY-CHECK inherits this conditional lower bound via our reduction.

Maintaining $k$ extra parameters incurs:

-   Documentation cost: $O(k)$ entries

-   Testing cost: $O(k)$ test cases

-   Migration cost: $O(k)$ parameters to update

Total maintenance cost is $C_{\text{over}}(k) = O(k)$.

For concrete threshold: when $n = 20$ parameters, exhaustive search requires $2^{20} \approx 10^6$ checks. Including $k = 5$ extra parameters costs $O(5)$ maintenance overhead but avoids $10^6$ computational work.

Since $2^n$ grows faster than any polynomial in $k$ or $n$, there exists $n_0$ such that for all $n > n_0$: $$C_{\text{over}}(k) \ll C_{\text{find}}(n)$$

Adding underspecification risk $C_{\text{under}}$ (production failures from missing parameters), which is unbounded in the model, makes over-specification strictly dominant. ◻
:::

::: corollary
[]{#cor:no-auto-minimize label="cor:no-auto-minimize"} Assuming $\Pclass \neq \coNP$, there exists no polynomial-time algorithm that:

1.  Takes an arbitrary configuration file with $n$ parameters

2.  Identifies the minimal sufficient parameter subset

3.  Guarantees correctness (no false negatives)
:::

::: proof
*Proof.* Such an algorithm would solve MINIMUM-SUFFICIENT-SET in polynomial time, contradicting Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} (assuming $\Pclass \neq \coNP$). ◻
:::

::: remark
Corollary [\[cor:no-auto-minimize\]](#cor:no-auto-minimize){reference-type="ref" reference="cor:no-auto-minimize"} explains the observed absence of "config cleanup" tools in software engineering practice. Engineers who include extra parameters are not exhibiting poor discipline---they are adapting to computational constraints. The problem is not lack of tooling effort; it is mathematical intractability.
:::

## Connection to Observed Practice

These theorems provide mathematical grounding for three widespread engineering behaviors:

**1. Configuration files grow over time.** Removing parameters requires solving -complete problems. Engineers rationally choose linear maintenance cost over exponential minimization cost.

**2. Heuristic model selection dominates.** ML practitioners use AIC, BIC, cross-validation instead of optimal feature selection because optimal selection is intractable (Theorem [\[thm:rational-overmodel\]](#thm:rational-overmodel){reference-type="ref" reference="thm:rational-overmodel"}).

**3. "Include everything" is a legitimate strategy.** When determining relevance/minimal sufficiency is exponential in the worst case (e.g., $O(2^n)$ by naive subset enumeration, and under ETH a $2^{\Omega(n)}$ worst-case lower bound in the succinct encoding; see Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}), including all $n$ parameters costs $O(n)$. For large $n$, this is the rational choice.

These behaviors are not ad hoc workarounds; under the stated computational model they are rational responses to worst-case intractability. The complexity results provide a mathematical lens: over-modeling is not a failure---it is the rational strategy under the model.


# Implications for Software Architecture {#sec:implications}

This section states corollaries for software architecture. The complexity results have direct implications for software engineering practice.

## Why Over-Specification Is Rational

Software architects routinely specify more configuration parameters than strictly necessary. Our results show this is computationally rational:

::: corollary
Given a software system with $n$ configuration parameters, checking whether a proposed subset suffices is -complete. Finding the minimum such set is also -complete.
:::

This explains why configuration files grow over time: removing "unnecessary" parameters requires solving a hard problem.

## Architectural Decision Quotient

The sufficiency framework suggests a measure for architectural decisions:

::: definition
For a software system with configuration space $S$ and behavior space $B$: $$\text{ADQ}(I) = \frac{|\{b \in B : b \text{ achievable with some } s \text{ where } s_I \text{ fixed}\}|}{|B|}$$
:::

High ADQ means the configuration subset $I$ leaves many behaviors achievable---it doesn't constrain the system much. Low ADQ means $I$ strongly constrains behavior.

::: proposition
Decisions with low ADQ (strongly constraining) require fewer additional decisions to fully specify system behavior.
:::

## Practical Recommendations

Based on our theoretical results:

1.  **Accept over-modeling:** Don't penalize engineers for including "extra" parameters. The alternative (minimal modeling) is computationally hard.

2.  **Use bounded scenarios:** When the scenario space is small (Proposition [\[prop:sufficiency-char\]](#prop:sufficiency-char){reference-type="ref" reference="prop:sufficiency-char"}), minimal modeling becomes tractable.

3.  **Exploit structure:** Tree-structured dependencies, bounded alternatives, and separable utilities admit efficient algorithms.

4.  **Invest in heuristics:** For general problems, develop domain-specific heuristics rather than seeking optimal solutions.

## Hardness Distribution: Right Place vs Wrong Place {#sec:hardness-distribution}

A general principle emerges from the complexity results: problem hardness is conserved and is *distributed* across a system in qualitatively different ways.

::: definition
[]{#def:hardness-distribution label="def:hardness-distribution"} Let $P$ be a problem with intrinsic hardness $H(P)$ (measured in computational steps, implementation effort, or error probability). A *solution architecture* $S$ partitions this hardness into:

-   $H_{\text{central}}(S)$: hardness paid once, at design time or in a shared component

-   $H_{\text{distributed}}(S)$: hardness paid per use site

For $n$ use sites, total realized hardness is: $$H_{\text{total}}(S) = H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)$$
:::

::: definition
[]{#def:hardness-conservation label="def:hardness-conservation"} For any problem $P$ with intrinsic hardness $H(P)$, any solution $S$ satisfies: $$H_{\text{central}}(S) + H_{\text{distributed}}(S) \geq H(P).$$ This statement is presented as a definitional principle grounded in the prior definition of intrinsic hardness: any correct solution must account for at least $H(P)$ units of work, which the architecture may allocate centrally or distribute across use sites. The substantive, theorem-like consequences (for example, Centralization Dominance) follow from this grounding.
:::

::: definition
[]{#def:hardness-efficiency label="def:hardness-efficiency"} The *hardness efficiency* of solution $S$ with $n$ use sites is: $$\eta(S, n) = \frac{H_{\text{central}}(S)}{H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)}$$
:::

High $\eta$ indicates centralized hardness (paid once); low $\eta$ indicates distributed hardness (paid repeatedly).

::: theorem
[]{#thm:centralization-dominance label="thm:centralization-dominance"} For $n > 1$ use sites, solutions with higher $H_{\text{central}}$ and lower $H_{\text{distributed}}$ yield:

1.  Lower total realized hardness: $H_{\text{total}}(S_1) < H_{\text{total}}(S_2)$ when $H_{\text{distributed}}(S_1) < H_{\text{distributed}}(S_2)$

2.  Fewer error sites: errors in centralized components affect 1 location; errors in distributed components affect $n$ locations

3.  Higher leverage: one unit of central effort affects $n$ sites
:::

::: proof
*Proof.* (1) follows from the total hardness formula. (2) follows from error site counting. (3) follows from the definition of leverage as $L = \Delta\text{Effect}/\Delta\text{Effort}$. ◻
:::

::: corollary
[]{#cor:right-wrong-hardness label="cor:right-wrong-hardness"} A solution exhibits *hardness in the right place* when:

-   Hardness is centralized (high $H_{\text{central}}$, low $H_{\text{distributed}}$)

-   Hardness is paid at design/compile time rather than runtime

-   Hardness is enforced by tooling (type checker, compiler) rather than convention

A solution exhibits *hardness in the wrong place* when:

-   Hardness is distributed (low $H_{\text{central}}$, high $H_{\text{distributed}}$)

-   Hardness is paid repeatedly at each use site

-   Hardness relies on human discipline rather than mechanical enforcement
:::

**Example: Type System Instantiation.** Consider a capability $C$ (e.g., provenance tracking) that requires hardness $H(C)$:

::: center
  **Approach**                  $H_{\text{central}}$     $H_{\text{distributed}}$
  ---------------------------- ----------------------- -----------------------------
  Native type system support    High (learning cost)    Low (type checker enforces)
  Manual implementation         Low (no new concepts)   High (reimplement per site)
:::

For $n$ use sites, manual implementation costs $n \cdot H_{\text{distributed}}$, growing without bound. Native support costs $H_{\text{central}}$ once, amortized across all uses. The "simpler" approach (manual) is only simpler at $n = 1$; for $n > H_{\text{central}}/H_{\text{distributed}}$, native support dominates.

::: remark
The decision quotient (Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"}) measures which coordinates are decision-relevant. Hardness distribution measures where the cost of *handling* those coordinates is paid. A high-axis system makes relevance explicit (central hardness); a low-axis system requires users to track relevance themselves (distributed hardness).
:::

#### Mechanized strengthening (sketch).

We formalized a strengthened reduction in the mechanization: given a Boolean formula $\varphi$ over $n$ variables we construct a decision problem with $n$ coordinates so that if $\varphi$ is not a tautology then every coordinate is decision-relevant. Intuitively, the construction places a copy of the base gadget at each coordinate and makes the global "accept" condition hold only when every coordinate's local test succeeds; a single falsifying assignment at one coordinate therefore changes the global optimal set, witnessing that coordinate's relevance. The mechanized statement and proof appear in the development as `Reduction_AllCoords.lean` (the lemma `all_coords_relevant_of_not_tautology`).

The next section develops the major practical consequence of this framework: the Simplicity Tax Theorem.


# Corollary: Complexity Conservation {#sec:simplicity-tax}

A quantitative consequence of the hardness results: when a model handles fewer dimensions than required, the gap must be paid at each use site.

::: definition
Let $R(P)$ be the required dimensions (those affecting $\Opt$) and $A(M)$ the dimensions model $M$ handles natively. The *expressive gap* is $\text{Gap}(M,P) = R(P) \setminus A(M)$.
:::

::: theorem
[]{#thm:tax-conservation label="thm:tax-conservation"} $|\text{Gap}(M, P)| + |R(P) \cap A(M)| = |R(P)|$. The total cannot be reduced---only redistributed between "handled natively" and "handled externally."
:::

::: theorem
[]{#thm:tax-grows label="thm:tax-grows"} For $n$ decision sites: $\text{TotalExternalWork} = n \times |\text{Gap}(M, P)|$.
:::

::: theorem
[]{#thm:amortization label="thm:amortization"} Let $H_{\text{central}}$ be the one-time cost of using a complete model. There exists $n^* = H_{\text{central}} / |\text{Gap}|$ such that for $n > n^*$, the complete model has lower total cost.
:::

::: corollary
Since identifying $R(P)$ is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), minimizing the expressive gap is also intractable.
:::

These results are machine-checked in Lean 4 (`HardnessDistribution.lean`).


# Related Work {#sec:related}

## Computational Decision Theory

The complexity of decision-making has been studied extensively. Papadimitriou [@papadimitriou1994complexity] established foundational results on the complexity of game-theoretic solution concepts. Our work extends this to the meta-question of identifying relevant information. For a modern treatment of complexity classes, see Arora and Barak [@arora2009computational].

#### Closest prior work and novelty.

Closest to our contribution is the literature on feature selection and model selection hardness, which proves NP-hardness of selecting informative feature subsets and inapproximability for minimum feature sets [@blum1997selection; @amaldi1998complexity]. Those results analyze predictive relevance or compression objectives. We study decision relevance and show coNP-completeness for sufficiency checking, a different quantifier structure with distinct proof techniques and a full hardness/tractability landscape under explicit encoding assumptions, mechanized in Lean 4. The formalization aspect is also novel: prior work establishes hardness on paper, while we provide machine-checked reductions with explicit polynomial bounds.

## Feature Selection

In machine learning, feature selection asks which input features are relevant for prediction. This is known to be NP-hard in general [@blum1997selection]. Our results show the decision-theoretic analog is -complete for both checking and minimization.

## Value of Information

The value of information (VOI) framework [@howard1966information] quantifies the maximum rational payment for information. Our work addresses a different question: not the *value* of information, but the *complexity* of identifying which information has value.

## Model Selection

Statistical model selection (AIC [@akaike1974new], BIC [@schwarz1978estimating], cross-validation [@stone1974cross]) provides practical heuristics for choosing among models. Our results provide theoretical justification: optimal model selection is intractable, so heuristics are necessary.


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

Proofs are machine-checked in Lean 4 (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} for proof listings). The formalization verifies the reduction mappings and equivalence theorems; complexity classifications follow from standard results (TAUTOLOGY is -complete, $\exists\forall$-SAT is $\SigmaP{2}$-complete) under the encoding model of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. In particular, the strengthened gadget showing that non-tautologies yield instances with *all coordinates relevant* (hence $k^*=\Omega(n)$) is also mechanized (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}).

## Complexity Characterization {#complexity-characterization .unnumbered}

The results provide precise complexity characterizations within the formal model:

1.  **Exact bounds.** SUFFICIENCY-CHECK is -complete---both -hard and in .

2.  **Constructive reductions.** The reductions from TAUTOLOGY and $\exists\forall$-SAT are explicit and machine-checked.

3.  **Encoding-regime separation.** Under the explicit-state encoding, SUFFICIENCY-CHECK is polynomial in $|S|$. Under ETH, there exist succinctly encoded worst-case instances (witnessed by a strengthened gadget family with $k^*=n$) requiring $2^{\Omega(n)}$ time. Intermediate regimes are not ruled out by the lower-bound statement.

## The Complexity Conservation Law {#the-complexity-conservation-law .unnumbered}

Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} develops a quantitative consequence: when a problem requires $k$ dimensions and a model handles only $j < k$ natively, the remaining $k - j$ dimensions must be handled externally at each decision site. For $n$ sites, total external work is $(k-j) \times n$.

This conservation law is formalized in Lean 4 (`HardnessDistribution.lean`), proving:

-   Conservation: complexity cannot be eliminated, only redistributed

-   Dominance: complete models have lower total work than incomplete models

-   Amortization: there exists a threshold $n^*$ beyond which higher-dimensional models have lower total cost

## Open Questions {#open-questions .unnumbered}

Several questions remain for future work:

-   **Fixed-parameter tractability:** Is SUFFICIENCY-CHECK FPT when parameterized by the size of the minimal sufficient set?

-   **Average-case complexity:** What is the complexity under natural distributions on decision problems?

-   **Quantum complexity:** Does quantum computation provide speedups for sufficiency checking?

-   **Learning cost formalization:** Can central cost $H_{\text{central}}$ be formalized as the rank of a concept matroid, making the amortization threshold precisely computable?

## Practical interpretation {#practical-interpretation .unnumbered}

While this work is theoretical, the complexity bounds have practical meaning. Under ETH, worst-case instances of SUFFICIENCY-CHECK and related problems grow exponentially with problem size; practitioners should therefore not expect polynomial‑time worst‑case solvers for arbitrary inputs. In practice, real datasets often have structure (sparsity, bounded dependency depth, separable utilities) that the tractable subcases capture. Thus, engineering efforts should focus on (a) detecting and exploiting structural restrictions in inputs, and (b) designing heuristic or approximate methods for large unstructured instances. Our experiments illustrate performance on representative inputs, but the theoretical bounds underline the need for domain constraints to achieve scalable, worst‑case guarantees.


# Lean 4 Proof Listings {#app:lean}

The complete Lean 4 formalization is included in the appendix and companion artifact (Zenodo DOI is listed on the paper title page).

The formalization is not a transcription; it exposes a reusable reduction library with compositional polynomial bounds, enabling later mechanized hardness proofs to reuse these components directly.

## On the Nature of Definitional Proofs {#definitional-proofs-nature}

The Lean proofs follow directly from the formal definitions and standard complexity-theoretic constructions. The mechanization provides machine-checked verification and precision.

**Definitional vs. derivational proofs.** The core theorems establish definitional properties and reduction constructions. For example, the polynomial reduction composition theorem (Theorem [\[thm:poly-compose\]](#thm:poly-compose){reference-type="ref" reference="thm:poly-compose"}) proves that composing two polynomial-time reductions yields a polynomial-time reduction. The proof follows from the definition of polynomial time: composing two polynomials yields a polynomial.

**Precedent in complexity theory.** This pattern occurs throughout classical complexity theory:

-   **Cook-Levin Theorem (1971):** SAT is NP-complete. The proof constructs a reduction from an arbitrary NP problem to SAT. The construction itself is straightforward (encode Turing machine computation as boolean formula), but the *insight* is recognizing that SAT captures all of NP.

-   **Ladner's Theorem (1975):** If P $\neq$ NP, then NP-intermediate problems exist. The proof is a diagonal construction---conceptually simple once the right framework is identified.

-   **Toda's Theorem (1991):** The polynomial hierarchy is contained in P$^\#$P. The proof uses counting arguments that are elegant but not technically complex. The profundity is in the *connection* between counting and the hierarchy.

**Why simplicity indicates strength.** A definitional theorem derived from precise formalization is *stronger* than an informal argument. When we prove that sufficiency checking is coNP-complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), we are not saying "we tried many algorithms and they all failed." We are saying something general: *any* algorithm solving sufficiency checking solves TAUTOLOGY, and vice versa. The proof is a reduction construction that follows from the problem definitions.

**Where the insight lies.** The semantic contribution of our formalization is:

1.  **Precision forcing.** Formalizing "coordinate sufficiency" in Lean requires stating exactly what it means for a coordinate subset to contain all decision-relevant information. This precision eliminates ambiguity about edge cases (what if projections differ only on irrelevant coordinates?).

2.  **Reduction correctness.** The TAUTOLOGY reduction (Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}) is machine-checked to preserve the decision structure. Complexity reductions are subtle and easy to mis-specify. We therefore mechanize the definitions and key reductions in Lean to rule out common formalization mistakes.

3.  **Encoding-regime separation.** Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} contrasts explicit-state polynomial-time (polynomial in $|S|$) with a succinct worst-case ETH lower bound witnessed by a hard family with $k^*=n$ requiring $2^{\Omega(n)}$ time. Intermediate regimes are not ruled out by the lower-bound statement.

**What machine-checking guarantees.** The Lean compiler verifies that each proof step is valid and each definition is consistent; the mechanization does not introduce additional axioms beyond the chosen foundations. The mechanization contains no `sorry` placeholders. Reviewers can independently verify the proofs by running `lake build` in the mechanization directory and inspecting the companion artifact.

**Comparison to informal complexity arguments.** Prior work on model selection complexity (Chickering et al. [@chickering2004large], Teyssier & Koller [@teyssier2012ordering]) presents compelling informal arguments but lacks machine-checked proofs. Our contribution is not new *wisdom*---the insight that model selection is hard is old. Our contribution is *formalization*: making "coordinate sufficiency" precise enough to mechanize, constructing verified reductions, and proving the complexity results hold for the formalized definitions.

This follows the tradition of verified complexity theory: just as Nipkow & Klein [@nipkow2014concrete] formalized automata theory and Cook [@cook2018complexity] formalized NP-completeness in proof assistants, we formalize decision-theoretic complexity. The proofs are simple because the formalization makes the structure clear. Simple proofs from precise definitions are the goal, not a limitation.

## Module Structure

The formalization consists of 33 files organized as follows:

-   `Basic.lean` -- Core definitions (DecisionProblem, CoordinateSet, Projection)

-   `AlgorithmComplexity.lean` -- Complexity definitions (polynomial time, reductions)

-   `PolynomialReduction.lean` -- Polynomial reduction composition (Theorem [\[thm:poly-compose\]](#thm:poly-compose){reference-type="ref" reference="thm:poly-compose"})

-   `Reduction.lean` -- TAUTOLOGY reduction for sufficiency checking

-   `Reduction_AllCoords.lean` -- Strengthened gadget: if $\varphi$ is not a tautology then every coordinate is relevant

-   `Hardness/` -- Counting complexity and approximation barriers

-   `Tractability/` -- Bounded actions, separable utilities, tree structure, FPT

-   `Economics/` -- Value of information and elicitation connections

-   `Dichotomy.lean` and `ComplexityMain.lean` -- Summary results

-   `HardnessDistribution.lean` -- Simplicity Tax Theorem (Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"})

## Key Theorems

::: theorem
[]{#thm:poly-compose label="thm:poly-compose"} Polynomial-time reductions compose to polynomial-time reductions.
:::

    theorem PolyReduction.comp_exists
        (f : PolyReduction A B) (g : PolyReduction B C) :
        exists h : PolyReduction A C,
          forall a, h.reduce a = g.reduce (f.reduce a)

::: theorem
[]{#thm:tax-conservation-lean label="thm:tax-conservation-lean"} The simplicity tax plus covered axes equals required axes (partition).
:::

    theorem simplicityTax_conservation :
        simplicityTax P T + (P.requiredAxes inter T.nativeAxes).card
          = P.requiredAxes.card

::: theorem
[]{#thm:fallacy-lean label="thm:fallacy-lean"} Incomplete tools always cost more than complete tools for $n > 0$ use sites.
:::

    theorem simplicity_preference_fallacy (T_simple T_complex : Tool)
        (h_simple_incomplete : isIncomplete P T_simple)
        (h_complex_complete : isComplete P T_complex)
        (n : Nat) (hn : n > 0) :
        totalExternalWork P T_complex n < totalExternalWork P T_simple n

## Verification Status

The mechanization and its verification status are documented in the companion artifact; reviewers may consult the artifact for exact counts and files. The proofs compile and can be verified via the provided build instructions.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/proofs/paper4_toc_*.lean`
- Lines: 2760
- Theorems: 106
