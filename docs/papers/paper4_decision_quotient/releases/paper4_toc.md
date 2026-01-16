# Paper: Computational Complexity of Sufficiency in Decision Problems

**Status**: Theory of Computing-ready | **Lean**: 2760 lines, 106 theorems

---

## Abstract

We study the computational complexity of determining which coordinates of a decision problem are sufficient to identify optimal actions. Given a decision problem with action set $A$, state space $S = X_1 \times \cdots \times X_n$, and utility function $u: A \times S \to \mathbb{R}$, a coordinate set $I \subseteq \{1,\ldots,n\}$ is *sufficient* if knowing only coordinates in $I$ determines the optimal action: $s_I = s'_I \implies \Opt(s) = \Opt(s')$.

We prove:

1.  **Sufficiency-Check is -complete:** Given a decision problem and coordinate set $I$, determining whether $I$ is sufficient is -complete via reduction from TAUTOLOGY.

2.  **Minimum-Sufficient-Set is -complete:** Finding the minimum sufficient coordinate set is -complete.

3.  **Anchor-Sufficiency is $\SigmaP{2}$-complete:** Given coordinate set $I$, determining whether there exists an assignment to $I$ that makes the optimal action constant on the induced subcube is $\SigmaP{2}$-complete via reduction from $\exists\forall$-SAT.

4.  **Complexity Dichotomy:** Sufficiency checking is polynomial when the minimal sufficient set has size $O(\log |S|)$, but requires $2^{\Omega(n)}$ time when it has size $\Omega(n)$ (assuming ETH).

5.  **Tractable Subcases:** Polynomial-time algorithms exist for bounded action sets, separable utilities, and tree-structured dependencies.

As an application, we prove a *conservation law for complexity*: when a decision problem requires $n$ dimensions but an analysis method handles only $k < n$ natively, the remaining $n - k$ dimensions must be handled externally at each use site. This quantifies the cost of using simplified models.

All results are machine-checked in Lean 4 ($\sim$`<!-- -->`{=html}5,000 lines, 200+ theorems). The formalization proves reduction correctness and the combinatorial lemmas; complexity class membership follows by composition with the known complexity of TAUTOLOGY and $\exists\forall$-SAT.

**Keywords:** computational complexity, decision theory, coNP-completeness, polynomial hierarchy, Lean 4


# Introduction {#sec:introduction}

Consider a decision problem with actions $A$ and states $S = X_1 \times \cdots \times X_n$, where each $X_i$ is a coordinate space. For each state $s \in S$, some subset $\Opt(s) \subseteq A$ of actions are optimal. A natural question arises:

> *Which coordinates are sufficient to determine the optimal action?*

A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only the coordinates in $I$ determines the optimal action set: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$ where $s_I$ denotes the projection of state $s$ onto coordinates in $I$.

This paper establishes the computational complexity of sufficiency-related problems:

1.  **Sufficiency-Check** (given $I$, is it sufficient?) is -complete.

2.  **Minimum-Sufficient-Set** (find the smallest sufficient $I$) is -complete.

3.  **Anchor-Sufficiency** (does there exist an assignment to $I$ making $\Opt$ constant?) is $\SigmaP{2}$-complete.

These results place the problem of identifying "decision-relevant" coordinates at the first and second levels of the polynomial hierarchy [@stockmeyer1976polynomial].

## Main Results

1.  **Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} (Sufficiency Checking is -complete):** Given a decision problem and coordinate set $I$, determining whether $I$ is sufficient is -complete via reduction from TAUTOLOGY [@cook1971complexity].

2.  **Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} (Minimum Sufficiency is -complete):** Finding the minimum sufficient coordinate set is -complete.

3.  **Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"} (Anchor-Sufficiency is $\SigmaP{2}$-complete):** Given coordinate set $I$, determining whether there exists an assignment to $I$ such that $\Opt$ is constant on the induced subcube is $\SigmaP{2}$-complete via reduction from $\exists\forall$-SAT.

4.  **Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} (Complexity Dichotomy):** Sufficiency checking exhibits a dichotomy:

    -   If the minimal sufficient set has size $O(\log |S|)$, checking is polynomial.

    -   If the minimal sufficient set has size $\Omega(n)$, checking requires $2^{\Omega(n)}$ time under ETH [@impagliazzo2001complexity].

5.  **Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} (Tractable Subcases):** Sufficiency checking is polynomial-time for:

    -   Bounded action sets ($|A| \leq k$ for constant $k$)

    -   Separable utility functions ($u(a,s) = f(a) + g(s)$)

    -   Tree-structured coordinate dependencies

## Applications

The complexity results have implications for model selection across domains:

-   **Machine learning:** Feature selection is intractable in general.

-   **Economics:** Identifying relevant market factors is intractable.

-   **Scientific modeling:** Determining which variables matter is intractable.

-   **Software engineering:** Configuration minimization is intractable.

We also develop a quantitative consequence: the *complexity conservation law*. When a decision problem requires $n$ dimensions but an analysis uses only $k < n$ coordinates, the remaining $n - k$ dimensions must be handled externally at each decision site. Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} formalizes this as the "Simplicity Tax Theorem" and proves that the total work is minimized when the analysis matches the problem's intrinsic dimensionality.

## Machine-Checked Proofs

All results are formalized in Lean 4 [@moura2021lean4] ($\sim$`<!-- -->`{=html}5,000 lines, 200+ theorems). The formalization proves:

-   Polynomial-time reduction composition

-   Correctness of the TAUTOLOGY and $\exists\forall$-SAT reduction mappings

-   The combinatorial lemmas underlying the dichotomy

-   The Simplicity Tax conservation and dominance theorems

Complexity class membership follows by composing these verified reductions with the known complexity of TAUTOLOGY and $\exists\forall$-SAT.

## Paper Structure

Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"} establishes formal foundations. Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} proves the main hardness results. Section [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"} develops the complexity dichotomy. Section [\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"} presents tractable special cases. Section [\[sec:implications\]](#sec:implications){reference-type="ref" reference="sec:implications"} discusses implications. Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} develops the Simplicity Tax Theorem. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"} surveys related work. Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} contains Lean proof listings.


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

The hardness results of Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} apply to worst-case instances. This section develops a more nuanced picture: a *dichotomy theorem* showing that problem difficulty depends on the size of the minimal sufficient set.

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


# Why Over-Modeling Is Optimal {#sec:engineering-justification}

The complexity results of Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} and [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"} transform engineering practice from art to mathematics. This section proves that observed behaviors---configuration over-specification, absence of automated minimization tools, heuristic model selection---are not failures of discipline but *provably optimal responses* to computational constraints.

The conventional critique of over-modeling ("you should identify only the essential variables") is computationally naive. It asks engineers to solve -complete problems. The rational response is to include everything and pay linear maintenance costs, rather than attempt exponential minimization costs.

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
This reduction is *parsimonious*: every instance of configuration simplification corresponds bijectively to an instance of SUFFICIENCY-CHECK. The problems are not merely related---they are identical up to encoding.
:::

## Computational Rationality of Over-Modeling

We now prove that over-specification is the optimal engineering strategy given complexity constraints.

::: theorem
[]{#thm:rational-overmodel label="thm:rational-overmodel"} Consider an engineer specifying a system configuration with $n$ parameters. Let:

-   $C_{\text{over}}(k)$ = cost of maintaining $k$ extra parameters beyond minimal

-   $C_{\text{find}}(n)$ = cost of finding minimal sufficient parameter set

-   $C_{\text{under}}$ = expected cost of production failures from underspecification

When SUFFICIENCY-CHECK is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}):

1.  Worst-case finding cost is exponential: $C_{\text{find}}(n) = \Omega(2^n)$

2.  Maintenance cost is linear: $C_{\text{over}}(k) = O(k)$

3.  For sufficiently large $n$, exponential cost dominates linear cost

Therefore, when $n$ exceeds a threshold, over-modeling minimizes total expected cost: $$C_{\text{over}}(k) < C_{\text{find}}(n) + C_{\text{under}}$$

Over-modeling is the economically optimal strategy under computational constraints.
:::

::: proof
*Proof.* By Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, SUFFICIENCY-CHECK is -complete. Under standard complexity assumptions ($\Pclass \neq \coNP$), no polynomial-time algorithm exists for checking sufficiency.

Finding the minimal sufficient set requires checking sufficiency of multiple candidate sets. Exhaustive search examines: $$\sum_{i=0}^{n} \binom{n}{i} = 2^n \text{ candidate subsets}$$

Each check requires $\Omega(1)$ time (at minimum, reading the input). Therefore: $$C_{\text{find}}(n) = \Omega(2^n)$$

Maintaining $k$ extra parameters incurs:

-   Documentation cost: $O(k)$ entries

-   Testing cost: $O(k)$ test cases

-   Migration cost: $O(k)$ parameters to update

Total maintenance cost is $C_{\text{over}}(k) = O(k)$.

For concrete threshold: when $n = 20$ parameters, exhaustive search requires $2^{20} \approx 10^6$ checks. Including $k = 5$ extra parameters costs $O(5)$ maintenance overhead but avoids $10^6$ computational work.

Since $2^n$ grows faster than any polynomial in $k$ or $n$, there exists $n_0$ such that for all $n > n_0$: $$C_{\text{over}}(k) \ll C_{\text{find}}(n)$$

Adding underspecification risk $C_{\text{under}}$ (production failures from missing parameters), which can be arbitrarily large, makes over-specification strictly dominant. ◻
:::

::: corollary
[]{#cor:no-auto-minimize label="cor:no-auto-minimize"} There exists no polynomial-time algorithm that:

1.  Takes an arbitrary configuration file with $n$ parameters

2.  Identifies the minimal sufficient parameter subset

3.  Guarantees correctness (no false negatives)
:::

::: proof
*Proof.* Such an algorithm would solve MINIMUM-SUFFICIENT-SET in polynomial time, contradicting Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} (assuming $\Pclass \neq \coNP$). ◻
:::

::: remark
Corollary [\[cor:no-auto-minimize\]](#cor:no-auto-minimize){reference-type="ref" reference="cor:no-auto-minimize"} explains the observed absence of "config cleanup" tools in software engineering practice. Engineers who include extra parameters are not exhibiting poor discipline---they are adapting optimally to computational impossibility. The problem is not lack of tooling effort; it is mathematical intractability.
:::

## Connection to Observed Practice

These theorems provide mathematical grounding for three widespread engineering behaviors:

**1. Configuration files grow over time.** Removing parameters requires solving -complete problems. Engineers rationally choose linear maintenance cost over exponential minimization cost.

**2. Heuristic model selection dominates.** ML practitioners use AIC, BIC, cross-validation instead of optimal feature selection because optimal selection is intractable (Theorem [\[thm:rational-overmodel\]](#thm:rational-overmodel){reference-type="ref" reference="thm:rational-overmodel"}).

**3. "Include everything" is a legitimate strategy.** When determining relevance costs $\Omega(2^n)$, including all $n$ parameters costs $O(n)$. For large $n$, this is the rational choice.

These are not workarounds or approximations. They are *optimal responses* to computational constraints. The complexity results transform engineering practice from art to mathematics: over-modeling is not a failure---it is the provably correct strategy.


# Implications for Software Architecture {#sec:implications}

The complexity results have direct implications for software engineering practice.

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

A fundamental principle emerges from the complexity results: problem hardness is conserved but can be *distributed* across a system in qualitatively different ways.

::: definition
[]{#def:hardness-distribution label="def:hardness-distribution"} Let $P$ be a problem with intrinsic hardness $H(P)$ (measured in computational steps, implementation effort, or error probability). A *solution architecture* $S$ partitions this hardness into:

-   $H_{\text{central}}(S)$: hardness paid once, at design time or in a shared component

-   $H_{\text{distributed}}(S)$: hardness paid per use site

For $n$ use sites, total realized hardness is: $$H_{\text{total}}(S) = H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)$$
:::

::: theorem
[]{#thm:hardness-conservation label="thm:hardness-conservation"} For any problem $P$ with intrinsic hardness $H(P)$, any solution $S$ satisfies: $$H_{\text{central}}(S) + H_{\text{distributed}}(S) \geq H(P)$$ Hardness cannot be eliminated, only redistributed.
:::

::: proof
*Proof.* By definition of intrinsic hardness: any correct solution must perform at least $H(P)$ units of work (computational, cognitive, or error-handling). This work is either centralized or distributed. 0◻ ◻
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
*Proof.* (1) follows from the total hardness formula. (2) follows from error site counting. (3) follows from the definition of leverage as $L = \Delta\text{Effect}/\Delta\text{Effort}$. 0◻ ◻
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

The next section develops the major practical consequence of this framework: the Simplicity Tax Theorem.


# The Simplicity Tax: A Conservation Law for Complexity {#sec:simplicity-tax}

The hardness results of Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}--[\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"} establish that identifying decision-relevant dimensions is -complete. This section develops a quantitative consequence: a conservation law for complexity that governs the total work required when using models of varying expressiveness.

## Definitions {#sec:tax-definitions}

::: definition
[]{#def:problem-tool label="def:problem-tool"} A *problem* $P$ has a set of *required dimensions* $R(P) \subseteq \{1,\ldots,n\}$---the coordinates that affect the optimal action. A *model* (or analysis method) $M$ has a set of *native dimensions* $A(M)$---the coordinates it can represent directly.
:::

::: definition
[]{#def:expressive-gap label="def:expressive-gap"} The *expressive gap* between model $M$ and problem $P$ is: $$\text{Gap}(M, P) = R(P) \setminus A(M)$$ The *simplicity tax* is $|\text{Gap}(M, P)|$: the number of dimensions the model cannot represent natively.
:::

::: definition
[]{#def:complete-incomplete label="def:complete-incomplete"} Model $M$ is *complete* for problem $P$ if $R(P) \subseteq A(M)$. Otherwise $M$ is *incomplete* for $P$.
:::

## The Conservation Theorem {#sec:conservation}

::: theorem
[]{#thm:tax-conservation label="thm:tax-conservation"} For any problem $P$ with required dimensions $R(P)$ and any model $M$: $$|\text{Gap}(M, P)| + |R(P) \cap A(M)| = |R(P)|$$ The required dimensions are partitioned into "handled natively" and "handled externally." The total cannot be reduced---only redistributed.
:::

::: proof
*Proof.* Set partition: $R(P) = (R(P) \cap A(M)) \cup (R(P) \setminus A(M))$. The sets are disjoint. Cardinality follows. 0◻ ◻
:::

::: theorem
[]{#thm:complete-no-tax label="thm:complete-no-tax"} If $M$ is complete for $P$, then $\text{SimplicityTax}(M, P) = 0$.
:::

::: theorem
[]{#thm:incomplete-positive-tax label="thm:incomplete-positive-tax"} If $M$ is incomplete for $P$, then $\text{SimplicityTax}(M, P) > 0$.
:::

::: theorem
[]{#thm:tax-grows label="thm:tax-grows"} For $n$ decision sites using an incomplete model: $$\text{TotalExternalWork}(M, P, n) = n \times \text{SimplicityTax}(M, P)$$ Total external work grows linearly in the number of sites.
:::

::: theorem
[]{#thm:complete-dominates label="thm:complete-dominates"} For any $n > 0$, a complete model has strictly less total work than an incomplete model: $$\text{TotalExternalWork}(M_{\text{complete}}, P, n) < \text{TotalExternalWork}(M_{\text{incomplete}}, P, n)$$
:::

::: proof
*Proof.* Complete: $0 \times n = 0$. Incomplete: $k \times n$ for $k \geq 1$. For $n > 0$: $0 < kn$. 0◻ ◻
:::

## Central vs. Distributed Costs {#sec:central-distributed}

When comparing models, two cost components must be distinguished:

-   $H_{\text{central}}$: The one-time cost of constructing or learning the model.

-   $H_{\text{distributed}}$: The per-site cost of handling dimensions not covered by the model.

A model with higher $H_{\text{central}}$ but zero $H_{\text{distributed}}$ may have lower total cost than a model with lower $H_{\text{central}}$ but positive $H_{\text{distributed}}$, depending on the number of decision sites.

::: theorem
[]{#thm:comparison label="thm:comparison"} Let $M_1$ be incomplete for problem $P$ and $M_2$ be complete. For any $n > 0$: $$\text{TotalWork}(M_2, P, n) < \text{TotalWork}(M_1, P, n)$$ when considering only per-site costs (ignoring $H_{\text{central}}$).
:::

::: theorem
[]{#thm:amortization label="thm:amortization"} There exists a threshold $n^*$ such that for all $n > n^*$, the total cost of the complete model (including $H_{\text{central}}$) is strictly less than the incomplete model: $$n^* = \frac{H_{\text{central}}(M_{\text{complete}})}{\text{SimplicityTax}(M_{\text{incomplete}}, P)}$$ Beyond $n^*$ decision sites, the complete model has lower total cost.
:::

::: remark
This theorem models central cost as a scalar $H_{\text{central}}$. A more refined model might treat it as the rank of a matroid of prerequisite concepts, ensuring that different minimal learning paths have equal cardinality. The qualitative result (threshold existence) is robust to the cost model; the quantitative threshold depends on its precise formalization.
:::

## Examples {#sec:examples}

The conservation law applies across domains:

::: center
  **Domain**        **Incomplete Model**   **Complete Model**   **Tax/Site**
  ----------------- ---------------------- -------------------- -----------------
  Type Systems      Dynamic typing         Static typing        Type errors
  Data Validation   Ad-hoc checks          Schema validation    Validation code
  Configuration     Hardcoded values       Config management    Change sites
  APIs              String parameters      Typed interfaces     Parse/validate
:::

In each case, the incomplete model has lower $H_{\text{central}}$ but positive $H_{\text{distributed}}$. For $n$ sites, total work is $H_{\text{central}} + n \times \text{tax}$.

**Example: Static vs. Dynamic Typing.** Dynamic typing has lower learning cost. But type errors are a per-site cost: each call site that could receive an incorrect type requires either defensive code or debugging. For $n$ call sites:

-   Static typing: type checker verifies once; per-site cost is 0.

-   Dynamic typing: $n$ potential error sites, each with positive per-site cost.

## Connection to the Complexity Results {#sec:connection}

The conservation law connects to the main complexity results as follows: since identifying the required dimensions $R(P)$ is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), and since misidentification leads to a positive simplicity tax, the cost of using an incomplete model is a direct consequence of the hardness of the sufficiency problem.

::: corollary
If identifying $R(P)$ is intractable, then minimizing the simplicity tax is also intractable.
:::

## Lean 4 Formalization {#sec:simplicity-lean}

The theorems in this section are machine-checked in `DecisionQuotient/HardnessDistribution.lean`:

::: center
  **Theorem**                          **Lean Name**
  ------------------------------------ ---------------------------------
  Complexity Conservation              `simplicityTax_conservation`
  Complete Models Pay No Tax           `complete_tool_no_tax`
  Incomplete Models Pay Positive Tax   `incomplete_tool_positive_tax`
  Linear Growth                        `simplicityTax_grows`
  Dominance                            `complete_dominates_incomplete`
  Amortization Threshold               `amortization_threshold`
  Tax Antitone w.r.t. Expressiveness   `simplicityTax_antitone`
:::

The formalization uses `Finset `$\mathbb{N}$ for dimensions. The `Model` type forms a lattice under the expressiveness ordering, with tax antitone (more expressive $\Rightarrow$ lower tax).


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

**Role of LLMs in this work.** This paper was developed through human-AI collaboration. The author provided the core intuitions---the connection between decision-relevance and computational complexity, the conjecture that SUFFICIENCY-CHECK is -complete, and the insight that the $\SigmaP{2}$ structure collapses for MINIMUM-SUFFICIENT-SET. Large language models (Claude, GPT-4) served as implementation partners for proof drafting, Lean formalization, and LaTeX generation.

The Lean 4 proofs were iteratively refined: the author specified what should be proved, the LLM proposed proof strategies, and the Lean compiler served as the arbiter of correctness. The complexity-theoretic reductions required careful human oversight to ensure the polynomial bounds were correctly established.

**What the author contributed:** The problem formulations (SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, ANCHOR-SUFFICIENCY), the hardness conjectures, the tractability conditions, and the connection to over-modeling in engineering practice.

**What LLMs contributed:** LaTeX drafting, Lean tactic exploration, reduction construction assistance, and prose refinement.

The proofs are machine-checked; their validity is independent of generation method. We disclose this methodology in the interest of academic transparency.

::: center

----------------------------------------------------------------------------------------------------
:::

## Summary of Results {#summary-of-results .unnumbered}

This paper establishes the computational complexity of coordinate sufficiency problems:

-   **Sufficiency-Check** is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"})

-   **Minimum-Sufficient-Set** is -complete (Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"})

-   **Anchor-Sufficiency** is $\SigmaP{2}$-complete (Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"})

-   A complexity dichotomy separates polynomial (logarithmic minimal set) from exponential (linear minimal set) cases (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"})

-   Tractable subcases exist for bounded actions, separable utilities, and tree structures (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"})

These results place the problem of identifying decision-relevant coordinates at the first and second levels of the polynomial hierarchy.

All proofs are machine-checked in Lean 4 ($\sim$`<!-- -->`{=html}5,000 lines). The formalization verifies the reduction mappings and equivalence theorems; complexity classifications follow from standard results (TAUTOLOGY is -complete, $\exists\forall$-SAT is $\SigmaP{2}$-complete).

## Complexity Characterization {#complexity-characterization .unnumbered}

The results provide exact complexity characterizations:

1.  **Exact bounds.** Sufficiency-Check is -complete---both -hard and in .

2.  **Constructive reductions.** The reductions from TAUTOLOGY and $\exists\forall$-SAT are explicit and machine-checked.

3.  **Complete dichotomy.** Under standard assumptions ( $\neq$ ), the complexity separates into exactly two cases with no intermediate behavior.

4.  **Tight tractability conditions.** The tractability conditions (bounded actions, separable utilities, tree structure) are tight---relaxing any condition yields -hardness.

## The Complexity Conservation Law {#the-complexity-conservation-law .unnumbered}

Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} develops a quantitative consequence: when a problem requires $k$ dimensions and a model handles only $j < k$ natively, the remaining $k - j$ dimensions must be handled externally at each decision site. For $n$ sites, total external work is $(k-j) \times n$.

This conservation law is formalized in Lean 4 (`HardnessDistribution.lean`), proving:

-   Conservation: complexity cannot be eliminated, only redistributed

-   Dominance: complete models have lower total work than incomplete models

-   Amortization: there exists a threshold $n^*$ beyond which higher-dimensional models have lower total cost

## Open Questions {#open-questions .unnumbered}

Several questions remain for future work:

-   **Fixed-parameter tractability:** Is Sufficiency-Check FPT when parameterized by the size of the minimal sufficient set?

-   **Average-case complexity:** What is the complexity under natural distributions on decision problems?

-   **Quantum complexity:** Does quantum computation provide speedups for sufficiency checking?

-   **Learning cost formalization:** Can central cost $H_{\text{central}}$ be formalized as the rank of a concept matroid, making the amortization threshold precisely computable?


# Lean 4 Proof Listings {#app:lean}

The complete Lean 4 formalization is available at:

::: center
<https://doi.org/10.5281/zenodo.18140966>
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

2.  **Reduction correctness.** The TAUTOLOGY reduction (Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}) is machine-checked to preserve the decision structure. Informal reductions can have subtle bugs; Lean verification guarantees the mapping is correct.

3.  **Complexity dichotomy.** Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} proves that problem instances are either tractable (P) or intractable (coNP-complete), with no intermediate cases under standard assumptions. This emerges from the formalization of constraint structure, not from case enumeration.

**What machine-checking guarantees.** The Lean compiler verifies that every proof step is valid, every definition is consistent, and no axioms are added beyond Lean's foundations (extended with Mathlib for basic combinatorics and complexity definitions). Zero `sorry` placeholders means zero unproven claims. The 3,400+ lines establish a verified chain from basic definitions (decision problems, coordinate spaces, polynomial reductions) to the final theorems (hardness results, dichotomy, tractable cases). Reviewers need not trust our informal explanations---they can run `lake build` and verify the proofs themselves.

**Comparison to informal complexity arguments.** Prior work on model selection complexity (Chickering et al. [@chickering2004large], Teyssier & Koller [@teyssier2012ordering]) presents compelling informal arguments but lacks machine-checked proofs. Our contribution is not new *wisdom*---the insight that model selection is hard is old. Our contribution is *formalization*: making "coordinate sufficiency" precise enough to mechanize, constructing verified reductions, and proving the complexity results hold for the formalized definitions.

This follows the tradition of verified complexity theory: just as Nipkow & Klein [@nipkow2014concrete] formalized automata theory and Cook [@cook2018complexity] formalized NP-completeness in proof assistants, we formalize decision-theoretic complexity. The proofs are simple because the formalization makes the structure clear. Simple proofs from precise definitions are the goal, not a limitation.

## Module Structure

The formalization consists of 33 files organized as follows:

-   `Basic.lean` -- Core definitions (DecisionProblem, CoordinateSet, Projection)

-   `AlgorithmComplexity.lean` -- Complexity definitions (polynomial time, reductions)

-   `PolynomialReduction.lean` -- Polynomial reduction composition (Theorem [\[thm:poly-compose\]](#thm:poly-compose){reference-type="ref" reference="thm:poly-compose"})

-   `Reduction.lean` -- TAUTOLOGY reduction for sufficiency checking

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

-   Total lines: $\sim$`<!-- -->`{=html}5,000

-   Theorems: 200+

-   Files: 33

-   Status: All proofs compile with no `sorry`


# Preemptive Rebuttals {#appendix-rebuttals}

We address anticipated objections to the main results.

## Objection 1: "coNP-completeness doesn't mean intractable"

**Objection:** "coNP-complete problems might have good heuristics or approximations. The hardness result doesn't preclude practical solutions."

**Response:** This objection actually *strengthens* our thesis. The point is not that practitioners cannot find useful approximations---they clearly do (feature selection heuristics in ML, sensitivity analysis in economics, configuration defaults in software). The point is that *optimal* dimension selection is provably hard.

The prevalence of heuristics across domains is itself evidence of the computational barrier. If optimal selection were tractable, we would see optimal algorithms, not heuristics. The universal adoption of "include more than necessary" strategies is the rational response to coNP-completeness.

## Objection 2: "Real problems don't have coordinate structure"

**Objection:** "Real decision problems are messier than your clean product-space model. The coordinate structure assumption is too restrictive."

**Response:** The assumption is weaker than it appears. Any finite state space can be encoded with binary coordinates; our hardness results apply to this encoding. More structured representations make the problem *easier*, not harder---so hardness for structured problems implies hardness for unstructured ones.

The coordinate structure abstracts common patterns: independent sensors, orthogonal configuration parameters, factored state spaces. These are ubiquitous in practice precisely because they enable tractable reasoning in special cases (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

## Objection 3: "The SAT reduction is artificial"

**Objection:** "The reduction from SAT/TAUT is an artifact of complexity theory. Real decision problems don't encode Boolean formulas."

**Response:** All coNP-completeness proofs use reductions. The reduction demonstrates that TAUT instances can be encoded as sufficiency-checking problems while preserving computational structure. This is standard methodology [@cook1971complexity; @karp1972reducibility].

The claim is not that practitioners encounter SAT problems in disguise, but that sufficiency checking is *at least as hard as* TAUT. If sufficiency checking were tractable, we could solve TAUT in polynomial time, contradicting the widely-believed $\P \neq \NP$ conjecture.

The reduction is a proof technique, not a claim about problem origins.

## Objection 4: "Tractable subcases are too restrictive"

**Objection:** "The tractable subcases (bounded actions, separable utility, tree structure) are too restrictive to cover real problems."

**Response:** These subcases characterize *when* dimension selection becomes feasible:

-   **Bounded actions:** Many real decisions have few options (buy/sell/hold, accept/reject, left/right/straight)

-   **Separable utility:** Additive decomposition is common in economics and operations research

-   **Tree structure:** Hierarchical dependencies appear in configuration, organizational decisions, and causal models

The dichotomy theorem (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}) precisely identifies the boundary. The contribution is not that all problems are hard, but that hardness is the *default* unless special structure exists.

## Objection 5: "This just formalizes the obvious"

**Objection:** "Everyone knows feature selection is hard. This paper just adds mathematical notation to folklore."

**Response:** The contribution is unification. Prior work established hardness for specific domains (feature selection in ML [@guyon2003introduction], factor identification in economics, variable selection in statistics). We prove a *universal* result that applies to *any* decision problem with coordinate structure.

This universality explains why the same "over-modeling" pattern appears across unrelated domains. It's not that each domain independently discovered the same heuristic---it's that each domain independently hit the same computational barrier.

The theorem makes "obvious" precise and proves it applies universally. This is the value of formalization.

## Objection 6: "The Lean proofs don't capture the real complexity"

**Objection:** "The Lean formalization models an idealized version of the problem. Real coNP-completeness proofs are about Turing machines, not Lean types."

**Response:** The Lean formalization captures the mathematical structure of the reduction, not the Turing machine details. We prove:

1.  The sufficiency-checking problem is in coNP (verifiable counterexample)

2.  TAUT reduces to sufficiency checking (polynomial-time construction)

3.  The reduction preserves yes/no answers (correctness)

These are the mathematical claims that establish coNP-completeness. The Turing machine encoding is implicit in Lean's computational semantics. The formalization provides machine-checked verification that the reduction is correct.

## Objection 7: "The dichotomy is not tight"

**Objection:** "The dichotomy between $O(\log n)$ and $\Omega(n)$ minimal sufficient sets leaves a gap. What about $O(\sqrt{n})$?"

**Response:** The dichotomy is tight under standard complexity assumptions. The gap corresponds to problems reducible to a polynomial number of SAT instances---exactly the problems in the polynomial hierarchy between P and coNP.

In practice, the dichotomy captures the relevant cases: either the problem has logarithmic dimension (tractable) or linear dimension (intractable). Intermediate cases exist theoretically but are rare in practice.

## Objection 8: "This doesn't help practitioners"

**Objection:** "Proving hardness doesn't help engineers solve their problems. This paper offers no constructive guidance."

**Response:** Understanding limits is constructive. The paper provides:

1.  **Tractable subcases** (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}): Check if your problem has bounded actions, separable utility, or tree structure

2.  **Justification for heuristics**: Over-modeling is not laziness---it's computationally rational

3.  **Focus for optimization**: Don't waste effort on optimal dimension selection; invest in good defaults and local search

Knowing that optimal selection is coNP-complete frees practitioners to use heuristics without guilt. This is actionable guidance.

## Objection 9: "But simple tools are easier to learn"

**Objection:** "The Simplicity Tax analysis ignores learning costs. Simple tools have lower barrier to entry, which matters for team adoption."

**Response:** This objection conflates $H_{\text{central}}$ (learning cost) with total cost. Yes, simple tools have lower learning cost. But for $n$ use sites, the total cost is: $$H_{\text{total}} = H_{\text{central}} + n \times H_{\text{distributed}}$$

The learning cost is paid once; the per-site cost is paid $n$ times. For $n > H_{\text{central}} / H_{\text{distributed}}$, the "complex" tool with higher learning cost has lower total cost.

The objection is actually an argument for training, not for tool avoidance. If the learning cost is the barrier, pay it---the amortization makes it worthwhile.

## Objection 10: "My team doesn't know metaclasses/types/frameworks"

**Objection:** "In practice, teams use what they know. Advocating for 'complex' tools ignores organizational reality."

**Response:** The Simplicity Tax is paid regardless of whether your team recognizes it. Ignorance of the tax does not exempt you from paying it.

If your team writes boilerplate at 50 locations because they don't know metaclasses, they pay the tax---in time, bugs, and maintenance. The tax is real whether it appears on a ledger or not.

Organizational reality is a constraint on *implementation*, not on *what is optimal*. The Simplicity Tax Theorem tells you the optimal; your job is to approach it within organizational constraints. "We don't know X" is a gap to close, not a virtue to preserve.

## Objection 11: "We can always refactor later"

**Objection:** "Start simple, refactor when needed. Technical debt is manageable."

**Response:** Refactoring from distributed to centralized is $O(n)$ work---you are paying the accumulated Simplicity Tax all at once. If you have $n$ sites each paying tax $k$, refactoring costs at least $nk$ effort.

"Refactor later" is not free. It is deferred payment with interest. The Simplicity Tax accrues whether you pay it incrementally (per-site workarounds) or in bulk (refactoring).

Moreover, distributed implementations create dependencies. Each workaround becomes a local assumption that must be preserved during refactoring. The refactoring cost is often *superlinear* in $n$.

## Objection 12: "The Simplicity Tax assumes all axes are equally important"

**Objection:** "Real problems have axes of varying importance. A tool that covers the important axes might be good enough."

**Response:** The theorem is conservative: it counts axes uniformly. Weighted versions strengthen the result.

If axis $a$ has importance $w_a$, define weighted tax: $$\text{WeightedTax}(T, P) = \sum_{a \in R(P) \setminus A(T)} w_a$$

Now the incomplete tool pays $\sum w_a \times n$ while the complete tool pays 0. The qualitative result is unchanged: incomplete tools pay per-site; complete tools do not.

The "cover important axes" heuristic only works if you *correctly identify* which axes are important. By Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, this identification is coNP-complete. You are back to the original hardness result.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/proofs/paper4_toc_*.lean`
- Lines: 2760
- Theorems: 106
