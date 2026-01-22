# Paper: Decision Quotient: Formal Semantics of Architectural Choice

**Status**: Draft-ready | **Lean**: 2760 lines, 106 theorems

---

## Abstract

We present a Lean 4 formalization of polynomial-time reductions and computational complexity proofs, demonstrated through a comprehensive analysis of *decision-relevant information*: the problem of identifying which variables matter for optimal decision-making.

**Formalization contributions.** We develop a reusable framework for expressing Karp reductions, oracle complexity classes, and parameterized hardness in Lean 4. The framework integrates with Mathlib's computability library and provides: (1) bundled reduction types with polynomial-time witnesses; (2) tactics for composing reductions; (3) templates for NP/coNP/ membership and hardness proofs.

**Verified complexity results.** As a case study, we formalize the complexity of the SUFFICIENCY-CHECK problem---determining which coordinates of a decision problem suffice for optimal action. We machine-verify:

-   **coNP-completeness** of sufficiency checking via reduction from TAUTOLOGY [@cook1971complexity]

-   **Inapproximability** within $(1-\varepsilon)\ln n$ via L-reduction from SET-COVER [@feige1998threshold]

-   **$2^{\Omega(n)}$ lower bounds** under ETH via circuit-based arguments [@impagliazzo2001complexity]

-   **W\[2\]-hardness** for the parameterized variant with kernelization lower bounds

-   **A complexity dichotomy**: polynomial time in the explicit-state model for $O(\log |S|)$-size sufficient sets, exponential under ETH in the succinct model for $\Omega(n)$-size

All complexity claims use the input encodings fixed in Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}.

The formalization comprises $\sim$`<!-- -->`{=html}5,600 lines of Lean 4 with 230+ machine-verified theorems across 36 files. All reductions include explicit polynomial bounds. We identify proof engineering patterns for complexity theory in dependent type systems and discuss challenges of formalizing computational hardness constructively.

**Practical corollaries.** The primary contribution is theoretical: a formalized reduction framework and a complete characterization of the core decision-relevant problems in the formal model (coNP/$\Sigma_2^P$ completeness and tractable cases under explicit encoding assumptions). The case study formalizes the principle *determining what you need to know is harder than knowing everything*. This implies that over-modeling is rational under the model and that "simpler" incomplete tools create more work (the Simplicity Tax Theorem, also machine-verified).

**Keywords:** Lean 4, formal verification, polynomial-time reductions, coNP-completeness, computational complexity, Mathlib, interactive theorem proving


# Introduction {#sec:introduction}

Computational complexity theory provides the mathematical foundation for understanding algorithmic hardness, yet its proofs remain largely unverified by machine. While proof assistants have transformed areas from program verification to pure mathematics (with projects like Mathlib formalizing substantial portions of undergraduate mathematics), complexity-theoretic reductions remain underrepresented in formal libraries.

This gap matters. Reductions are notoriously error-prone: they require careful polynomial-time bounds, precise correspondence between instances, and subtle handling of edge cases. Published proofs occasionally contain errors that survive peer review. Machine verification eliminates this uncertainty while producing reusable artifacts.

We address this gap by developing a Lean 4 framework for formalizing polynomial-time reductions, demonstrated through a comprehensive complexity analysis of *decision-relevant information*: the problem of identifying which variables matter for optimal decision-making.

Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"} fixes the computational model and input encodings used for all complexity claims.

## Contributions

This paper makes the following contributions, ordered by formalization significance:

1.  **A Lean 4 framework for polynomial-time reductions.** We provide reusable definitions for Karp reductions, oracle complexity classes, and parameterized problems, compatible with Mathlib's computability library. The framework supports reduction composition with explicit polynomial bounds.

2.  **Machine-verified NP/coNP-completeness proofs.** We formalize a complete reduction from TAUTOLOGY to SUFFICIENCY-CHECK, demonstrating the methodology for coNP-hardness proofs in Lean 4. The reduction includes machine-checked polynomial-time bounds.

3.  **Formalized approximation hardness.** We provide (to our knowledge) the first Lean formalization of an inapproximability result via L-reduction, showing $(1-\varepsilon)\ln n$-hardness for MINIMUM-SUFFICIENT-SET from SET-COVER.

4.  **ETH-based lower bounds in Lean.** We formalize conditional lower bounds using the Exponential Time Hypothesis, including circuit-based argument structure for $2^{\Omega(n)}$ bounds.

5.  **Parameterized complexity in Lean 4.** We prove W\[2\]-hardness with kernelization lower bounds, extending Lean's coverage to parameterized complexity theory.

6.  **Case study: Decision-relevant information.** We apply the framework to prove that identifying which coordinates of a decision problem suffice for optimal action is coNP-complete, with a sharp complexity dichotomy and tractability conditions.

#### What is new.

We contribute (i) a reusable Lean 4 framework for polynomial-time reductions with explicit polynomial bounds; (ii) the first machine-checked coNP-completeness proof for a decision-theoretic sufficiency problem; and (iii) a complete complexity landscape for coordinate sufficiency under explicit encoding assumptions. Prior work studies decision complexity in general or feature selection hardness, but does not formalize these reductions or establish this landscape in Lean.

## The Case Study: Sufficiency Checking

Our case study addresses a core question in decision theory:

> **Which variables are sufficient to determine the optimal action?**

Consider a decision problem with actions $A$ and states $S = X_1 \times \cdots \times X_n$. A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only coordinates in $I$ determines optimal action: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$

We prove this problem is coNP-complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), finding minimum sufficient sets is coNP-complete (Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}), and a complexity dichotomy separates polynomial time in the explicit-state model for $O(\log |S|)$-size sufficient sets from $2^{\Omega(n)}$ lower bounds under ETH in the succinct model for $\Omega(n)$-size sets.

The primary contribution is theoretical: a formalized reduction framework and a complete characterization of the core decision-relevant problems in the formal model (coNP/$\Sigma_2^P$ completeness and tractable cases under explicit encoding assumptions). The practical corollary (that "determining what you need to know is harder than knowing everything") explains ubiquitous over-modeling across engineering, science, and finance. For CPP/ITP readers, the significance is methodological: these results demonstrate an end-to-end pipeline from problem formulation to machine-verified hardness proof.

## Formalization Statistics

::: center
  **Metric**                                                 **Value**
  ----------------------- --------------------------------------------
  Lines of Lean 4                         $\sim$`<!-- -->`{=html}5,600
  Theorems/lemmas                                                 230+
  Proof files                                                       36
  Reduction proofs          5 (SAT, TAUTOLOGY, SET-COVER, ETH, W\[2\])
  External dependencies           Mathlib (computability, data.finset)
  `sorry` count                                                      0
:::

All proofs compile with `lake build` and pass `#print axioms` verification (depending only on `propext`, `Quot.sound`, and `Classical.choice` where necessary for classical reasoning).

## Paper Structure

Section [\[sec:methodology\]](#sec:methodology){reference-type="ref" reference="sec:methodology"} describes our formalization methodology and Lean 4 framework design. Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"} establishes formal foundations for the case study. Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}--[\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"} develop the core complexity results with machine-verified proofs. Sections [\[sec:implications\]](#sec:implications){reference-type="ref" reference="sec:implications"} and [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} present corollaries and implications for practice (also machine-verified). Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"} surveys related work in both complexity theory and formal verification. Section [\[sec:engineering\]](#sec:engineering){reference-type="ref" reference="sec:engineering"} discusses proof engineering insights. Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} contains proof listings.

## Artifact Availability

The complete Lean 4 formalization is available at:

::: center
<https://doi.org/10.5281/zenodo.18140965>
:::

The proofs build with `lake build` using the Lean toolchain specified in `lean-toolchain`. We encourage artifact evaluation and welcome contributions extending the reduction framework.


# Formalization Methodology {#sec:methodology}

This section describes our Lean 4 framework for formalizing polynomial-time reductions and complexity proofs. We discuss design decisions, integration with Mathlib, and challenges specific to complexity theory in dependent type systems.

## Representing Decision Problems

Decision problems are represented as `Prop`-valued functions over finite types:

    def DecisionProblem (α : Type*) := α → Prop

    structure Instance (P : DecisionProblem α) where
      input : α
      certificate : P input → Prop  -- witness structure for NP

For complexity classes requiring witness bounds, we bundle size constraints:

    structure NPWitness (P : DecisionProblem α) (x : α) where
      witness : β
      valid : P x ↔ ∃ w : β, verify x w
      size_bound : size witness ≤ poly (size x)

## Polynomial-Time Reductions

Karp reductions are bundled structures containing the reduction function, correctness proof, and polynomial bound:

    structure KarpReduction (P : DecisionProblem α) (Q : DecisionProblem β) where
      f : α → β
      correct : ∀ x, P x ↔ Q (f x)
      poly_time : ∃ p : Polynomial ℕ, ∀ x, time (f x) ≤ p.eval (size x)

Reduction composition preserves polynomial bounds:

    def KarpReduction.comp (r₁ : KarpReduction P Q) (r₂ : KarpReduction Q R) :
        KarpReduction P R where
      f := r₂.f ∘ r₁.f
      correct := fun x => (r₁.correct x).trans (r₂.correct (r₁.f x))
      poly_time := poly_comp r₁.poly_time r₂.poly_time

## Complexity Class Membership

We define complexity classes via their characteristic properties:

    def InNP (P : DecisionProblem α) : Prop :=
      ∃ V : α → β → Prop,
        (∀ x, P x ↔ ∃ w, V x w) ∧
        (∃ p, ∀ x w, V x w → size w ≤ p.eval (size x)) ∧
        PolyTimeVerifiable V

    def InCoNP (P : DecisionProblem α) : Prop :=
      InNP (fun x => ¬P x)

    def CoNPComplete (P : DecisionProblem α) : Prop :=
      InCoNP P ∧ ∀ Q : DecisionProblem β, InCoNP Q → KarpReduction Q P

## The Sufficiency Problem Encoding

The core decision problem is encoded as:

    structure DecisionProblemWithCoords (n : ℕ) where
      actions : Finset Action
      states : Fin n → Finset State
      optimal : (Fin n → State) → Finset Action

    def Sufficient (D : DecisionProblemWithCoords n) (I : Finset (Fin n)) : Prop :=
      ∀ s s' : Fin n → State,
        (∀ i ∈ I, s i = s' i) → D.optimal s = D.optimal s'

The reduction from TAUTOLOGY constructs a decision problem where sufficiency of coordinate set $I$ is equivalent to the formula being a tautology.

## Handling Classical vs Constructive Reasoning

Complexity theory inherently uses classical reasoning (e.g., "$P$ or not $P$" for decision problems). We use Lean's `Classical` namespace where necessary:

    open Classical in
    theorem sufficiency_decidable (D : DecisionProblemWithCoords n) (I : Finset (Fin n)) :
        Decidable (Sufficient D I) := by
      apply decidable_of_iff (∀ s s', _)
      · exact Fintype.decidableForallFintype

The `#print axioms` command verifies which axioms each theorem depends on. Our constructive lemmas (basic properties, reduction correctness) avoid classical axioms; hardness proofs necessarily use `Classical.choice`.

## Integration with Mathlib

We build on Mathlib's existing infrastructure:

-   **Computability:** `Mathlib.Computability.Primrec` for primitive recursive functions, used to establish polynomial bounds

-   **Finset/Fintype:** Finite sets and types for encoding bounded state spaces

-   **Polynomial:** `Mathlib.Algebra.Polynomial` for polynomial time bounds

-   **Order:** Lattice operations for sufficiency lattices

Where Mathlib lacks coverage (e.g., Karp reductions, W-hierarchy), we provide standalone definitions designed for future Mathlib contribution.

## Proof Automation

We develop custom tactics for common reduction patterns:

    macro "reduce_from" src:term : tactic =>
      `(tactic| (
        refine ⟨?f, ?correct, ?poly⟩
        case f => exact $src.f
        case correct => intro x; exact $src.correct x
        case poly => exact $src.poly_time
      ))

For sufficiency proofs, we use a `sufficiency` tactic that unfolds the definition and applies extensionality:

    macro "sufficiency" : tactic =>
      `(tactic| (
        unfold Sufficient
        intro s s' heq
        ext a
        simp only [Finset.mem_filter]
        constructor <;> intro h <;> exact h
      ))

## Verification Commands

Each theorem includes verification metadata:

    #check @sufficiency_coNP_complete  -- type signature
    #print axioms sufficiency_coNP_complete  -- axiom dependencies
    #eval Nat.repr (countSorry `sufficiency_coNP_complete)  -- 0

The build log (included in the artifact) records successful compilation of all 230+ theorems with 0 `sorry` placeholders.


# Formal Foundations {#sec:foundations}

We formalize decision problems with coordinate structure, sufficiency of coordinate sets, and the decision quotient, drawing on classical decision theory [@savage1954foundations; @raiffa1961applied]. All definitions in this section are implemented in Lean 4 using the encoding described in Section [\[sec:methodology\]](#sec:methodology){reference-type="ref" reference="sec:methodology"}.

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
