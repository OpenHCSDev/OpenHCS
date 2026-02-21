/-
  Paper 4: Decision-Relevant Uncertainty

  ClaimClosure.lean - Closure of paper-level claim steps

  This module mechanizes paper-specific claims that were previously
  prose-only or partially mechanized composition steps:
  - Sufficiency characterization via projected optimal-set cover
  - ADQ ordering monotonicity
  - One-step deterministic bridge
  - Over-modeling diagnostic contrapositive (in the Boolean model)
  - Conditional no-auto-minimization corollary logic
-/

import DecisionQuotient.Sufficiency
import DecisionQuotient.Instances
import DecisionQuotient.Computation
import DecisionQuotient.Reduction
import DecisionQuotient.Reduction_AllCoords
import DecisionQuotient.Hardness
import DecisionQuotient.Hardness.Sigma2PHardness
import DecisionQuotient.HardnessDistribution
import DecisionQuotient.Tractability.BoundedActions
import DecisionQuotient.Tractability.SeparableUtility
import DecisionQuotient.Tractability.TreeStructure
import Mathlib.Data.Rat.Init
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace DecisionQuotient
namespace ClaimClosure

open scoped Finset

/-! ## Shared coordinate lemmas -/

lemma agreeOn_refl {S : Type*} {n : ℕ} [CoordinateSpace S n]
    (s : S) (I : Finset (Fin n)) :
    agreeOn s s I := by
  intro i hi
  rfl

lemma agreeOn_symm {S : Type*} {n : ℕ} [CoordinateSpace S n]
    {s s' : S} {I : Finset (Fin n)} :
    agreeOn s s' I → agreeOn s' s I := by
  intro h i hi
  exact (h i hi).symm

lemma agreeOn_trans {S : Type*} {n : ℕ} [CoordinateSpace S n]
    {s₁ s₂ s₃ : S} {I : Finset (Fin n)} :
    agreeOn s₁ s₂ I → agreeOn s₂ s₃ I → agreeOn s₁ s₃ I := by
  intro h12 h23 i hi
  exact (h12 i hi).trans (h23 i hi)

/-! ## Proposition `prop:sufficiency-char` (finite-model mechanization) -/

section SufficiencyCharacterization

variable {A S : Type*} {n : ℕ}
variable [Fintype A] [Fintype S] [DecidableEq A]
variable [CoordinateSpace S n]

/-- Finite optimal-action set at a state. -/
noncomputable def optFinset (dp : DecisionProblem A S) (s : S) : Finset A :=
  by
    classical
    exact Finset.univ.filter (fun a => a ∈ dp.Opt s)

/-- States that agree with `s` on coordinates `I`. -/
noncomputable def compatibleStates (I : Finset (Fin n)) (s : S) : Finset S :=
  by
    classical
    exact Finset.univ.filter (fun s' => agreeOn s s' I)

/-- Union of optimal-action sets over the projection class of `s` under `I`. -/
noncomputable def projectedOptCover (dp : DecisionProblem A S) (I : Finset (Fin n))
    (s : S) : Finset A :=
  (compatibleStates (n := n) I s).biUnion (fun s' => optFinset dp s')

/-- Decision quotient induced by coordinate set `I` at state `s` (finite model). -/
noncomputable def dqProjection (dp : DecisionProblem A S) (I : Finset (Fin n))
    (s : S) : ℚ :=
  (projectedOptCover (n := n) dp I s).card / (Fintype.card A : ℚ)

/-- Baseline quotient value from the exact optimal set at `s`. -/
noncomputable def dqExact (dp : DecisionProblem A S) (s : S) : ℚ :=
  (optFinset dp s).card / (Fintype.card A : ℚ)

lemma mem_compatibleStates_iff (I : Finset (Fin n)) (s t : S) :
    t ∈ compatibleStates (n := n) I s ↔ agreeOn s t I := by
  classical
  simp [compatibleStates]

omit [Fintype S] [DecidableEq A] in
lemma mem_optFinset_iff (dp : DecisionProblem A S) (s : S) (a : A) :
    a ∈ optFinset dp s ↔ a ∈ dp.Opt s := by
  classical
  simp [optFinset]

lemma optFinset_subset_projectedOptCover (dp : DecisionProblem A S)
    (I : Finset (Fin n)) (s : S) :
    optFinset dp s ⊆ projectedOptCover (n := n) dp I s := by
  intro a ha
  have hs : s ∈ compatibleStates (n := n) I s :=
    (mem_compatibleStates_iff (n := n) I s s).2 (agreeOn_refl (n := n) s I)
  exact Finset.mem_biUnion.mpr ⟨s, hs, ha⟩

/-- If `I` is sufficient, the projected cover equals the exact optimal set at every state. -/
theorem projectedOptCover_eq_opt_of_sufficient (dp : DecisionProblem A S)
    (I : Finset (Fin n)) (hI : dp.isSufficient I) :
    ∀ s : S, projectedOptCover (n := n) dp I s = optFinset dp s := by
  intro s
  apply Finset.ext
  intro a
  constructor
  · intro ha
    rcases Finset.mem_biUnion.mp ha with ⟨s', hs', ha'⟩
    have hsAgree : agreeOn s s' I :=
      (mem_compatibleStates_iff (n := n) I s s').1 hs'
    have hOptEq : dp.Opt s' = dp.Opt s :=
      hI s' s ((agreeOn_symm (n := n)) hsAgree)
    have haOptS' : a ∈ dp.Opt s := by
      have haOptS'Raw : a ∈ dp.Opt s' := (mem_optFinset_iff dp s' a).1 ha'
      simpa [hOptEq] using haOptS'Raw
    exact (mem_optFinset_iff dp s a).2 haOptS'
  · intro ha
    have hs : s ∈ compatibleStates (n := n) I s :=
      (mem_compatibleStates_iff (n := n) I s s).2 (agreeOn_refl (n := n) s I)
    exact Finset.mem_biUnion.mpr ⟨s, hs, ha⟩

/-- Converse direction: classwise projected-cover equality implies sufficiency. -/
theorem sufficient_of_projectedOptCover_eq_opt (dp : DecisionProblem A S)
    (I : Finset (Fin n))
    (hCover : ∀ s : S, projectedOptCover (n := n) dp I s = optFinset dp s) :
    dp.isSufficient I := by
  intro s s' hss'
  have hClassEq : compatibleStates (n := n) I s = compatibleStates (n := n) I s' := by
    apply Finset.ext
    intro t
    constructor
    · intro ht
      have hst : agreeOn s t I :=
        (mem_compatibleStates_iff (n := n) I s t).1 ht
      have hs't : agreeOn s' t I :=
        agreeOn_trans (n := n) ((agreeOn_symm (n := n)) hss') hst
      exact (mem_compatibleStates_iff (n := n) I s' t).2 hs't
    · intro ht
      have hs't : agreeOn s' t I :=
        (mem_compatibleStates_iff (n := n) I s' t).1 ht
      have hst : agreeOn s t I :=
        agreeOn_trans (n := n) hss' hs't
      exact (mem_compatibleStates_iff (n := n) I s t).2 hst
  have hCoverEq : projectedOptCover (n := n) dp I s = projectedOptCover (n := n) dp I s' := by
    simp [projectedOptCover, hClassEq]
  have hOptFinEq : optFinset dp s = optFinset dp s' := by
    calc
      optFinset dp s = projectedOptCover (n := n) dp I s := (hCover s).symm
      _ = projectedOptCover (n := n) dp I s' := hCoverEq
      _ = optFinset dp s' := hCover s'
  ext a
  constructor
  · intro ha
    have haf : a ∈ optFinset dp s := (mem_optFinset_iff dp s a).2 ha
    have haf' : a ∈ optFinset dp s' := by simpa [hOptFinEq] using haf
    exact (mem_optFinset_iff dp s' a).1 haf'
  · intro ha
    have haf : a ∈ optFinset dp s' := (mem_optFinset_iff dp s' a).2 ha
    have haf' : a ∈ optFinset dp s := by simpa [hOptFinEq] using haf
    exact (mem_optFinset_iff dp s a).1 haf'

/-- Finite-model equivalence used for Proposition `prop:sufficiency-char`. -/
theorem sufficiency_iff_projectedOptCover_eq_opt (dp : DecisionProblem A S)
    (I : Finset (Fin n)) :
    dp.isSufficient I ↔
      ∀ s : S, projectedOptCover (n := n) dp I s = optFinset dp s := by
  constructor
  · exact projectedOptCover_eq_opt_of_sufficient (n := n) dp I
  · exact sufficient_of_projectedOptCover_eq_opt (n := n) dp I

/-- Quotient-ratio form (with nonempty actions) matching the paper statement. -/
theorem sufficiency_iff_dq_ratio (dp : DecisionProblem A S)
    [Nonempty A] (I : Finset (Fin n)) :
    dp.isSufficient I ↔ ∀ s : S, dqProjection (n := n) dp I s = dqExact dp s := by
  constructor
  · intro hI s
    have hEq := projectedOptCover_eq_opt_of_sufficient (n := n) dp I hI s
    simp [dqProjection, dqExact, hEq]
  · intro hRatio
    have hAq : (Fintype.card A : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card A))
    have hCover : ∀ s : S, projectedOptCover (n := n) dp I s = optFinset dp s := by
      intro s
      have hq := hRatio s
      have hmul := congrArg (fun x : ℚ => x * (Fintype.card A : ℚ)) hq
      have hcardQ : ((projectedOptCover (n := n) dp I s).card : ℚ) = ((optFinset dp s).card : ℚ) := by
        simpa [dqProjection, dqExact, hAq] using hmul
      have hcard : (projectedOptCover (n := n) dp I s).card = (optFinset dp s).card := by
        exact_mod_cast hcardQ
      have hsub : optFinset dp s ⊆ projectedOptCover (n := n) dp I s :=
        optFinset_subset_projectedOptCover (n := n) dp I s
      have hcardle : (projectedOptCover (n := n) dp I s).card ≤ (optFinset dp s).card := by
        simp [hcard]
      have hEqSub : optFinset dp s = projectedOptCover (n := n) dp I s :=
        Finset.eq_of_subset_of_card_le hsub hcardle
      exact hEqSub.symm
    exact sufficient_of_projectedOptCover_eq_opt (n := n) dp I hCover

end SufficiencyCharacterization

/-! ## Proposition `prop:adq-ordering` -/

section ADQOrdering

variable {B : Type*}

/-- Finite-model ADQ value over a behavior universe `U` and achievable set `X`. -/
noncomputable def adq (U X : Finset B) : ℚ :=
  (X.card : ℚ) / (U.card : ℚ)

/-- If ADQ is strictly smaller against the same nonempty denominator,
then achievable-cardinality is strictly smaller. -/
theorem adq_ordering
    (U X Y : Finset B) (hU : 0 < U.card)
    (hLt : adq U X < adq U Y) :
    X.card < Y.card := by
  have hUq : (0 : ℚ) < (U.card : ℚ) := by
    exact_mod_cast hU
  have hCardQ : (X.card : ℚ) < (Y.card : ℚ) := by
    exact (div_lt_div_iff_of_pos_right hUq).mp hLt
  exact_mod_cast hCardQ

end ADQOrdering

/-! ## Proposition `prop:one-step-bridge` -/

section OneStepBridge

variable {A S : Type*}

/-- One-step deterministic sequential regime (bridge fragment). -/
structure OneStepSequentialObjective where
  reward : A → S → ℝ

/-- One-step optimizer set. -/
def OneStepSequentialObjective.Opt (R : OneStepSequentialObjective (A := A) (S := S))
    (s : S) : Set A :=
  { a : A | ∀ a' : A, R.reward a' s ≤ R.reward a s }

/-- Induced static decision problem. -/
def OneStepSequentialObjective.toDecisionProblem
    (R : OneStepSequentialObjective (A := A) (S := S)) :
    DecisionProblem A S :=
  { utility := R.reward }

/-- Sufficiency in one-step sequential form. -/
def OneStepSequentialObjective.isSufficient
    (R : OneStepSequentialObjective (A := A) (S := S))
    {n : ℕ} [CoordinateSpace S n] (I : Finset (Fin n)) : Prop :=
  ∀ s s' : S, agreeOn s s' I → R.Opt s = R.Opt s'

/-- Formal one-step deterministic bridge used in Proposition `prop:one-step-bridge`. -/
theorem one_step_bridge
    (R : OneStepSequentialObjective (A := A) (S := S))
    {n : ℕ} [CoordinateSpace S n] (I : Finset (Fin n)) :
    R.isSufficient I ↔ (R.toDecisionProblem).isSufficient I := by
  rfl

end OneStepBridge

/-! ## Over-modeling diagnostic contrapositive in the mechanized Boolean model -/

section DiagnosticContrapositive

open Sigma2PHardness

variable {A : Type*} {n : ℕ}

/-- Boundary characterization predicate in the mechanized Boolean model:
there exists an exactly relevance-identifying coordinate set. -/
def boundaryCharacterized
    (dp : DecisionProblem A (Fin n → Bool)) : Prop :=
  ∃ I : Finset (Fin n), exactlyIdentifiesRelevant dp I

/-- Contrapositive diagnostic theorem:
if exact relevance identification fails for every candidate set,
boundary characterization fails in this model. -/
theorem no_exact_identifier_implies_not_boundary_characterized
    (dp : DecisionProblem A (Fin n → Bool)) :
    (¬ ∃ I : Finset (Fin n), exactlyIdentifiesRelevant dp I) →
      ¬ boundaryCharacterized dp := by
  intro hNone hBoundary
  exact hNone hBoundary

/-- Equivalent form using the sufficient-and-subset characterization. -/
theorem boundaryCharacterized_iff_exists_sufficient_subset
    (dp : DecisionProblem A (Fin n → Bool)) :
    boundaryCharacterized dp ↔
      ∃ I : Finset (Fin n), dp.isSufficient I ∧ I ⊆ relevantFinset dp := by
  constructor
  · rintro ⟨I, hI⟩
    exact ⟨I, (exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset dp I).1 hI⟩
  · rintro ⟨I, hI⟩
    exact ⟨I, (exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset dp I).2 hI⟩

end DiagnosticContrapositive

/-! ## Conditional composition theorem for `cor:no-auto-minimize` -/

section ConditionalComposition

/-- Pure logical closure used by `cor:no-auto-minimize`:
if a polytime exact minimizer implies a class collapse, then under
non-collapse no such minimizer exists. -/
theorem no_auto_minimize_of_p_neq_conp
    {P_eq_coNP HasPolytimeExactMinimizer : Prop}
    (hNeq : ¬ P_eq_coNP)
    (hCollapse : HasPolytimeExactMinimizer → P_eq_coNP) :
    ¬ HasPolytimeExactMinimizer := by
  intro hPoly
  exact hNeq (hCollapse hPoly)

end ConditionalComposition

/-! ## Complexity-theoretic lift closures (explicitly conditional on standard facts) -/

section ComplexityLifts

open Sigma2PHardness

/-- Named bundle for standard external assumptions used by conditional lift theorems.
    This keeps assumption tracking explicit when assembling theorem-level closures. -/
structure StandardComplexityAssumptions
    (TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP RelevantCard_coNP
      RelevantCard_coNP_complete ExistsForallSAT_sigma2p_complete ETH : Prop) : Prop where
  hTautologyCoNPComplete : TAUTOLOGY_coNP_complete
  hSufficiencyInCoNP : SUFFICIENCY_in_coNP
  hRelevantCardCoNP : RelevantCard_coNP
  hRelevantCardCoNPComplete : RelevantCard_coNP_complete
  hExistsForallSATSigma2PComplete : ExistsForallSAT_sigma2p_complete
  hETH : ETH

/-! ### SUFFICIENCY-CHECK (coNP) -/

/-- Mechanized reduction core used in coNP transfer for SUFFICIENCY-CHECK. -/
theorem sufficiency_conp_reduction_core {n : ℕ} (φ : Formula n) :
    (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology :=
  (tautology_iff_sufficient φ).symm

/-- Conditional coNP-completeness transfer for SUFFICIENCY-CHECK.
    The transfer/completeness fact itself is treated as a standard external lemma. -/
theorem sufficiency_conp_complete_conditional
    {n : ℕ}
    {TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP SUFFICIENCY_coNP_complete : Prop}
    (hIn : SUFFICIENCY_in_coNP)
    (hCompose :
      TAUTOLOGY_coNP_complete → SUFFICIENCY_in_coNP →
      (∀ φ : Formula n,
        (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology) →
      SUFFICIENCY_coNP_complete) :
    TAUTOLOGY_coNP_complete → SUFFICIENCY_coNP_complete := by
  intro hT
  exact hCompose hT hIn (fun φ => (tautology_iff_sufficient φ).symm)

/-! ### MINIMUM-SUFFICIENT-SET collapse and coNP lift -/

/-- Mechanized quantifier-collapse core used by both collapse and coNP claims. -/
theorem minsuff_collapse_core
    {A : Type*} {n : ℕ} (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ) :
    (∃ I : Finset (Fin n), I.card ≤ k ∧ dp.isSufficient I) ↔
      (relevantFinset dp).card ≤ k :=
  min_sufficient_set_iff_relevant_card (dp := dp) k

/-- Conditional lift from the collapse core to the coNP-reading consequence. -/
theorem minsuff_collapse_to_conp_conditional
    {RelevantCard_coNP MSS_collapse_consequence : Prop}
    (hCompose :
      RelevantCard_coNP →
      (∀ (A : Type*) (n : ℕ) (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ),
        (∃ I : Finset (Fin n), I.card ≤ k ∧ dp.isSufficient I) ↔
          (relevantFinset dp).card ≤ k) →
      MSS_collapse_consequence) :
    RelevantCard_coNP → MSS_collapse_consequence := by
  intro hCard
  exact hCompose hCard (fun A n dp k => min_sufficient_set_iff_relevant_card (dp := dp) k)

/-- Conditional coNP-completeness transfer for MINIMUM-SUFFICIENT-SET. -/
theorem minsuff_conp_complete_conditional
    {RelevantCard_coNP_complete MSS_coNP_complete : Prop}
    (hCompose :
      RelevantCard_coNP_complete →
      (∀ (A : Type*) (n : ℕ) (dp : DecisionProblem A (Fin n → Bool)) (k : ℕ),
        (∃ I : Finset (Fin n), I.card ≤ k ∧ dp.isSufficient I) ↔
          (relevantFinset dp).card ≤ k) →
      MSS_coNP_complete) :
    RelevantCard_coNP_complete → MSS_coNP_complete := by
  intro hCard
  exact hCompose hCard (fun A n dp k => min_sufficient_set_iff_relevant_card (dp := dp) k)

/-! ### ANCHOR-SUFFICIENCY (\Sigma_2^P) -/

/-- Mechanized \(\exists\forall\)-SAT reduction core for ANCHOR-SUFFICIENCY. -/
theorem anchor_sigma2p_reduction_core (φ : ExistsForallFormula) :
    ExistsForallFormula.satisfiable φ ↔
      (qbfProblem (ExistsForallFormula.padUniversal φ)).anchorSufficient
        (xCoords (ExistsForallFormula.padUniversal φ).nx (ExistsForallFormula.padUniversal φ).ny) :=
  anchor_sufficiency_sigma2p φ

/-- Conditional \(\Sigma_2^P\)-completeness transfer for ANCHOR-SUFFICIENCY. -/
theorem anchor_sigma2p_complete_conditional
    {ExistsForallSAT_sigma2p_complete Anchor_sigma2p_complete : Prop}
    (hCompose :
      ExistsForallSAT_sigma2p_complete →
      (∀ φ : ExistsForallFormula,
        ExistsForallFormula.satisfiable φ ↔
          (qbfProblem (ExistsForallFormula.padUniversal φ)).anchorSufficient
            (xCoords (ExistsForallFormula.padUniversal φ).nx (ExistsForallFormula.padUniversal φ).ny)) →
      Anchor_sigma2p_complete) :
    ExistsForallSAT_sigma2p_complete → Anchor_sigma2p_complete := by
  intro hSrc
  exact hCompose hSrc (fun φ => anchor_sufficiency_sigma2p φ)

/-! ### Dichotomy and ETH-conditioned lower bound closure -/

/-- Mechanized hard-family core used in the ETH branch. -/
theorem hard_family_all_coords_core {n : ℕ} (φ : Formula n) (h : ¬ φ.isTautology) :
    ∀ i : Fin n, (reductionProblemMany φ).isRelevant i :=
  all_coords_relevant_of_not_tautology (φ := φ) h

/-- Mechanized explicit-state algorithmic upper-core. -/
theorem explicit_state_upper_core
    {A S : Type*} [DecidableEq S] [DecidableEq (Set A)]
    (dp : DecisionProblem A S) (equiv : S → S → Prop) [DecidableRel equiv]
    (pairs : List (S × S)) :
    (countedCheckPairs dp equiv pairs).steps ≤ pairs.length :=
  countedCheckPairs_steps_bound dp equiv pairs

/-- Conditional dichotomy closure: explicit upper branch + ETH transfer from hard family. -/
theorem dichotomy_conditional
    {ETH ExplicitStateUpperBound SuccinctETHLowerBound : Prop}
    (hExplicit : ExplicitStateUpperBound)
    (hTransfer :
      ETH →
      (∀ {n : ℕ} (φ : Formula n), ¬ φ.isTautology →
        ∀ i : Fin n, (reductionProblemMany φ).isRelevant i) →
      SuccinctETHLowerBound) :
    ETH → (ExplicitStateUpperBound ∧ SuccinctETHLowerBound) := by
  intro hEth
  refine ⟨hExplicit, ?_⟩
  exact hTransfer hEth (fun φ hnt i => all_coords_relevant_of_not_tautology (φ := φ) hnt i)

/-! ### Cost asymmetry under ETH (conditional closure) -/

/-- Conditional cost-asymmetry closure:
    if ETH yields an eventual \(2^n\)-lower-bound for finding-cost, then
    linear-overhead maintenance is eventually dominated. -/
theorem cost_asymmetry_eth_conditional
    {ETH : Prop} {Cfind : ℕ → ℕ}
    (k c : ℕ)
    (hLower : ETH → ∃ n0, ∀ n ≥ n0, 2 ^ n ≤ Cfind n) :
    ETH → ∃ n0, ∀ n ≥ n0, k < Cfind n + c := by
  intro hEth
  obtain ⟨n1, h1⟩ := HardnessDistribution.linear_lt_exponential_plus_constant_eventually k c
  obtain ⟨n2, h2⟩ := hLower hEth
  refine ⟨max n1 n2, ?_⟩
  intro n hn
  have hn1 : n ≥ n1 := le_trans (Nat.le_max_left _ _) hn
  have hn2 : n ≥ n2 := le_trans (Nat.le_max_right _ _) hn
  have hk : k < 2 ^ n + c := h1 n hn1
  have hpow : 2 ^ n ≤ Cfind n := h2 n hn2
  exact lt_of_lt_of_le hk (Nat.add_le_add_right hpow c)

/-! ### Tractable-subcase closure -/

/-- Mechanized bounded-action tractable branch. -/
theorem tractable_bounded_core
    {A S : Type*} [DecidableEq A] [DecidableEq S]
    {n : ℕ} [CoordinateSpace S n] [Fintype A] [Fintype S]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S) (k : ℕ)
    (hcard : Fintype.card A ≤ k) :
    ∃ (decide : Finset (Fin n) → Bool),
      (∀ I, decide I = true ↔ cdp.toAbstract.isSufficient I) :=
  sufficiency_poly_bounded_actions (k := k) cdp hcard

/-- Mechanized separable-utility tractable branch. -/
theorem tractable_separable_core
    {A S : Type*} [DecidableEq A] [DecidableEq S]
    {n : ℕ} [CoordinateSpace S n]
    (dp : FiniteDecisionProblem (A := A) (S := S))
    (hsep : SeparableUtility (dp := dp)) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ dp.isSufficient I :=
  sufficiency_poly_separable (dp := dp) hsep

/-- Mechanized tree-structured tractable branch. -/
theorem tractable_tree_core
    {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S)
    (deps : Fin n → Finset (Fin n)) (htree : TreeStructured deps) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I :=
  sufficiency_poly_tree_structured cdp deps htree

/-- Conditional assembly theorem for the full tractable-subcase statement. -/
theorem tractable_subcases_conditional
    {BoundedCase SeparableCase TreeCase TractableSubcases : Prop}
    (hBounded : BoundedCase)
    (hSeparable : SeparableCase)
    (hTree : TreeCase)
    (hAssemble : BoundedCase → SeparableCase → TreeCase → TractableSubcases) :
    TractableSubcases :=
  hAssemble hBounded hSeparable hTree

end ComplexityLifts

/-! ## Subproblem-to-full transfer closure (`#2`) -/

section SubproblemTransfer

/-- Generic transfer principle:
hardness of a subproblem lifts to the full problem whenever every full solver
induces a solver for the subproblem. -/
theorem subproblem_hardness_lifts_to_full
    {HasFullSolver HasSubSolver : Prop}
    (hRestrict : HasFullSolver → HasSubSolver)
    (hSubHard : ¬ HasSubSolver) :
    ¬ HasFullSolver := by
  intro hFull
  exact hSubHard (hRestrict hFull)

end SubproblemTransfer

/-! ## Selector / epsilon transfer-separation (`#6`) -/

section SelectorAndEpsilon

variable {A S : Type*} {n : ℕ} [CoordinateSpace S n]

/-- ε-optimal action set. -/
def DecisionProblem.epsOpt (dp : DecisionProblem A S) (ε : ℝ) (s : S) : Set A :=
  { a : A | ∀ a' : A, dp.utility a' s ≤ dp.utility a s + ε }

/-- ε-sufficiency: projection agreement preserves ε-optimal sets. -/
def DecisionProblem.isEpsilonSufficient (dp : DecisionProblem A S)
    (ε : ℝ) (I : Finset (Fin n)) : Prop :=
  ∀ s s' : S, agreeOn s s' I →
    DecisionProblem.epsOpt dp ε s = DecisionProblem.epsOpt dp ε s'

theorem DecisionProblem.epsOpt_zero_eq_opt (dp : DecisionProblem A S) (s : S) :
    DecisionProblem.epsOpt dp 0 s = dp.Opt s := by
  ext a
  simp [DecisionProblem.epsOpt, DecisionProblem.Opt, DecisionProblem.isOptimal]

theorem DecisionProblem.sufficient_iff_zeroEpsilonSufficient
    (dp : DecisionProblem A S) (I : Finset (Fin n)) :
    dp.isSufficient I ↔ DecisionProblem.isEpsilonSufficient dp 0 I := by
  constructor
  · intro hI
    intro s s' hs
    simpa [DecisionProblem.epsOpt_zero_eq_opt (dp := dp) s,
      DecisionProblem.epsOpt_zero_eq_opt (dp := dp) s'] using hI s s' hs
  · intro hI
    intro s s' hs
    simpa [DecisionProblem.epsOpt_zero_eq_opt (dp := dp) s,
      DecisionProblem.epsOpt_zero_eq_opt (dp := dp) s'] using hI s s' hs

/-! ### Explicit selector-level separation witness -/

private def i0 : Fin 1 := ⟨0, by decide⟩
private def sFalse : Fin 1 → Bool := fun _ => false
private def sTrue : Fin 1 → Bool := fun _ => true

/-- Witness problem where selector-level sufficiency can hold while set-level
sufficiency fails (for `I = ∅`). -/
def selectorGapProblem : DecisionProblem Bool (Fin 1 → Bool) where
  utility := fun a s =>
    if s i0 then
      if a = true then 1 else 1
    else
      if a = true then 1 else 0

noncomputable def preferTrueSelector (X : Set Bool) : Bool := by
  classical
  exact if (true : Bool) ∈ X then true else false

theorem selectorGap_true_mem_opt (s : Fin 1 → Bool) :
    (true : Bool) ∈ (selectorGapProblem.Opt s) := by
  unfold selectorGapProblem DecisionProblem.Opt DecisionProblem.isOptimal
  intro a'
  cases a' <;> by_cases hs : s i0 <;> simp [hs]

theorem selectorGap_selectorSufficient_empty :
    selectorGapProblem.isSelectorSufficient preferTrueSelector (∅ : Finset (Fin 1)) := by
  intro s s' _
  unfold DecisionProblem.SelectedAction preferTrueSelector
  have hs : (true : Bool) ∈ selectorGapProblem.Opt s := selectorGap_true_mem_opt s
  have hs' : (true : Bool) ∈ selectorGapProblem.Opt s' := selectorGap_true_mem_opt s'
  simp [hs, hs']

theorem selectorGap_not_set_sufficient_empty :
    ¬ selectorGapProblem.isSufficient (∅ : Finset (Fin 1)) := by
  intro hsuff
  have hconst :=
    (DecisionProblem.emptySet_sufficient_iff_constant (dp := selectorGapProblem)).1 hsuff
  have hEq : selectorGapProblem.Opt sFalse = selectorGapProblem.Opt sTrue := hconst sFalse sTrue
  have hFalseInTrue : (false : Bool) ∈ selectorGapProblem.Opt sTrue := by
    unfold selectorGapProblem DecisionProblem.Opt DecisionProblem.isOptimal sTrue i0
    intro a'
    cases a' <;> simp
  have hFalseNotInFalse : (false : Bool) ∉ selectorGapProblem.Opt sFalse := by
    intro hmem
    have h := hmem true
    unfold selectorGapProblem sFalse i0 at h
    norm_num at h
  have hFalseInFalse : (false : Bool) ∈ selectorGapProblem.Opt sFalse := by
    simpa [hEq] using hFalseInTrue
  exact hFalseNotInFalse hFalseInFalse

theorem selectorSufficient_not_implies_setSufficient :
    ∃ (dp : DecisionProblem Bool (Fin 1 → Bool))
      (σ : Set Bool → Bool) (I : Finset (Fin 1)),
      dp.isSelectorSufficient σ I ∧ ¬ dp.isSufficient I := by
  refine ⟨selectorGapProblem, preferTrueSelector, ∅, ?_⟩
  exact ⟨selectorGap_selectorSufficient_empty, selectorGap_not_set_sufficient_empty⟩

end SelectorAndEpsilon

/-! ## Assumption ledger projection (`#8`) -/

section AssumptionLedger

theorem standard_assumption_ledger_unpack
    {TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP RelevantCard_coNP
      RelevantCard_coNP_complete ExistsForallSAT_sigma2p_complete ETH : Prop}
    (hStd : StandardComplexityAssumptions TAUTOLOGY_coNP_complete SUFFICIENCY_in_coNP
      RelevantCard_coNP RelevantCard_coNP_complete
      ExistsForallSAT_sigma2p_complete ETH) :
    TAUTOLOGY_coNP_complete ∧ SUFFICIENCY_in_coNP ∧ RelevantCard_coNP ∧
      RelevantCard_coNP_complete ∧ ExistsForallSAT_sigma2p_complete ∧ ETH := by
  refine ⟨hStd.hTautologyCoNPComplete, hStd.hSufficiencyInCoNP, hStd.hRelevantCardCoNP,
    hStd.hRelevantCardCoNPComplete, hStd.hExistsForallSATSigma2PComplete, hStd.hETH⟩

end AssumptionLedger

end ClaimClosure
end DecisionQuotient
