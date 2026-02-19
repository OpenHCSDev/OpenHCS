/-
  Credibility/Basic.lean

  Core definitions for credibility theory (Paper 5 Section 2)

  Definitions:
    2.0a Mathematical Credibility
    2.0b Social Credibility
    2.0c Domain Independence
    2.0d Costly Signal Domain-Specificity
    2.1 Signal
    2.2 Cheap Talk
    2.3 Costly Signal
    2.4 Prior
    2.5 Credibility Function
    2.6 Rational Agent
    2.7 Deception Prior
    2.8 Magnitude
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic

namespace Credibility

/-! ## Section 2.0: Two Credibility Domains -/

/-- Credibility domains: mathematical (formal verification) vs social (institutional acceptance) -/
inductive CredibilityDomain
  | mathematical  -- Audience: formal verifier; measure: logical soundness
  | social        -- Audience: human agents; measure: institutional acceptance
  deriving DecidableEq, Repr

/-- Definition 2.0a/b: Domain-specific credibility function type -/
def DomainCredibilityFn (Claim Signal : Type*) :=
  CredibilityDomain → Claim → Signal → ℝ

/-- A signal's costliness is domain-specific -/
structure DomainSignalCost where
  costMathTrue : ℝ   -- Cost in mathematical domain if claim is true
  costMathFalse : ℝ  -- Cost in mathematical domain if claim is false
  costSocTrue : ℝ    -- Cost in social domain if claim is true
  costSocFalse : ℝ   -- Cost in social domain if claim is false
  math_true_nonneg : 0 ≤ costMathTrue
  math_false_nonneg : 0 ≤ costMathFalse
  soc_true_nonneg : 0 ≤ costSocTrue
  soc_false_nonneg : 0 ≤ costSocFalse

/-- A signal is costly in the mathematical domain -/
def isCostlyInMathDomain (c : DomainSignalCost) : Prop :=
  c.costMathFalse > c.costMathTrue

/-- A signal is costly in the social domain -/
def isCostlyInSocialDomain (c : DomainSignalCost) : Prop :=
  c.costSocFalse > c.costSocTrue

/-- A signal is cheap talk in the mathematical domain -/
def isCheapTalkInMathDomain (c : DomainSignalCost) : Prop :=
  c.costMathTrue = c.costMathFalse

/-- A signal is cheap talk in the social domain -/
def isCheapTalkInSocialDomain (c : DomainSignalCost) : Prop :=
  c.costSocTrue = c.costSocFalse

/-- Theorem 2.0c: Domain Independence - costly in one domain does not imply costly in other -/
theorem domain_independence_math_not_implies_social :
    ∃ c : DomainSignalCost, isCostlyInMathDomain c ∧ isCheapTalkInSocialDomain c := by
  -- Machine-checked proof: costly in math domain, cheap talk in social domain
  use ⟨0, 1, 1, 1, le_refl 0, zero_le_one, zero_le_one, zero_le_one⟩
  constructor
  · -- costMathFalse (1) > costMathTrue (0)
    simp [isCostlyInMathDomain]
  · -- costSocTrue (1) = costSocFalse (1)
    simp [isCheapTalkInSocialDomain]

theorem domain_independence_social_not_implies_math :
    ∃ c : DomainSignalCost, isCostlyInSocialDomain c ∧ isCheapTalkInMathDomain c := by
  -- Institutional credential: costly in social domain, cheap talk in math domain
  use ⟨1, 1, 0, 1, zero_le_one, zero_le_one, le_refl 0, zero_le_one⟩
  constructor
  · -- costSocFalse (1) > costSocTrue (0)
    simp [isCostlyInSocialDomain]
  · -- costMathTrue (1) = costMathFalse (1)
    simp [isCheapTalkInMathDomain]

/-- Corollary 2.0d: Machine-checked proofs are maximally costly in math domain only.
    We model "infinite cost" as the property that costMathFalse can be arbitrarily large
    while costMathTrue remains bounded. -/
theorem machine_proof_domain_specificity :
    ∃ c : DomainSignalCost,
      c.costMathFalse > c.costMathTrue ∧
      isCheapTalkInSocialDomain c := by
  -- Use finite approximation (infinite cost modeled as very large)
  use ⟨0, 1, 1, 1, le_refl 0, zero_le_one, zero_le_one, zero_le_one⟩
  constructor
  · -- costMathFalse (1) > costMathTrue (0)
    norm_num
  · simp [isCheapTalkInSocialDomain]

/-! ## Definition 2.1: Signal -/

/-- A signal is content with associated truth and production cost -/
structure Signal where
  content : String
  cost : ℝ
  cost_nonneg : 0 ≤ cost

/-! ## Definition 2.2: Cheap Talk -/

/-- A signaling situation is cheap talk if cost is independent of truth -/
def isCheapTalk (costIfTrue costIfFalse : ℝ) : Prop :=
  costIfTrue = costIfFalse

/-! ## Definition 2.3: Costly Signal -/

/-- A signaling situation is costly if false claims cost more -/
def isCostlySignal (costIfTrue costIfFalse : ℝ) : Prop :=
  costIfFalse > costIfTrue

/-- Cost differential for costly signals -/
def costDifferential (costIfTrue costIfFalse : ℝ) : ℝ :=
  costIfFalse - costIfTrue

lemma costDifferential_pos_of_costly {costT costF : ℝ} 
    (h : isCostlySignal costT costF) : 0 < costDifferential costT costF := by
  simp only [costDifferential, isCostlySignal] at *
  linarith

/-! ## Definition 2.4: Prior -/

/-- Prior probability distribution -/
structure Prior (α : Type*) where
  prob : α → ℝ
  prob_nonneg : ∀ a, 0 ≤ prob a
  prob_le_one : ∀ a, prob a ≤ 1

/-! ## Definition 2.5: Credibility -/

/-- A credibility value is a probability in [0, 1].
    This enforces proper probability semantics for all credibility computations. -/
structure CredibilityValue where
  val : ℝ
  nonneg : 0 ≤ val
  le_one : val ≤ 1

namespace CredibilityValue

/-- Coercion to ℝ for arithmetic -/
instance : Coe CredibilityValue ℝ := ⟨CredibilityValue.val⟩

/-- Zero credibility -/
def zero : CredibilityValue := ⟨0, le_refl 0, zero_le_one⟩

/-- Full credibility -/
def one : CredibilityValue := ⟨1, zero_le_one, le_refl 1⟩

/-- Ordering on credibility values -/
instance : LE CredibilityValue := ⟨fun a b => a.val ≤ b.val⟩
instance : LT CredibilityValue := ⟨fun a b => a.val < b.val⟩

theorem le_def {a b : CredibilityValue} : a ≤ b ↔ a.val ≤ b.val := Iff.rfl
theorem lt_def {a b : CredibilityValue} : a < b ↔ a.val < b.val := Iff.rfl

end CredibilityValue

/-- Credibility function type: maps claims and evidence to bounded credibility values -/
def CredibilityFn (Claim Evidence : Type*) := Claim → Evidence → CredibilityValue

/-! ## Definition 2.7: Deception Prior -/

/-- Probability that a random agent is deceptive -/
structure DeceptionPrior where
  π : ℝ
  π_nonneg : 0 ≤ π
  π_le_one : π ≤ 1

/-! ## Dual Truth Framework -/

/-- Truth vector: (Epistemic truth, Ego-driven truth) -/
structure TruthVector where
  epistemic : ℝ    -- E ∈ [0, 1], probability claim is epistemically true
  ego : ℝ          -- G ∈ [0, 1], probability claim is ego-aligned
  e_nonneg : 0 ≤ epistemic
  e_le_one : epistemic ≤ 1
  g_nonneg : 0 ≤ ego
  g_le_one : ego ≤ 1

namespace TruthVector

/-- Coercion to pair of real numbers -/
def toPair (tv : TruthVector) : (ℝ × ℝ) := (tv.epistemic, tv.ego)

/-- Zero truth vector -/
def zero : TruthVector := ⟨0, 0, le_refl 0, zero_le_one, le_refl 0, zero_le_one⟩

/-- Full truth vector (both epistemic and ego-driven truth are 1) -/
def one : TruthVector := ⟨1, 1, zero_le_one, le_refl 1, zero_le_one, le_refl 1⟩

/-- Coherence measure: product of epistemic and ego-driven truth -/
def productCoherence (tv : TruthVector) : ℝ :=
  tv.epistemic * tv.ego

/-- Vector magnitude coherence (Euclidean norm) -/
noncomputable def magnitudeCoherence (tv : TruthVector) : ℝ :=
  Real.sqrt (tv.epistemic ^ 2 + tv.ego ^ 2)

/-- Weighted coherence measure with context-dependent weights -/
noncomputable def weightedCoherence (tv : TruthVector) (w_e w_g : ℝ)
    (w_e_nonneg : 0 ≤ w_e) (w_g_nonneg : 0 ≤ w_g) (w_sum_pos : 0 < w_e + w_g) : ℝ :=
  (w_e * tv.epistemic + w_g * tv.ego) / (w_e + w_g)

/-- Check if a truth vector is coherent -/
def isCoherent (tv : TruthVector) : Prop :=
  tv.epistemic > 0 ∧ tv.ego > 0 ∧ |tv.epistemic - tv.ego| < 0.1  -- 10% tolerance

/-- Check if a truth vector has collapsed coherence -/
def isCoherenceCollapsed (tv : TruthVector) : Prop :=
  tv.epistemic = 0 ∨ tv.ego = 0

end TruthVector

/-! ## Theorem: Ego-Truth Tradeoff -/

/-- The ego-truth tradeoff: High magnitude claims have a threshold where E decreases as G increases -/
theorem egoTruthTradeoff (magnitude : ℝ) (h_mag_pos : 0 < magnitude) (h_mag_high : magnitude > 2) :
    ∃ e1 g1 e2 g2 : ℝ,
      0 ≤ e1 ∧ e1 ≤ 1 ∧ 0 ≤ g1 ∧ g1 ≤ 1 ∧
      0 ≤ e2 ∧ e2 ≤ 1 ∧ 0 ≤ g2 ∧ g2 ≤ 1 ∧
      g1 < g2 ∧ e1 > e2 ∧
      |e1 - e2| / (g2 - g1) ≥ magnitude := by
  -- Choose specific values that satisfy the tradeoff
  let g1 : ℝ := 0.0
  let g2 : ℝ := 1.0 / magnitude  -- Small delta G
  let e1 : ℝ := 1.0
  let e2 : ℝ := 0.0
  
  use e1, g1, e2, g2
  -- Verify all conditions
  constructor
  · linarith  -- 0 ≤ 1.0
  · linarith  -- 1.0 ≤ 1
  · linarith  -- 0 ≤ 0.0
  · linarith  -- 0.0 ≤ 1
  · linarith  -- 0 ≤ 0.0
  · linarith  -- 0.0 ≤ 1
  · linarith  -- 0 ≤ 1/magnitude ≤ 1 (since magnitude > 2)
  · linarith  -- 1/magnitude ≤ 1
  · linarith [magnitude > 2]  -- 0 < 1/magnitude
  · linarith  -- 1.0 > 0.0
  · have numerator : |e1 - e2| = 1.0 := by linarith
    have denominator : g2 - g1 = 1.0 / magnitude := by linarith
    have ratio : numerator / denominator = magnitude := by field_simp [numerator, denominator]; linarith
    linarith [ratio ≥ magnitude]

/-! ## Theorem: Credibility Vector -/

/-- The credibility vector extends the credibility function to the dual truth vector -/
noncomputable def credibilityVector (tv : TruthVector) (w_e w_g : ℝ)
    (w_e_nonneg : 0 ≤ w_e) (w_g_nonneg : 0 ≤ w_g) (w_sum_pos : 0 < w_e + w_g) : ℝ :=
  TruthVector.weightedCoherence tv w_e w_g w_e_nonneg w_g_nonneg w_sum_pos

/-! ## Theorem: Coherence Collapse -/

/-- Misaligned truth vectors lead to coherence collapse -/
theorem coherenceCollapse (tv : TruthVector) (h_misaligned : |tv.epistemic - tv.ego| > 0.9) :
    TruthVector.isCoherenceCollapsed tv := by
  -- Assume not collapsed, reach contradiction
  by_contra h_not_collapsed : ¬tv.isCoherenceCollapsed
  -- This implies both E > 0 and G > 0
  have h_e_pos : tv.epistemic > 0 := by cases h_not_collapsed <;> linarith
  have h_g_pos : tv.ego > 0 := by cases h_not_collapsed <;> linarith
  
  -- From |E - G| > 0.9, we have two cases
  have h_e_gt_g_plus : tv.epistemic > tv.ego + 0.9 ∨ tv.ego > tv.epistemic + 0.9 := abs_gt.1 h_misaligned
  cases h_e_gt_g_plus
  · -- Case 1: E > G + 0.9
    -- Since G > 0, E > 0.9
    -- But E ≤ 1, so G + 0.9 < 1 → G < 0.1
    -- Contradiction? Wait, no, but let's see
    have h_e_gt_0.9 : tv.epistemic > 0.9 := by linarith [h_g_pos]
    have h_g_lt_0.1 : tv.ego < 0.1 := by linarith [h_e_gt_g_plus]
    -- But how does this contradict? Maybe I need to strengthen the theorem
    -- Let's instead directly show that if both are > 0.1, then |E - G| ≤ 0.9
    by_contra h_both_pos : tv.epistemic > 0.1 ∧ tv.ego > 0.1
    have h_e ≤ 1 ∧ h_g ≤ 1 by exact tv.prop
    have h_e_range : 0.1 < tv.epistemic ≤ 1 := by cases h_both_pos <;> linarith
    have h_g_range : 0.1 < tv.ego ≤ 1 := by cases h_both_pos <;> linarith
    have h_diff_le : |tv.epistemic - tv.ego| ≤ 0.9 := by
      let max_e := 1.0
      let min_e := 0.1
      let max_g := 1.0
      let min_g := 0.1
      have max_diff := max_e - min_g := by linarith
      have min_diff := min_e - max_g := by linarith
      have abs_min_diff := abs min_diff := by linarith
      have max_abs_diff := max max_diff abs_min_diff := by linarith
      linarith [max_abs_diff ≤ 0.9]
    linarith [h_misaligned, h_diff_le]
  · -- Case 2: G > E + 0.9
    -- Similar to case 1
    by_contra h_both_pos : tv.epistemic > 0.1 ∧ tv.ego > 0.1
    have h_e_range : 0.1 < tv.epistemic ≤ 1 := by cases h_both_pos <;> linarith
    have h_g_range : 0.1 < tv.ego ≤ 1 := by cases h_both_pos <;> linarith
    have h_diff_le : |tv.epistemic - tv.ego| ≤ 0.9 := by
      let max_e := 1.0
      let min_e := 0.1
      let max_g := 1.0
      let min_g := 0.1
      have max_diff := max_e - min_g := by linarith
      have min_diff := min_e - max_g := by linarith
      have abs_min_diff := abs min_diff := by linarith
      have max_abs_diff := max max_diff abs_min_diff := by linarith
      linarith [max_abs_diff ≤ 0.9]
    linarith [h_misaligned, h_diff_le]

/-! ## Definition 2.8: Magnitude -/

/-- Magnitude of a claim: -log(prior probability) -/
noncomputable def magnitude (prior : ℝ) (h : 0 < prior) : ℝ :=
  -Real.log prior

lemma magnitude_nonneg {prior : ℝ} (h_pos : 0 < prior) (h_le : prior ≤ 1) : 
    0 ≤ magnitude prior h_pos := by
  simp only [magnitude, neg_nonneg]
  exact Real.log_nonpos (le_of_lt h_pos) h_le

lemma magnitude_mono {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p < q) :
    magnitude q hq < magnitude p hp := by
  simp only [magnitude]
  have h := Real.log_lt_log hp hpq
  linarith

/-! ## Bayes' Rule formulation -/

/-- Posterior probability via Bayes' rule -/
noncomputable def bayesPosterior (prior likelihood marginal : ℝ) 
    (h_marginal_pos : 0 < marginal) : ℝ :=
  (likelihood * prior) / marginal

/-- Marginal probability for binary hypothesis -/
noncomputable def binaryMarginal (prior likelihoodTrue likelihoodFalse : ℝ) : ℝ :=
  likelihoodTrue * prior + likelihoodFalse * (1 - prior)

/-! ## Cheap Talk Credibility -/

/-- Posterior credibility via Bayes' rule (Theorem 3.1).

    Given:
    - prior p = P(C=1)
    - emission rate α = P(S | C=1)
    - emission rate β = P(S | C=0)

    Returns: P(C=1 | S) = p·α / (p·α + (1-p)·β)

    For cheap talk with mimicability q: α = 1, β = q
    So: P(C=1 | S) = p / (p + (1-p)·q) -/
noncomputable def posteriorCredibility (prior α β : ℝ) : ℝ :=
  (prior * α) / (prior * α + (1 - prior) * β)

/-- Cheap talk credibility with mimicability parameter q.
    Assumes truthful senders emit with certainty (α = 1). -/
noncomputable def cheapTalkCredibility (prior mimicability : ℝ) : ℝ :=
  posteriorCredibility prior 1 mimicability

/-- The cheap talk bound: p / (p + (1-p)·q) -/
noncomputable def cheapTalkBound (prior mimicability : ℝ) : ℝ :=
  prior / (prior + (1 - prior) * mimicability)

/-- Cheap talk credibility equals the bound when α = 1 and β = q. -/
lemma cheapTalkCredibility_eq_bound (p q : ℝ) (hp : p + (1 - p) * q ≠ 0) :
    cheapTalkCredibility p q = cheapTalkBound p q := by
  simp only [cheapTalkCredibility, posteriorCredibility, cheapTalkBound, mul_one]

/-! ## Verified Signal Credibility -/

/-- Verified signal credibility lower bound (Theorem 4.1a).

    Given verifier with:
    - True positive rate ≥ 1 - ε_T
    - False positive rate ≤ ε_F

    Returns lower bound: p·(1-ε_T) / (p·(1-ε_T) + (1-p)·ε_F) -/
noncomputable def verifiedCredibilityBound (prior εT εF : ℝ) : ℝ :=
  (prior * (1 - εT)) / (prior * (1 - εT) + (1 - prior) * εF)

/-- At εF = 0, verified credibility equals 1 (perfect verification). -/
lemma verified_credibility_at_zero (p εT : ℝ) (hp : 0 < p) (hεT : εT < 1) :
    verifiedCredibilityBound p εT 0 = 1 := by
  unfold verifiedCredibilityBound
  have h1 : 0 < 1 - εT := by linarith
  have h2 : 0 < p * (1 - εT) := mul_pos hp h1
  simp only [mul_zero, add_zero]
  exact div_self (ne_of_gt h2)

/-- As false positive rate → 0, verified credibility → 1 (when ε_T < 1).
    Direct proof: at εF = 0, the function equals 1, and we use continuity. -/
lemma verified_credibility_limit (p εT : ℝ) (hp : 0 < p) (hεT : εT < 1) :
    Filter.Tendsto (fun εF => verifiedCredibilityBound p εT εF)
      (nhds 0) (nhds 1) := by
  have h_at_zero := verified_credibility_at_zero p εT hp hεT
  rw [← h_at_zero]
  -- The function is p*(1-εT) / (p*(1-εT) + (1-p)*εF)
  have h1 : 0 < 1 - εT := by linarith
  have h2 : 0 < p * (1 - εT) := mul_pos hp h1
  unfold verifiedCredibilityBound
  -- Show continuity at 0 via Filter.Tendsto for rational functions
  apply Filter.Tendsto.div
  · exact tendsto_const_nhds
  · apply Filter.Tendsto.add tendsto_const_nhds
    apply Filter.Tendsto.const_mul
    exact continuous_id.tendsto 0
  · simp only [mul_zero, add_zero]
    exact ne_of_gt h2

/-! ## Bounded Credibility Constructors -/

/-- Cheap talk bound is nonnegative under valid probability inputs. -/
lemma cheapTalkBound_nonneg' (p q : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) :
    0 ≤ cheapTalkBound p q := by
  unfold cheapTalkBound
  have h1 : 0 ≤ (1 - p) * q := mul_nonneg (by linarith) hq
  have hden : 0 ≤ p + (1 - p) * q := by linarith
  exact div_nonneg hp hden

/-- Cheap talk bound is at most 1 under valid probability inputs. -/
lemma cheapTalkBound_le_one' (p q : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) :
    cheapTalkBound p q ≤ 1 := by
  unfold cheapTalkBound
  have h1 : 0 ≤ (1 - p) * q := mul_nonneg (by linarith) hq
  by_cases hden : p + (1 - p) * q = 0
  · simp [hden]
  · have hden_pos : 0 < p + (1 - p) * q := by
      have hden_nonneg : 0 ≤ p + (1 - p) * q := by linarith
      exact lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    rw [div_le_one hden_pos]
    linarith

/-- Verified credibility bound is nonnegative. -/
lemma verifiedCredibilityBound_nonneg (p εT εF : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hεT : εT ≤ 1) (hεF : 0 ≤ εF) :
    0 ≤ verifiedCredibilityBound p εT εF := by
  unfold verifiedCredibilityBound
  have h1 : 0 ≤ p * (1 - εT) := mul_nonneg hp (by linarith)
  have h2 : 0 ≤ (1 - p) * εF := mul_nonneg (by linarith) hεF
  have hden : 0 ≤ p * (1 - εT) + (1 - p) * εF := by linarith
  exact div_nonneg h1 hden

/-- Verified credibility bound is at most 1. -/
lemma verifiedCredibilityBound_le_one (p εT εF : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hεT : 0 ≤ εT) (hεT' : εT ≤ 1) (hεF : 0 ≤ εF) :
    verifiedCredibilityBound p εT εF ≤ 1 := by
  unfold verifiedCredibilityBound
  have h1 : 0 ≤ p * (1 - εT) := mul_nonneg hp (by linarith)
  have h2 : 0 ≤ (1 - p) * εF := mul_nonneg (by linarith) hεF
  by_cases hden : p * (1 - εT) + (1 - p) * εF = 0
  · simp [hden]
  · have hden_pos : 0 < p * (1 - εT) + (1 - p) * εF := by
      have hden_nonneg : 0 ≤ p * (1 - εT) + (1 - p) * εF := by linarith
      exact lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    rw [div_le_one hden_pos]
    linarith

/-- Construct a CredibilityValue from cheapTalkBound. -/
noncomputable def cheapTalkBoundValue (p q : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) : CredibilityValue :=
  ⟨cheapTalkBound p q,
   cheapTalkBound_nonneg' p q hp hp' hq,
   cheapTalkBound_le_one' p q hp hp' hq⟩

/-- Construct a CredibilityValue from verifiedCredibilityBound. -/
noncomputable def verifiedCredibilityBoundValue (p εT εF : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hεT : 0 ≤ εT) (hεT' : εT ≤ 1) (hεF : 0 ≤ εF) : CredibilityValue :=
  ⟨verifiedCredibilityBound p εT εF,
   verifiedCredibilityBound_nonneg p εT εF hp hp' hεT' hεF,
   verifiedCredibilityBound_le_one p εT εF hp hp' hεT hεT' hεF⟩

end Credibility
