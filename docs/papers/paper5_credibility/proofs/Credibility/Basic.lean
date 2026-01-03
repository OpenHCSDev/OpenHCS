/-
  Credibility/Basic.lean
  
  Core definitions for credibility theory (Paper 5 Section 2)
  
  Definitions:
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

/-- Credibility of a claim given signals -/
def Credibility (Claim Signal : Type*) := Claim → List Signal → ℝ

/-! ## Definition 2.7: Deception Prior -/

/-- Probability that a random agent is deceptive -/
structure DeceptionPrior where
  π : ℝ
  π_nonneg : 0 ≤ π
  π_le_one : π ≤ 1

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

/-- Baseline precision used for cheap talk comparisons. -/
def baseline_precision : ℝ := 0

/-- A simple credibility scoring function; we treat precision directly as credibility. -/
def credibility (precision : ℝ) : ℝ := precision

/-- Credibility strictly increases with precision. -/
lemma strictMono_credibility : StrictMono credibility := by
  intro a b h
  simpa [credibility] using h

/-- A toy optimal precision derived from cost coefficients. -/
def optimal_precision_from_cost (c e : ℝ) : ℝ := c + e

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

end Credibility
