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

/-- Credibility from cheap talk under rational deception model
    
    P(true | signal) = P(signal|true)·P(true) / P(signal)
    
    For cheap talk: P(signal|true) = 1, P(signal|false) = π_d
    Where π_d = probability deceptive agent sends signal -/
noncomputable def cheapTalkCredibility (prior deceptionPrior : ℝ) : ℝ :=
  prior / (prior + (1 - prior) * deceptionPrior)

end Credibility

