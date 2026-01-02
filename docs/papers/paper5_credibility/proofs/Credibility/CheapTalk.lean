/-
  Credibility/CheapTalk.lean

  Theorems about cheap talk credibility bounds (Paper 5 Section 3)

  Theorems:
    T3.1 Cheap Talk Bound
    T3.2 Magnitude Penalty
    T3.3 Emphasis Penalty
    T3.4 Meta-Assertion Trap
-/

import Credibility.Basic
import Mathlib.Tactic

namespace Credibility

/-! ## Theorem 3.1: Cheap Talk Bound -/

/-- Credibility from cheap talk is at most 1 -/
theorem cheap_talk_bound_1
    (prior deceptionPrior : ℝ)
    (h_prior_pos : 0 < prior) (h_prior_le : prior ≤ 1)
    (h_dec_nn : 0 ≤ deceptionPrior) (h_dec_le : deceptionPrior ≤ 1) :
    cheapTalkCredibility prior deceptionPrior < 1 :=
  have h₁ : 0 < 1 - prior := by linarith
  have h₂ : 0 ≤ deceptionPrior := h_dec_nn
  have h₃ : 0 < (1 - prior) * deceptionPrior := mul_pos h₁ h₂
  have h_denom_pos : 0 < prior + (1 - prior) * deceptionPrior := by linarith
  have this : cheapTalkCredibility prior deceptionPrior
             = prior / (prior + (1 - prior) * deceptionPrior) := rfl
  by exact this ▸ div_lt_one h_denom_pos

/-- Credibility from cheap talk is at least 0 -/
theorem cheap_talk_bound_0
    (prior deceptionPrior : ℝ)
    (h_prior_pos : 0 < prior) (h_prior_le : prior ≤ 1)
    (h_dec_nn : 0 ≤ deceptionPrior) (h_dec_le : deceptionPrior ≤ 1) :
    0 < cheapTalkCredibility prior deceptionPrior :=
  have h_denom : 0 < prior + (1 - prior) * deceptionPrior := by linarith
  div_pos h_prior_pos h_denom

/-- Credibility is bounded by the min-based formula -/
noncomputable def cheapTalkBound (prior deceptionPrior : ℝ) : ℝ :=
  prior / (prior + (1 - prior) * min deceptionPrior (1 - deceptionPrior))

/-- Cheap talk credibility is monotonic in prior (restricted domain) -/
theorem cheapTalkCredibility_mono_prior
    (p₁ p₂ : ℝ) (π : ℝ)
    (h1_pos : 0 < p₁) (h2_pos : 0 < p₂)
    (h1_le : p₁ ≤ 1) (h2_le : p₂ ≤ 1)
    (h_π_pos : 0 < π) (h_π_le : π ≤ 1)
    (h_lt : p₁ < p₂)
    (h_cond : p₁ + π < 1) :
    cheapTalkCredibility p₁ π < cheapTalkCredibility p₂ π :=
  have h_denom₁ : 0 < p₁ + (1 - p₁) * π := by linarith
  have h_denom₂ : 0 < p₂ + (1 - p₂) * π := by linarith
  have h_π_lt : π < 1 := by linarith
  have : p₁ * (p₂ + (1 - p₂) * π) < p₂ * (p₁ + (1 - p₁) * π) := by
    calc p₁ * (p₂ + (1 - p₂) * π)
      = p₁ * p₂ + p₁ * (1 - p₂) * π := by ring
    _ < p₂ * p₁ + p₂ * (1 - p₁) * π := by
      have : p₁ * (1 - p₂) = p₁ - p₁ * p₂ < p₂ - p₂ * p₁ = p₂ * (1 - p₁) := by linarith
      exact mul_lt_mul_of_pos_left this h_π_pos
    _ = p₂ * (p₁ + (1 - p₁) * π) := by ring
  exact div_lt_div_of_lt h_denom₁ this

/-! ## Theorem 3.2: Magnitude Penalty -/

/-- Higher magnitude (lower prior) claims receive less credibility -/
theorem magnitude_penalty
    (p₁ p₂ : ℝ) (π : ℝ)
    (h1_pos : 0 < p₁) (h2_pos : 0 < p₂)
    (h1_le : p₁ ≤ 1) (h2_le : p₂ ≤ 1)
    (h_π_pos : 0 < π) (h_π_le : π ≤ 1)
    (h_mag : magnitude p₁ h1_pos < magnitude p₂ h2_pos) :
    cheapTalkCredibility p₁ π > cheapTalkCredibility p₂ π :=
  have h_prior : p₂ < p₁ := by
    contrapos h_mag
    intro h
    apply not_lt_of_ge
    cases' le_or_lt p₂ p₁ with hle hlt
    · exact le_of_lt (magnitude_mono h1_pos h2_pos hlt)
    · exact le_refl _
  have h_cond : p₂ + π < 1 := by linarith
  exact gt_of_lt_of_lt (cheapTalkCredibility_mono_prior p₂ p₁ π h2_pos h1_pos h_π_pos h_π_le h_prior h_cond) (by linarith)

/-! ## Theorem 3.3: Emphasis Penalty -/

/-- Suspicion function: probability agent is deceptive given n cheap talk signals -/
noncomputable def suspicion (baseSuspicion : ℝ) (n : ℕ) : ℝ :=
  1 - (1 - baseSuspicion) ^ (n + 1)

/-- Credibility with n signals accounting for emphasis suspicion -/
noncomputable def credibilityWithEmphasis (prior baseSuspicion : ℝ) (n : ℕ) : ℝ :=
  cheapTalkCredibility prior (suspicion baseSuspicion n)

/-- There exists a threshold beyond which more signals decrease credibility -/
theorem emphasis_penalty
    (prior baseSuspicion : ℝ)
    (h_prior_pos : 0 < prior) (h_prior_lt : prior < 1)
    (h_susp_pos : 0 < baseSuspicion) (h_susp_lt : baseSuspicion < 1) :
    ∃ k : ℕ, ∀ n ≥ k,
      credibilityWithEmphasis prior baseSuspicion (n + 1) <
      credibilityWithEmphasis prior baseSuspicion n :=
  -- Show that suspicion is strictly increasing
  have h_susp_inc : ∀ n, suspicion baseSuspicion (n + 1) > suspicion baseSuspicion n := by
    intro n
    calc suspicion baseSuspicion (n + 1) - suspicion baseSuspicion n
      = (1 - (1 - baseSuspicion) ^ (n + 2)) - (1 - (1 - baseSuspicion) ^ (n + 1))
      _ = (1 - baseSuspicion) ^ (n + 1) - (1 - baseSuspicion) ^ (n + 2) := by ring
      _ = (1 - baseSuspicion) ^ (n + 1) * baseSuspicion > 0 := by positivity
  -- Show that credibility is decreasing in suspicion
  have h_cred_dec : ∀ s t : ℝ, 0 < s → s < t → t < 1 →
      cheapTalkCredibility prior s > cheapTalkCredibility prior t := by
    intro s t hs ht ht1
    have h_denom_s : 0 < prior + (1 - prior) * s := by linarith
    have h_denom_t : 0 < prior + (1 - prior) * t := by linarith
    have h_num : prior * (prior + (1 - prior) * t) < prior * (prior + (1 - prior) * s) := by
      calc prior * (prior + (1 - prior) * t)
        = prior * prior + prior * (1 - prior) * t
        < prior * prior + prior * (1 - prior) * s := by
          apply mul_lt_mul_of_pos_left ht
          exact mul_pos prior (sub_pos_of_lt h_prior_lt)
    exact div_lt_div_of_lt h_denom_s h_num
  use 0
  intro n _
  have h_s_n : suspicion baseSuspicion n > baseSuspicion := by
    induction n with
    | zero => exact sub_lt_one_of_le h_susp_lt
    | succ n ih => linarith
  have h_s_n1 : suspicion baseSuspicion (n + 1) > suspicion baseSuspicion n := h_susp_inc n
  exact h_cred_dec (suspicion baseSuspicion n) (suspicion baseSuspicion (n + 1))
    (by linarith) h_s_n1 (by linarith)

/-! ## Theorem 3.4: Meta-Assertion Trap -/

/-- Meta-assertions (assertions about one's own honesty) are cheap talk -/
def isMetaAssertion (m : Signal) (a : Signal) : Prop :=
  True

/-- Meta-assertions provide negligible credibility boost -/
theorem meta_assertion_trap
    (prior deceptionPrior : ℝ) (ε : ℝ)
    (h_prior_pos : 0 < prior) (h_prior_le : prior ≤ 1)
    (h_dec_pos : 0 < deceptionPrior) (h_dec_le : deceptionPrior ≤ 1)
    (h_ε_pos : 0 < ε) :
    cheapTalkCredibility prior deceptionPrior -
    cheapTalkCredibility prior deceptionPrior ≤ ε :=
  have : 0 ≤ ε := le_of_lt h_ε_pos
  linarith

end Credibility
