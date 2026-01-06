/-
  Credibility/Leverage.lean

  Lightweight leverage results compatible with the simplified credibility model.
-/

import Credibility.Basic
import Credibility.CheapTalk
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Credibility

/-- Leverage: impact per unit effort. -/
noncomputable def leverage (impact effort : ℝ) (h_effort_pos : 0 < effort) : ℝ :=
  impact / effort

/-- Credibility impact from cheap talk (simplified model). -/
noncomputable def cheapTalkImpact (prior deceptionPrior : ℝ) : ℝ :=
  cheapTalkCredibility prior deceptionPrior - prior

/-- Effort is word count (proxy for text length). -/
def wordCount (text : String) : ℕ :=
  (text.splitOn " ").length

/-- Credibility leverage for text-based signals. -/
noncomputable def credibilityLeverage
    (prior deceptionPrior : ℝ) (text : String)
    (h_words : 0 < wordCount text) : ℝ :=
  leverage (cheapTalkImpact prior deceptionPrior) (wordCount text) (by exact Nat.cast_pos.mpr h_words)

/-- For nonnegative impact, leverage weakens as effort grows. -/
theorem leverage_inverse_effort
    {impact e₁ e₂ : ℝ}
    (h_imp : 0 ≤ impact) (h1_pos : 0 < e₁) (h2_pos : 0 < e₂)
    (h_le : e₁ ≤ e₂) :
    leverage impact e₁ h1_pos ≥ leverage impact e₂ h2_pos := by
  have h_inv : 1 / e₂ ≤ 1 / e₁ := one_div_le_one_div_of_le h1_pos h_le
  have h := mul_le_mul_of_nonneg_left h_inv h_imp
  simpa [leverage, div_eq_mul_inv] using h

/-- Credibility leverage is maximized by minimizing word count (when impact is nonnegative).
    Note: This holds when cheap talk increases or maintains credibility. -/
theorem credibility_leverage_minimization
    (prior deceptionPrior : ℝ)
    (t₁ t₂ : String)
    (h1_pos : 0 < wordCount t₁) (h2_pos : 0 < wordCount t₂)
    (h_words : wordCount t₁ ≤ wordCount t₂)
    (h_nonneg : posteriorCredibility prior 1 deceptionPrior ≥ prior) :
    credibilityLeverage prior deceptionPrior t₁ h1_pos ≥
    credibilityLeverage prior deceptionPrior t₂ h2_pos := by
  unfold credibilityLeverage cheapTalkImpact leverage
  simp only [cheapTalkCredibility]
  have h1_cast : (0 : ℝ) < wordCount t₁ := Nat.cast_pos.mpr h1_pos
  have h2_cast : (0 : ℝ) < wordCount t₂ := Nat.cast_pos.mpr h2_pos
  have h_words_cast : (wordCount t₁ : ℝ) ≤ wordCount t₂ := Nat.cast_le.mpr h_words
  have h_numer : posteriorCredibility prior 1 deceptionPrior - prior ≥ 0 := by linarith
  -- Numerator is nonnegative, so dividing by larger denominator gives smaller result
  rw [ge_iff_le, div_le_div_iff₀ h2_cast h1_cast]
  exact mul_le_mul_of_nonneg_left h_words_cast h_numer

/-- Shorter text achieves at least as much leverage as longer text (when impact is nonnegative). -/
theorem brevity_principle
    (prior deceptionPrior : ℝ)
    (short long : String)
    (h_short_pos : 0 < wordCount short)
    (h_long_pos : 0 < wordCount long)
    (h_shorter : wordCount short ≤ wordCount long)
    (h_nonneg : posteriorCredibility prior 1 deceptionPrior ≥ prior) :
    credibilityLeverage prior deceptionPrior short h_short_pos ≥
    credibilityLeverage prior deceptionPrior long h_long_pos := by
  exact credibility_leverage_minimization prior deceptionPrior short long
    h_short_pos h_long_pos h_shorter h_nonneg

end Credibility
