/-
  Credibility/Leverage.lean
  
  Leverage theory integration (Paper 5 Section 6)
  
  Theorems:
    T6.1 Credibility Leverage
-/

import Credibility.Basic
import Credibility.CheapTalk
import Mathlib.Tactic

namespace Credibility

/-! ## Leverage Definition -/

/-- Leverage: impact per unit effort -/
noncomputable def leverage (impact effort : ℝ) (h_effort_pos : 0 < effort) : ℝ :=
  impact / effort

/-- Credibility impact from cheap talk (bounded) -/
noncomputable def cheapTalkImpact (prior deceptionPrior : ℝ) : ℝ :=
  cheapTalkCredibility prior deceptionPrior - prior  -- Δ credibility

/-- Effort is word count (proxy for text length) -/
def wordCount (text : String) : ℕ := 
  (text.splitOn " ").length

/-- Credibility leverage for text-based signals -/
noncomputable def credibilityLeverage 
    (prior deceptionPrior : ℝ) (text : String) 
    (h_words : 0 < wordCount text) : ℝ :=
  leverage (cheapTalkImpact prior deceptionPrior) (wordCount text) (by exact Nat.cast_pos.mpr h_words)

/-! ## Theorem 6.1: Credibility Leverage Minimization -/

/-- For cheap talk, same impact means leverage ∝ 1/effort -/
theorem leverage_inverse_effort
    (impact : ℝ) (e₁ e₂ : ℝ) 
    (h1_pos : 0 < e₁) (h2_pos : 0 < e₂)
    (h_e_lt : e₁ < e₂) :
    leverage impact e₁ h1_pos > leverage impact e₂ h2_pos := by
  simp only [leverage]
  exact div_lt_div_of_pos_left (by linarith) h2_pos h_e_lt

/-- Credibility leverage is maximized by minimizing word count -/
theorem credibility_leverage_minimization
    (prior deceptionPrior : ℝ) 
    (t₁ t₂ : String)
    (h1_pos : 0 < wordCount t₁) (h2_pos : 0 < wordCount t₂)
    (h_words : wordCount t₁ < wordCount t₂) :
    credibilityLeverage prior deceptionPrior t₁ h1_pos > 
    credibilityLeverage prior deceptionPrior t₂ h2_pos := by
  simp only [credibilityLeverage]
  apply leverage_inverse_effort
  exact Nat.cast_lt.mpr h_words

/-! ## Corollary: Brevity Principle -/

/-- Shorter text achieves higher leverage -/
theorem brevity_principle
    (prior deceptionPrior : ℝ) 
    (short long : String)
    (h_short_pos : 0 < wordCount short)
    (h_long_pos : 0 < wordCount long)
    (h_shorter : wordCount short < wordCount long)
    (h_same_claim : True) :  -- Both express the same claim
    credibilityLeverage prior deceptionPrior short h_short_pos > 
    credibilityLeverage prior deceptionPrior long h_long_pos := by
  exact credibility_leverage_minimization prior deceptionPrior short long 
    h_short_pos h_long_pos h_shorter

end Credibility

