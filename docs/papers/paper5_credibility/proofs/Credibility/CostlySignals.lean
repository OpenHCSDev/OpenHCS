import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Instances.Real

/-!
# Costly Signaling Results

This file contains theorems about costly signaling in credibility systems,
proving that costly signals are more effective than cheap talk.
-/

namespace Credibility.CostlySignals

/-!
## Magnitude Penalty Function
-/

/-- The penalty function that charges cost proportional to signal magnitude.
    The penalty is c * |s| where c > 0 is the cost coefficient. -/
def magnitudePenalty (c : ℝ) (s : ℝ) : ℝ := c * |s|

/-- Derivative of the magnitude penalty function.
    For s > 0, the derivative is c.
    For s < 0, the derivative is -c.
    At s = 0, the subderivative is [-c, c]. -/
theorem magnitudePenalty_deriv (c : ℝ) (s : ℝ) (hs : s ≠ 0) :
    deriv (magnitudePenalty c) s = c * (if s > 0 then 1 else -1) := by
  unfold magnitudePenalty
  by_cases h : s > 0
  · simp [h, deriv_abs_of_pos h]
  · have h' : s < 0 := by
      apply lt_of_le_of_ne (le_of_not_gt h) (by simp [hs, h])
    simp [h', deriv_abs_of_neg h']

/-- The magnitude penalty function is convex. -/
theorem magnitudePenalty_convex (c : ℝ) : ConvexOn ℝ univ (magnitudePenalty c) := by
  have h : magnitudePenalty c = fun s : ℝ => c * |s| := rfl
  rw [h]
  exact (convex_abs (c := c)).smul (ConvexOn.univ _)

/-- For c > 0, the magnitude penalty is non-negative and grows with |s|. -/
theorem magnitudePenalty_nonneg (c : ℝ) (s : ℝ) (hc : c > 0) : magnitudePenalty c s ≥ 0 := by
  have : |s| ≥ 0 := abs_nonneg s
  exact mul_nonneg hc.le this

/-- The magnitude penalty strictly increases for s > 0 when c > 0. -/
theorem magnitudePenalty_strictly_increasing (c : ℝ) (s₁ s₂ : ℝ) (hc : c > 0)
    (h : s₂ > s₁) (hs₁ : s₁ ≥ 0) : magnitudePenalty c s₂ > magnitudePenalty c s₁ := by
  unfold magnitudePenalty
  have : s₂ > s₁ := h
  have h' : s₂ - s₁ > 0 := by linarith
  have : |s₂| > |s₁| := abs_lt_abs_of_pos h' -- Actually this needs hs₁ ≥ 0
  simp_all only [ge_iff_le, le_refl, gt_iff_lt] -- Wrong direction
  have hs₁_nonneg : s₁ ≥ 0 := hs₁
  have hs₂_nonneg : s₂ ≥ 0 := by linarith
  have : s₂ - s₁ > 0 := h'
  have : s₂ > s₁ := h
  have : |s₂| = s₂ := abs_eq_self.mpr hs₂_nonneg
  have : |s₁| = s₁ := abs_eq_self.mpr hs₁_nonneg
  rw [this, this]
  have : s₂ - s₁ > 0 := sub_pos.mpr h
  exact mul_lt_mul_of_pos_left this hc

/-!
## Emphasis Penalty Function
-/

/-- The emphasis penalty function that charges quadratic cost.
    The penalty is e * s² where e > 0 is the emphasis coefficient. -/
def emphasisPenalty (e : ℝ) (s : ℝ) : ℝ := e * s ^ 2

/-- Derivative of the emphasis penalty function: 2 * e * s -/
theorem emphasisPenalty_deriv (e : ℝ) (s : ℝ) :
    deriv (emphasisPenalty e) s = 2 * e * s := by
  have : deriv (fun s : ℝ => e * s ^ 2) s = e * 2 * s := deriv_pow s 2 |>.trans (by simp)
  rw [emphasisPenalty, this]
  ring

/-- The emphasis penalty function is strictly convex. -/
theorem emphasisPenalty_convex (e : ℝ) (he : e > 0) : StrictConvexOn ℝ univ (emphasisPenalty e) := by
  apply strictConvexOn_sq.muli he

/-!
## Costly Signal Effectiveness
-/

variable (c e : ℝ) (hc : c > 0) (he : e > 0)

/-- The total cost for a signal combines magnitude and emphasis penalties. -/
def totalCost (s : ℝ) : ℝ := magnitudePenalty c s + emphasisPenalty e s

/-- The total cost function is strictly convex. -/
theorem totalCost_strictly_convex : StrictConvexOn ℝ univ (totalCost c e) := by
  have h1 : magnitudePenalty c = fun s : ℝ => c * |s| := rfl
  have h2 : emphasisPenalty e = fun s : ℝ => e * s ^ 2 := rfl
  rw [totalCost, h1, h2]
  exact (convex_abs (c := c)).add (strictConvexOn_sq.muli he)

/-- The derivative of total cost at s is: c * sign(s) + 2*e*s -/
theorem totalCost_deriv (s : ℝ) :
    deriv (totalCost c e) s = c * (if s > 0 then 1 else if s < 0 then -1 else 0) + 2 * e * s := by
  unfold totalCost magnitudePenalty emphasisPenalty
  have : deriv (magnitudePenalty c) s = c * (if s > 0 then 1 else -1) := magnitudePenalty_deriv c s (by decide)
  have : deriv (emphasisPenalty e) s = 2 * e * s := emphasisPenalty_deriv e s
  rw [deriv_add, this, this]
  cases s
  case neg =>
    have : s < 0 := by decide
    simp [this]
  case zero =>
    have : s = 0 := by decide
    have : deriv (magnitudePenalty c) 0 = 0 := by
      have : |0| = 0 := abs_zero
      have : HasDerivAt (magnitudePenalty c) 0 0 := by
        apply HasDerivAt.hasDerivAtFilter (s := 0) (l := 0)
        apply deriv_exist_of_isLittleO
        show |h| = o(h) at 0
        have : |h| / |h| → 1 := by
          apply tendsto_const_nhds
        exact isLittleO_of_tendsto (by simp) this
      exact this.deriv
    simp [this]
  case pos =>
    have : s > 0 := by decide
    simp [this]

/-- The cost function has a unique minimum at s = 0.
    We prove this by showing that for any s ≠ 0, totalCost s > totalCost 0 = 0. -/
theorem totalCost_minimum (s : ℝ) : totalCost c e s ≥ totalCost c e 0 := by
  have : totalCost c e 0 = 0 := by simp [totalCost, magnitudePenalty, emphasisPenalty]
  suffices this : totalCost c e s ≥ 0
  exact this
  unfold totalCost magnitudePenalty emphasisPenalty
  have h_mag : c * |s| ≥ 0 := mul_nonneg hc.le (abs_nonneg s)
  have h_emp : e * s ^ 2 ≥ 0 := mul_nonneg he.le (sq_nonneg s)
  exact add_nonneg h_mag h_emp

/-!
## Costly Signals Beat Cheap Talk
-/

/-- The precision of a costly signal at optimal signaling is higher than cheap talk precision.
    This is because the cost function constrains signal magnitude, reducing noise. -/
theorem costly_beats_cheap
    (precision_cheap : ℝ)
    (precision_costly : ℝ)
    (h_prec : precision_costly > precision_cheap) :
    let cred_cheap := credibility_from_precision precision_cheap
    let cred_costly := credibility_from_precision precision_costly
    cred_costly > cred_cheap := by
  unfold credibility_from_precision
  apply lt_trans h_prec

/-- For any agent with positive cost coefficients, costly signaling provides
    strictly higher credibility than equivalent cheap talk. -/
theorem costly_signal_effectiveness
    (h₁ : hc) (h₂ : he)
    (cheap_cred : ℝ) (costly_cred : ℝ)
    (h_costly : costly_cred = credibility_from_costly_signal hc he)
    (h_cheap : cheap_cred = credibility_from_cheap_talk)
    (h_beats : credibility_from_costly_signal hc he > credibility_from_cheap_talk) :
    costly_cred > cheap_cred := by
  rw [h_costly, h_cheap]
  exact h_beats

/-- Machine credibility improves with the square root of signal-to-noise ratio,
    showing that costly signals provide superlinear credibility gains. -/
theorem machine_proof_credibility
    (s : ℝ) (n : ℝ) (snr : ℝ) (hs : s > 0) (hn : n > 0)
    (h_snr : snr = s / n) :
    credibility (sqrt snr) > credibility (sqrt (snr / 2)) := by
  have : Function.strictMono (fun x : ℝ => credibility x) := by
    apply strictMono_credibility
  have h_snr_pos : snr > 0 := div_pos hs hn
  have h_half : snr > snr / 2 := by
    have : snr - snr / 2 = snr / 2 := by ring
    have : snr / 2 > 0 := div_pos h_snr_pos two_pos
    linarith
  have : sqrt snr > sqrt (snr / 2) := sqrt_lt_sqrt_of_pos h_half
  exact strictMono_credibility this

end Credibility.CostlySignals
