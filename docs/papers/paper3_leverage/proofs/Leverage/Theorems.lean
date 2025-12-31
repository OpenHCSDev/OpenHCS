/-
# Leverage-Driven Software Architecture - Main Theorems

This module proves the main results connecting leverage to error probability
and architectural optimality.

Key theorems:
- 3.1: Leverage-Error Tradeoff (max leverage ⟹ min error)
- 3.2: Metaprogramming Dominance (unbounded leverage)
- 3.4: Architectural Decision Criterion
- 3.6: Leverage Composition

All proofs are definitional - no sorry placeholders.

Author: Formalized for Paper 3
Date: 2025-12-30
-/

import Leverage.Foundations
import Leverage.Probability

namespace Leverage

/-!
## Theorem 3.1: Leverage-Error Tradeoff

For fixed capabilities, maximizing leverage minimizes error probability.
This is the central theorem connecting the leverage framework to error reduction.
-/

/-- Theorem 3.1: Leverage-Error Tradeoff
    For fixed capability set, maximizing leverage minimizes error probability -/
theorem leverage_error_tradeoff (a₁ a₂ : Architecture) (p : ErrorRate)
    (h_same_caps : a₁.capabilities = a₂.capabilities)
    (h_higher_leverage : a₁.higher_leverage a₂)
    (h_p : p.numerator > 0) :
    expected_errors_lt (expected_errors a₁ p) (expected_errors a₂ p) := by
  -- Higher leverage with same caps means lower DOF
  unfold Architecture.higher_leverage at h_higher_leverage
  rw [h_same_caps] at h_higher_leverage
  -- a₁.dof < a₂.dof (since caps equal and a₁.caps * a₂.dof > a₂.caps * a₁.dof)
  have h_dof : a₁.dof < a₂.dof := Nat.lt_of_mul_lt_mul_left h_higher_leverage
  exact lower_dof_lower_errors a₁ a₂ p h_dof h_p

/-- Corollary: For fixed capabilities, minimum DOF = maximum leverage -/
theorem min_dof_max_leverage (a₁ a₂ : Architecture)
    (h_same_caps : a₁.capabilities = a₂.capabilities)
    (h_dof : a₁.dof < a₂.dof)
    (h_caps_pos : a₁.capabilities > 0) :
    a₁.higher_leverage a₂ :=
  lower_dof_higher_leverage a₁ a₂ h_same_caps h_dof h_caps_pos

/-!
## Theorem 3.2: Metaprogramming Dominance

Metaprogramming (DOF=1, unlimited capabilities) achieves unbounded leverage.
-/

/-- Metaprogramming architecture: DOF = 1, capabilities can grow arbitrarily -/
def MetaprogrammingArchitecture (caps : Nat) : Architecture where
  dof := 1
  capabilities := caps
  dof_pos := by decide

/-- Theorem 3.2: Metaprogramming achieves unbounded leverage -/
theorem metaprogramming_unbounded_leverage :
    ∀ target_leverage : Nat, ∃ caps : Nat,
      let m := MetaprogrammingArchitecture caps
      m.capabilities ≥ target_leverage := fun target =>
  ⟨target, Nat.le_refl target⟩

/-- Metaprogramming dominates any fixed-capability architecture -/
theorem metaprogramming_dominates (a : Architecture) (caps : Nat) (h : caps ≥ a.capabilities) :
    let m := MetaprogrammingArchitecture caps
    m.geq_leverage a := by
  unfold Architecture.geq_leverage MetaprogrammingArchitecture
  simp
  -- caps * a.dof ≥ a.capabilities * 1
  have h1 : caps * a.dof ≥ a.capabilities * a.dof := Nat.mul_le_mul_right a.dof h
  have h2 : a.capabilities * a.dof ≥ a.capabilities * 1 := Nat.mul_le_mul_left a.capabilities a.dof_pos
  omega

/-!
## Theorem 3.4: Architectural Decision Criterion

Optimal architecture maximizes leverage while satisfying requirements.
-/

/-- Definition: Architecture is optimal if it has maximum leverage for its capabilities -/
def optimal (a : Architecture) : Prop :=
  ∀ a' : Architecture, a'.capabilities = a.capabilities → a.dof ≤ a'.dof

/-- Theorem 3.4: Optimal architecture minimizes error -/
theorem optimal_minimizes_error (a : Architecture) (p : ErrorRate) (h : optimal a) :
    ∀ a' : Architecture, a'.capabilities = a.capabilities →
      expected_errors_le (expected_errors a p) (expected_errors a' p) := by
  intro a' h_caps
  have h_dof := h a' h_caps
  unfold expected_errors_le expected_errors
  simp
  exact Nat.mul_le_mul_right p.denominator (Nat.mul_le_mul_right p.numerator h_dof)

/-- SSOT is optimal -/
theorem ssot_is_optimal (a : Architecture) (h : a.is_ssot) : optimal a := by
  unfold optimal Architecture.is_ssot at *
  intro a' _
  rw [h]
  exact a'.dof_pos

/-!
## Theorem 3.6: Leverage Composition

For modular architecture, combined leverage depends on component leverages.
-/

/-- Theorem 3.6: Composition DOF is additive -/
theorem composition_dof_additive (a₁ a₂ : Architecture) :
    (a₁.compose a₂).dof = a₁.dof + a₂.dof := rfl

/-- Theorem: Composition capabilities are additive -/
theorem composition_caps_additive (a₁ a₂ : Architecture) :
    (a₁.compose a₂).capabilities = a₁.capabilities + a₂.capabilities := rfl

/-- Theorem: If both components have leverage ≥ 1, composition does too -/
theorem composition_preserves_leverage_bound (a₁ a₂ : Architecture)
    (h₁ : a₁.capabilities ≥ a₁.dof)
    (h₂ : a₂.capabilities ≥ a₂.dof) :
    (a₁.compose a₂).capabilities ≥ (a₁.compose a₂).dof := by
  simp [Architecture.compose]
  omega

/-!
## SSOT Theorems
-/

/-- Theorem: SSOT (DOF=1) minimizes error for single structural fact -/
theorem ssot_minimizes_error (a_ssot a_other : Architecture) (p : ErrorRate)
    (h₁ : a_ssot.is_ssot) (h₂ : a_other.dof ≥ 1) :
    expected_errors_le (expected_errors a_ssot p) (expected_errors a_other p) := by
  unfold Architecture.is_ssot at h₁
  unfold expected_errors_le expected_errors
  simp
  have : a_ssot.dof ≤ a_other.dof := by omega
  exact Nat.mul_le_mul_right p.denominator (Nat.mul_le_mul_right p.numerator this)

/-- Theorem: SSOT dominates non-SSOT with same capabilities -/
theorem ssot_dominates_non_ssot (a_ssot a_other : Architecture)
    (h₁ : a_ssot.is_ssot)
    (h₂ : a_other.dof > 1)
    (h_caps : a_ssot.capabilities = a_other.capabilities)
    (h_caps_pos : a_ssot.capabilities > 0) :
    a_ssot.higher_leverage a_other := by
  unfold Architecture.is_ssot at h₁
  have h_dof : a_ssot.dof < a_other.dof := by omega
  exact lower_dof_higher_leverage a_ssot a_other h_caps h_dof h_caps_pos

/-!
## Pareto Optimality
-/

/-- Definition: Pareto-optimal means no architecture dominates on all metrics -/
def pareto_optimal (a : Architecture) : Prop :=
  ¬∃ a' : Architecture,
    a'.capabilities ≥ a.capabilities ∧
    a'.dof < a.dof

/-- Theorem: SSOT is Pareto-optimal -/
theorem ssot_pareto_optimal (a : Architecture) (h : a.is_ssot) : pareto_optimal a := by
  unfold pareto_optimal Architecture.is_ssot at *
  intro ⟨a', _, h_dof⟩
  rw [h] at h_dof
  have : a'.dof ≥ 1 := a'.dof_pos
  omega

/-- Theorem: Optimal with maximum capabilities implies Pareto-optimal
    Note: This requires that a has maximum capabilities among all considered architectures -/
theorem optimal_max_caps_implies_pareto (a : Architecture) (h : optimal a)
    (h_max_caps : ∀ a' : Architecture, a'.capabilities ≤ a.capabilities) :
    pareto_optimal a := by
  unfold pareto_optimal optimal at *
  intro ⟨a', h_caps, h_dof⟩
  -- a' has caps ≥ a.caps, but also a' caps ≤ a caps (by h_max_caps)
  -- So a'.caps = a.caps
  have h_eq : a'.capabilities = a.capabilities := by
    have h1 := h_max_caps a'
    omega
  -- By optimal, a.dof ≤ a'.dof for equal caps
  have h_opt := h a' h_eq
  -- But h_dof says a'.dof < a.dof, contradiction
  omega

end Leverage
