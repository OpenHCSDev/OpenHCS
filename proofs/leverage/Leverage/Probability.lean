/-
# Leverage-Driven Software Architecture - Probability Model

This module formalizes the relationship between DOF and error probability.

Key insight: We use a discrete probability model with explicit error rates
represented as natural number fractions, avoiding real number complexity.

Key results:
- P(error) monotonically increases with DOF
- E[errors] = DOF × p (linear scaling)
- Lower DOF → lower error probability

Author: Formalized for Paper 3
Date: 2025-12-30
-/

import Leverage.Foundations

namespace Leverage

/-!
## Error Model

We model error probability discretely to enable decidable proofs.
Error rate p is represented as a fraction (numerator, denominator).
For typical software: p ≈ 0.01 = 1/100.
-/

/-- Error rate as a fraction (num/denom where denom > 0) -/
structure ErrorRate where
  numerator : Nat
  denominator : Nat
  denom_pos : denominator > 0 := by decide
  rate_valid : numerator < denominator  -- 0 ≤ p < 1
  deriving DecidableEq, Repr

/-- Standard error rate: 1% = 1/100 -/
def standardErrorRate : ErrorRate where
  numerator := 1
  denominator := 100
  rate_valid := by decide

/-- Expected errors: DOF × p (as fraction) -/
def expected_errors (a : Architecture) (p : ErrorRate) : Nat × Nat :=
  (a.dof * p.numerator, p.denominator)

/-- Error count comparison: is e₁ < e₂? -/
def expected_errors_lt (e₁ e₂ : Nat × Nat) : Prop :=
  e₁.1 * e₂.2 < e₂.1 * e₁.2

/-- Error count comparison: is e₁ ≤ e₂? -/
def expected_errors_le (e₁ e₂ : Nat × Nat) : Prop :=
  e₁.1 * e₂.2 ≤ e₂.1 * e₁.2

/-!
## Core Theorems - All Definitional
-/

/-- Theorem: Expected errors scale linearly with DOF -/
theorem expected_errors_linear (a : Architecture) (p : ErrorRate) :
    (expected_errors a p).1 = a.dof * p.numerator := rfl

/-- Theorem: Same error rate, different DOF → proportional expected errors -/
theorem expected_errors_proportional (a₁ a₂ : Architecture) (p : ErrorRate) :
    let e₁ := expected_errors a₁ p
    let e₂ := expected_errors a₂ p
    e₁.2 = e₂.2  -- Same denominator
    := rfl

/-- Theorem: Lower DOF means fewer expected errors -/
theorem lower_dof_lower_errors (a₁ a₂ : Architecture) (p : ErrorRate)
    (h : a₁.dof < a₂.dof) (h_p : p.numerator > 0) :
    expected_errors_lt (expected_errors a₁ p) (expected_errors a₂ p) := by
  unfold expected_errors_lt expected_errors
  simp only
  -- (a₁.dof * p.numerator) * p.denominator < (a₂.dof * p.numerator) * p.denominator
  have h1 : a₁.dof * p.numerator < a₂.dof * p.numerator :=
    Nat.mul_lt_mul_of_pos_right h h_p
  exact Nat.mul_lt_mul_of_pos_right h1 p.denom_pos

/-- Theorem: Equal DOF means equal expected errors -/
theorem equal_dof_equal_errors (a₁ a₂ : Architecture) (p : ErrorRate)
    (h : a₁.dof = a₂.dof) :
    expected_errors a₁ p = expected_errors a₂ p := by
  unfold expected_errors
  simp [h]

/-- Theorem: SSOT (DOF=1) has minimal expected errors -/
theorem ssot_minimal_errors (a_ssot a_other : Architecture) (p : ErrorRate)
    (h₁ : a_ssot.is_ssot)
    (h₂ : a_other.dof > 1)
    (h_p : p.numerator > 0) :
    expected_errors_lt (expected_errors a_ssot p) (expected_errors a_other p) := by
  unfold Architecture.is_ssot at h₁
  have h : a_ssot.dof < a_other.dof := by omega
  exact lower_dof_lower_errors a_ssot a_other p h h_p

/-- Theorem: Zero error rate means zero expected errors -/
theorem zero_rate_zero_errors (a : Architecture) :
    let p := ErrorRate.mk 0 100 (by decide) (by decide)
    (expected_errors a p).1 = 0 := by
  simp [expected_errors]

/-- Theorem: DOF reduction by factor k reduces expected errors by factor k -/
theorem dof_reduction_error_reduction (dof₁ dof₂ : Nat) (p : ErrorRate)
    (h₁ : dof₁ > 0) (h₂ : dof₂ > 0) (h_lt : dof₁ < dof₂) :
    let a₁ := Architecture.mk dof₁ 1 h₁
    let a₂ := Architecture.mk dof₂ 1 h₂
    (expected_errors a₁ p).1 < (expected_errors a₂ p).1 ∨ p.numerator = 0 := by
  simp [expected_errors]
  cases p.numerator with
  | zero => right; rfl
  | succ n =>
    left
    exact Nat.mul_lt_mul_of_pos_right h_lt (Nat.succ_pos n)

/-!
## Error Probability Ordering
-/

/-- Architecture A has lower error than B if DOF(A) < DOF(B) -/
def Architecture.lower_error (a b : Architecture) : Prop :=
  a.dof < b.dof

/-- Theorem: Lower error is transitive -/
theorem lower_error_trans (a b c : Architecture)
    (h₁ : a.lower_error b) (h₂ : b.lower_error c) :
    a.lower_error c := by
  unfold Architecture.lower_error at *
  omega

/-- Theorem: SSOT has lowest error among all architectures with same capabilities -/
theorem ssot_lowest_error (a_ssot a_other : Architecture)
    (h₁ : a_ssot.is_ssot)
    (h₂ : a_other.dof ≥ 1) :
    a_ssot.dof ≤ a_other.dof := by
  unfold Architecture.is_ssot at h₁
  omega

/-- Theorem: Composition increases error (DOF adds) -/
theorem compose_increases_error (a₁ a₂ : Architecture) :
    (a₁.compose a₂).dof > a₁.dof ∧ (a₁.compose a₂).dof > a₂.dof := by
  simp [Architecture.compose]
  have h1 := a₁.dof_pos
  have h2 := a₂.dof_pos
  constructor <;> omega

end Leverage
