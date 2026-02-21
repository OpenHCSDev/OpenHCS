/-
  SSOT Formalization - Information Theory: Entropy Foundations
  Paper 2: Formal Foundations for the Single Source of Truth Principle

  This file formalizes Shannon entropy for finite discrete distributions.
  It provides the foundation for information-theoretic arguments in paper2_it.

  Design principle: Handle edge cases explicitly (0 * log 0 = 0 convention)
  and use standard Mathlib definitions for real analysis.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
## Finite Probability Distributions

A finite probability distribution over n outcomes is a function from Fin n to ℝ
assigning non-negative probabilities that sum to 1.
-/

/-- Finite probability distribution over n outcomes -/
structure FiniteDist (n : ℕ) where
  prob : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ prob i
  sum_one : ∑ i, prob i = 1

namespace FiniteDist

/-- Support of a distribution: indices with positive probability -/
noncomputable def support {n : ℕ} (p : FiniteDist n) : Finset (Fin n) :=
  {i : Fin n | 0 < p.prob i}

/-- Cardinality of the support -/
noncomputable def supportSize {n : ℕ} (p : FiniteDist n) : ℕ :=
  p.support.card

/-- A distribution is deterministic if it has exactly one outcome with probability 1 -/
def isDeterministic {n : ℕ} (p : FiniteDist n) : Prop :=
  ∃ i₀ : Fin n, p.prob i₀ = 1 ∧ ∀ i ≠ i₀, p.prob i = 0

/-- Uniform distribution over n outcomes -/
noncomputable def uniform (n : ℕ) (hn : n > 0) : FiniteDist n where
  prob i := (1 : ℝ) / n
  nonneg i := by
    have h : 0 < (1 : ℝ) / n := by
      apply div_pos
      · norm_num
      · exact Nat.cast_pos.mpr hn
    exact le_of_lt h
  sum_one := by
    calc
      ∑ i : Fin n, (1 : ℝ) / n
      _ = (n : ℝ) * ((1 : ℝ) / n) := by
        rw [Finset.sum_const, Finset.card_fin]
      _ = 1 := by
        field_simp
        exact Nat.cast_ne_zero.mpr (Ne.symm (Nat.ne_of_gt hn))

end FiniteDist

/-!
## Shannon Entropy

Shannon entropy H(X) = -∑ p_i * log(p_i), where we use the convention
that 0 * log(0) = 0 (limit as p → 0⁺).
-/

/-- The term p * log(p) with the convention 0 * log(0) = 0 -/
noncomputable def entropyTerm (p : ℝ) : ℝ :=
  if p = 0 then 0 else p * Real.log p

/-- Shannon entropy of a finite distribution -/
noncomputable def entropy {n : ℕ} (p : FiniteDist n) : ℝ :=
  -∑ i, entropyTerm (p.prob i)

/-!
## Basic Properties of Entropy
-/

namespace Entropy

/-- Entropy is non-negative -/
theorem entropy_nonneg {n : ℕ} (p : FiniteDist n) : 0 ≤ entropy p := by
  sorry

/-- Entropy is bounded by log of support size -/
theorem entropy_le_log_card {n : ℕ} (p : FiniteDist n) :
    entropy p ≤ Real.log (p.supportSize : ℝ) := by
  sorry -- Proof uses Jensen's inequality for concave function -log

/-- Entropy of uniform distribution is log n -/
theorem entropy_uniform {n : ℕ} (hn : n > 0) :
    entropy (FiniteDist.uniform n hn) = Real.log n := by
  sorry

/-- Helper: entropyTerm is zero iff p = 0 or p = 1 -/
theorem entropyTerm_zero_iff (p : ℝ) : entropyTerm p = 0 ↔ p = 0 ∨ p = 1 := by
  sorry

/-- Entropy is zero iff distribution is deterministic -/
theorem entropy_zero_iff {n : ℕ} (p : FiniteDist n) :
    entropy p = 0 ↔ p.isDeterministic := by
  constructor
  · intro h_ent
    -- If H(p) = 0, then all entropy terms are zero
    -- This means each p.prob i is either 0 or 1
    -- Since sum is 1, exactly one has probability 1
    sorry
  · intro h_det
    -- If deterministic, exactly one outcome has probability 1, rest are 0
    -- Then entropy = -1*log(1) - 0*log(0) - ... = 0
    sorry

end Entropy
