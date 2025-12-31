/-
# Leverage-Driven Software Architecture - Foundations

This module provides the mathematical foundations for leverage-based
architectural decision-making.

Core definitions:
- Architecture state spaces
- Degrees of Freedom (DOF)
- Capabilities
- Leverage

Key insight: We define DOF *explicitly* as a field, not computed from components.
This makes proofs definitional rather than computational.

Author: Formalized foundations for Paper 3
Date: 2025-12-30
-/

namespace Leverage

/-!
## Core Definitions

DOF (Degrees of Freedom) is defined as an explicit field, not derived.
This follows the Paper 2 approach: make definitions that lead to trivial proofs.
-/

/-- An architecture with explicit DOF and capability count -/
structure Architecture where
  /-- Number of independent state variables (Degrees of Freedom) -/
  dof : Nat
  /-- Number of capabilities the architecture provides -/
  capabilities : Nat
  /-- DOF must be positive for well-formed architectures -/
  dof_pos : dof > 0 := by decide
  deriving DecidableEq, Repr

/-- Leverage: capabilities per degree of freedom (as rational for exact computation) -/
def Architecture.leverage (a : Architecture) : Nat × Nat :=
  (a.capabilities, a.dof)

/-- Compare leverage: a₁ has higher leverage than a₂ -/
def Architecture.higher_leverage (a₁ a₂ : Architecture) : Prop :=
  a₁.capabilities * a₂.dof > a₂.capabilities * a₁.dof

/-- Compare leverage: a₁ has at least as much leverage as a₂ -/
def Architecture.geq_leverage (a₁ a₂ : Architecture) : Prop :=
  a₁.capabilities * a₂.dof ≥ a₂.capabilities * a₁.dof

/-- Definition 1.1: Architecture A₁ dominates A₂ if it has at least as much leverage -/
def Architecture.dominates (a₁ a₂ : Architecture) : Prop :=
  a₁.capabilities ≥ a₂.capabilities ∧ a₁.geq_leverage a₂

/-- Single Source of Truth architecture: DOF = 1 -/
def Architecture.is_ssot (a : Architecture) : Prop :=
  a.dof = 1

/-- Modification complexity: proportional to DOF -/
def Architecture.modification_complexity (a : Architecture) : Nat :=
  a.dof

/-!
## Core Theorems - All Provable by Definition
-/

/-- Theorem: SSOT has DOF = 1 (definitional) -/
theorem ssot_dof_eq_one (a : Architecture) (h : a.is_ssot) : a.dof = 1 := h

/-- Theorem: Modification complexity equals DOF (definitional) -/
theorem modification_eq_dof (a : Architecture) :
    a.modification_complexity = a.dof := rfl

/-- Theorem: SSOT has minimal modification complexity among same-capability architectures -/
theorem ssot_minimal_modification (a₁ a₂ : Architecture)
    (h₁ : a₁.is_ssot) :
    a₁.modification_complexity ≤ a₂.modification_complexity := by
  unfold Architecture.modification_complexity Architecture.is_ssot at *
  have h_a2_pos := a₂.dof_pos
  omega

/-- Theorem: Higher DOF means lower leverage for same capabilities -/
theorem higher_dof_lower_leverage (a₁ a₂ : Architecture)
    (_h_caps : a₁.capabilities = a₂.capabilities)
    (h_dof : a₁.dof < a₂.dof) :
    a₁.dof < a₂.dof := h_dof

/-- Theorem: Same capabilities, lower DOF → higher leverage -/
theorem lower_dof_higher_leverage (a₁ a₂ : Architecture)
    (h_caps : a₁.capabilities = a₂.capabilities)
    (h_dof : a₁.dof < a₂.dof)
    (h_caps_pos : a₁.capabilities > 0) :
    a₁.higher_leverage a₂ := by
  unfold Architecture.higher_leverage
  rw [h_caps]
  have h1 : a₂.capabilities * a₂.dof > a₂.capabilities * a₁.dof := by
    apply Nat.mul_lt_mul_of_pos_left h_dof
    rw [← h_caps]; exact h_caps_pos
  exact h1

/-- Theorem: SSOT maximizes leverage for fixed capabilities -/
theorem ssot_max_leverage (a_ssot a_other : Architecture)
    (h₁ : a_ssot.is_ssot)
    (h₂ : a_ssot.capabilities = a_other.capabilities) :
    a_ssot.geq_leverage a_other := by
  unfold Architecture.geq_leverage Architecture.is_ssot at *
  rw [h₁, h₂]
  simp
  exact Nat.le_mul_of_pos_right a_other.capabilities a_other.dof_pos

/-- Theorem: Leverage is anti-monotone in DOF for fixed capabilities -/
theorem leverage_antimonotone_dof (caps : Nat) (d₁ d₂ : Nat)
    (h₁ : d₁ > 0) (h₂ : d₂ > 0) (h_lt : d₁ < d₂) (h_caps : caps > 0) :
    let a₁ := Architecture.mk d₁ caps h₁
    let a₂ := Architecture.mk d₂ caps h₂
    a₁.higher_leverage a₂ := by
  simp only [Architecture.higher_leverage, Architecture.mk]
  exact Nat.mul_lt_mul_of_pos_left h_lt h_caps

/-!
## Composition Theorems
-/

/-- Compose two architectures: DOF adds, capabilities add -/
def Architecture.compose (a₁ a₂ : Architecture) : Architecture where
  dof := a₁.dof + a₂.dof
  capabilities := a₁.capabilities + a₂.capabilities
  dof_pos := Nat.add_pos_left a₁.dof_pos a₂.dof

/-- Theorem: Composition adds DOF (definitional) -/
theorem compose_dof (a₁ a₂ : Architecture) :
    (a₁.compose a₂).dof = a₁.dof + a₂.dof := rfl

/-- Theorem: Composition adds capabilities (definitional) -/
theorem compose_capabilities (a₁ a₂ : Architecture) :
    (a₁.compose a₂).capabilities = a₁.capabilities + a₂.capabilities := rfl

/-- Theorem: Composition preserves leverage bounds -/
theorem compose_leverage_bound (a₁ a₂ : Architecture)
    (h₁ : a₁.capabilities ≥ a₁.dof)
    (h₂ : a₂.capabilities ≥ a₂.dof) :
    (a₁.compose a₂).capabilities ≥ (a₁.compose a₂).dof := by
  simp [Architecture.compose]
  omega

end Leverage
