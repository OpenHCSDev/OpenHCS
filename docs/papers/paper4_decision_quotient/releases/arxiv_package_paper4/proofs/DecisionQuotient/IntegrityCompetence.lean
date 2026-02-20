/-
  Paper 4: Decision Quotient

  IntegrityCompetence.lean

  Formalizes the Foundations-section split between:
  - Solver integrity (sound certified assertions)
  - Regime competence (integrity + non-abstaining coverage + resource bound)

  LaTeX references:
  - Definition: certifying solver / solver integrity / competence under regime
  - Proposition: Integrity--Competence Separation
-/

import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace DecisionQuotient.IntegrityCompetence

open Set

universe u v w

variable {X : Type u} {Y : Type v} {W : Type w}

/-- Regime tuple used by competence claims:
    in-scope instances, encoding length, and resource budget. -/
structure Regime (X : Type u) where
  inScope : Set X
  encLen : X → ℕ
  budget : ℕ → ℕ

/-- Certifying solver: may abstain, otherwise emits candidate output + witness,
    together with a checker and solve-side cost function. -/
structure CertifyingSolver (X : Type u) (Y : Type v) (W : Type w) where
  solve : X → Option (Y × W)
  check : X → Y → W → Prop
  solveCost : X → ℕ

/-- Solver integrity:
    1. Any asserted output must pass the checker.
    2. Any checker-accepted claim is semantically correct. -/
def SolverIntegrity (R : Set (X × Y)) (Q : CertifyingSolver X Y W) : Prop :=
  (∀ x y w, Q.solve x = some (y, w) → Q.check x y w) ∧
  (∀ x y w, Q.check x y w → (x, y) ∈ R)

/-- Competence under a declared regime:
    integrity + non-abstaining coverage on in-scope instances + solve-side budget. -/
def CompetentOn (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W) : Prop :=
  SolverIntegrity R Q ∧
  (∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w)) ∧
  (∀ x, x ∈ Γ.inScope → Q.solveCost x ≤ Γ.budget (Γ.encLen x))

/-- Competence implies integrity by definition. -/
theorem competence_implies_integrity
    (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W) :
    CompetentOn R Γ Q → SolverIntegrity R Q := by
  intro h
  exact h.1

/-- A canonical integrity-preserving abstaining solver:
    - Always abstains
    - Checker always rejects
    - Zero solve-side cost
-/
def alwaysAbstain : CertifyingSolver X Y W where
  solve := fun _ => none
  check := fun _ _ _ => False
  solveCost := fun _ => 0

/-- Always-abstain solver satisfies integrity for any target relation. -/
theorem alwaysAbstain_integrity (R : Set (X × Y)) :
    SolverIntegrity R (alwaysAbstain (X := X) (Y := Y) (W := W)) := by
  constructor
  · intro x y w h
    simp [alwaysAbstain] at h
  · intro x y w h
    simp [alwaysAbstain] at h

/-- Competence entails non-abstaining coverage on in-scope instances. -/
theorem competent_has_coverage
    (R : Set (X × Y)) (Γ : Regime X) (Q : CertifyingSolver X Y W)
    (hComp : CompetentOn R Γ Q) :
    ∀ x, x ∈ Γ.inScope → ∃ y w, Q.solve x = some (y, w) :=
  hComp.2.1

/-- Integrity does not imply competence on any nonempty scope:
    an always-abstain solver is integrity-preserving but not competent. -/
theorem integrity_not_competent_of_nonempty_scope
    (R : Set (X × Y)) (Γ : Regime X) (hScope : Γ.inScope.Nonempty) :
    ∃ Q : CertifyingSolver X Y W, SolverIntegrity R Q ∧ ¬ CompetentOn R Γ Q := by
  refine ⟨alwaysAbstain (X := X) (Y := Y) (W := W), alwaysAbstain_integrity (R := R), ?_⟩
  intro hComp
  rcases hScope with ⟨x, hx⟩
  rcases competent_has_coverage (R := R) (Γ := Γ)
      (Q := alwaysAbstain (X := X) (Y := Y) (W := W)) hComp x hx with ⟨y, w, hSolve⟩
  simp [alwaysAbstain] at hSolve

end DecisionQuotient.IntegrityCompetence

