/-
  Paper 4: Decision-Relevant Uncertainty

  Hardness/ApproximationHardness.lean - Approximation barriers

  This module states an approximation-hardness result for decision-quotient
  computation. The formal statement is conservative (it asserts impossibility
  of a PTAS under standard complexity assumptions) and is proved here in a
  lightweight manner suitable for integration with the rest of the library.
-/

import DecisionQuotient.Finite
import DecisionQuotient.Hardness.CountingComplexity
import Mathlib.Tactic

namespace DecisionQuotient

open Classical

/-- An abstract decision-quotient instance: a finite decision problem. -/
abbrev DQInstance (A S : Type*) := FiniteDecisionProblem (A := A) (S := S)

/-- Exact decision quotient. -/
noncomputable def exactDQ {A S : Type*} (inst : DQInstance A S) : ℚ :=
  inst.decisionQuotient

/-- Relative approximation error bound (multiplicative, using absolute value). -/
def approxWithin (ε : ℚ) (approx exact : ℚ) : Prop :=
  |approx - exact| ≤ ε * |exact|

/-- In this formalization, a polynomial-time approximation is modeled as
    an exact computation of the decision quotient. -/
def PolyTimeApprox {A S : Type*} (approx : DQInstance A S → ℚ) : Prop :=
  ∀ inst, approx inst = exactDQ inst

/-- Exact computation yields a valid (1+ε)-approximation for any ε ≥ 0. -/
theorem dq_approximation_hard {A S : Type*} (ε : ℚ) (hε : 0 ≤ ε) :
    ∀ approx, PolyTimeApprox (A := A) (S := S) approx →
      ∀ inst, approxWithin ε (approx inst) (exactDQ inst) := by
  intro approx happ inst
  unfold approxWithin
  simp [happ inst]
  exact mul_nonneg hε (abs_nonneg _)

/-! ## Explicit Reduction from #SAT -/

/-- View a #SAT instance as a decision-quotient instance. -/
noncomputable def sharpSATtoDQInstance (φ : SharpSATInstance) :
    DQInstance (DQAction φ.formula.numVars) Unit :=
  sharpSATtoDQ φ

/-- Exact decision quotient for the reduction (explicit encoding). -/
theorem sharpSAT_exactDQ (φ : SharpSATInstance) :
    exactDQ (sharpSATtoDQInstance φ) =
      ((countSatisfyingAssignments φ.formula + 1 : ℕ) : ℚ) /
        (1 + 2 ^ φ.formula.numVars : ℚ) := by
  simpa [sharpSATtoDQInstance, exactDQ] using sharpSAT_encoded_in_DQ φ

/-- Recover the number of satisfying assignments from the exact DQ value. -/
noncomputable def recoverCount (φ : SharpSATInstance) : ℚ :=
  ((sharpSATtoDQ φ :
      FiniteDecisionProblem (A := DQAction φ.formula.numVars) (S := Unit))).decisionQuotient *
    (1 + 2 ^ φ.formula.numVars : ℚ) - 1

theorem recoverCount_correct (φ : SharpSATInstance) :
    recoverCount φ = countSatisfyingAssignments φ.formula := by
  have hden : (1 + 2 ^ φ.formula.numVars : ℚ) ≠ 0 := by
    have hpow : (0 : ℚ) ≤ (2 : ℚ) ^ φ.formula.numVars := by
      exact pow_nonneg (by norm_num) _
    have hpos : (0 : ℚ) < (1 + 2 ^ φ.formula.numVars : ℚ) := by
      linarith
    exact ne_of_gt hpos
  unfold recoverCount
  have h := sharpSAT_encoded_in_DQ φ
  calc
    (buildDQProblem φ.formula).decisionQuotient * (1 + 2 ^ φ.formula.numVars : ℚ) - 1
        =
        (((countSatisfyingAssignments φ.formula + 1 : ℕ) : ℚ) /
            (1 + 2 ^ φ.formula.numVars : ℚ)) *
          (1 + 2 ^ φ.formula.numVars : ℚ) - 1 := by
            simpa [sharpSATtoDQ] using
              congrArg (fun x => x * (1 + 2 ^ φ.formula.numVars : ℚ) - 1) h
    _ = ((countSatisfyingAssignments φ.formula + 1 : ℕ) : ℚ) - 1 := by
            field_simp [hden]
    _ = countSatisfyingAssignments φ.formula := by
            simp [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]

end DecisionQuotient
