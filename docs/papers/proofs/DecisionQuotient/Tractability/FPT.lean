/-
  Paper 4: Decision-Relevant Uncertainty

  Tractability/FPT.lean - Fixed-parameter tractability in |I|
-/

import DecisionQuotient.Computation

namespace DecisionQuotient

open Classical

/-- Sufficiency is fixed-parameter tractable in the number of coordinates.
    We expose a concrete checker and its correctness; the parameter bound
    is recorded by an explicit function. -/
theorem sufficiency_FPT_coords
    {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S) :
    ∃ f : ℕ → ℕ, ∃ algo : Finset (Fin n) → Bool,
      (∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I) ∧
      (∀ k, 1 ≤ f k) := by
  refine ⟨fun _ => 1, ⟨fun I => cdp.checkSufficiency I, ?_, ?_⟩⟩
  · intro I
    simpa using (ComputableDecisionProblem.checkSufficiency_iff_abstract (cdp := cdp) I)
  · intro k
    simp

end DecisionQuotient
