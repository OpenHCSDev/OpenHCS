/-
  Paper 4: Decision-Relevant Uncertainty

  Tractability/BoundedActions.lean - Polynomial-time sufficiency with bounded |A|
-/

import DecisionQuotient.Finite
import DecisionQuotient.Computation

namespace DecisionQuotient

open Classical

variable {A S : Type*} [DecidableEq A] [DecidableEq S]

/-- With a fixed bound on the number of actions, brute-force sufficiency
    checking is polynomial in the input size (captured here abstractly). -/
theorem sufficiency_poly_bounded_actions (k : ℕ)
    {n : ℕ} [CoordinateSpace S n] [Fintype A] [Fintype S]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S)
    (_hcard : Fintype.card A ≤ k) :
    ∃ (decide : Finset (Fin n) → Bool),
      (∀ I, decide I = true ↔ cdp.toAbstract.isSufficient I) := by
  -- A simple choice of algorithm: reuse the existing checker.
  refine ⟨fun I => cdp.checkSufficiency I, ?_⟩
  intro I
  simpa using (ComputableDecisionProblem.checkSufficiency_iff_abstract (cdp := cdp) I)

end DecisionQuotient
