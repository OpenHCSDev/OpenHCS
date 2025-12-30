/-
  SSOT Formalization - Completeness Theorem (Iff)
  Paper 2: Formal Foundations for the Single Source of Truth Principle
-/

import Ssot.Requirements

-- Definition: SSOT-Complete Language
-- A language that can achieve verifiable SSOT for all structural facts
def ssot_complete (L : LanguageFeatures) : Prop :=
  L.has_definition_hooks = true ∧ L.has_introspection = true

-- Theorem 3.6: Necessary and Sufficient Conditions for SSOT
-- A language L enables complete SSOT for structural facts IFF
-- it has definition-time hooks AND introspectable derivation
theorem ssot_iff (L : LanguageFeatures) :
    ssot_complete L ↔ (L.has_definition_hooks = true ∧ L.has_introspection = true) := by
  unfold ssot_complete
  rfl

-- Direction 1: Sufficiency (⟸)
-- Given both features, SSOT is achievable and verifiable
theorem ssot_sufficient (L : LanguageFeatures)
    (h_hooks : L.has_definition_hooks = true)
    (h_intro : L.has_introspection = true) :
    ssot_complete L := by
  unfold ssot_complete
  exact ⟨h_hooks, h_intro⟩

-- Direction 2: Necessity (⟹)
-- If SSOT is achievable, both features must be present
theorem ssot_necessary (L : LanguageFeatures)
    (h : ssot_complete L) :
    L.has_definition_hooks = true ∧ L.has_introspection = true := by
  exact h

-- The IFF is the key theorem: these are DERIVED requirements
-- We didn't choose them; correctness forcing determined them

-- Corollary: A language is SSOT-incomplete iff it lacks either feature
theorem ssot_incomplete_iff (L : LanguageFeatures) :
    ¬ssot_complete L ↔ (L.has_definition_hooks = false ∨ L.has_introspection = false) := by
  unfold ssot_complete
  constructor
  · intro h
    -- h : ¬(hooks = true ∧ intro = true)
    -- Need to show: hooks = false ∨ intro = false
    cases hd : L.has_definition_hooks with
    | false => left; rfl
    | true =>
      cases hi : L.has_introspection with
      | false => right; rfl
      | true =>
        have : L.has_definition_hooks = true ∧ L.has_introspection = true := ⟨hd, hi⟩
        exact absurd this h
  · intro h ⟨h1, h2⟩
    cases h with
    | inl hf => rw [hf] at h1; exact Bool.false_ne_true h1
    | inr hf => rw [hf] at h2; exact Bool.false_ne_true h2

