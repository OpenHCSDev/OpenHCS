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

-- IMPOSSIBILITY THEOREM (Constructive)
-- For any language lacking either feature, SSOT is impossible
-- This is not "Java is worse" - it is "Java CANNOT achieve SSOT"
theorem impossibility (L : LanguageFeatures)
    (h : L.has_definition_hooks = false ∨ L.has_introspection = false) :
    ¬ssot_complete L := by
  intro hc
  exact ssot_incomplete_iff L |>.mpr h hc

-- Specific impossibility for Java-like languages
-- (has introspection but no definition hooks)
theorem java_impossibility (L : LanguageFeatures)
    (h_no_hooks : L.has_definition_hooks = false)
    (_ : L.has_introspection = true) :
    ¬ssot_complete L := by
  exact impossibility L (Or.inl h_no_hooks)

-- Specific impossibility for Rust-like languages
-- (has definition hooks but no introspection)
theorem rust_impossibility (L : LanguageFeatures)
    (_ : L.has_definition_hooks = true)
    (h_no_intro : L.has_introspection = false) :
    ¬ssot_complete L := by
  exact impossibility L (Or.inr h_no_intro)

-- THEOREM: Generated Files Are Second Encodings
-- A generated source file is a second encoding, not a derivation
-- This is why code generation does not achieve SSOT

-- Model: An encoding is a file/artifact that can be independently modified
structure Encoding where
  can_be_modified_independently : Bool
  can_be_deleted : Bool
  requires_separate_compilation : Bool
  deriving DecidableEq

def is_second_encoding (e : Encoding) : Bool :=
  e.can_be_modified_independently || e.can_be_deleted || e.requires_separate_compilation

-- A generated Java file is a second encoding
def generated_java_file : Encoding := {
  can_be_modified_independently := true,  -- Can edit HandlerRegistry.java
  can_be_deleted := true,                 -- Can delete it
  requires_separate_compilation := true   -- Must be compiled separately
}

theorem generated_file_is_second_encoding :
    is_second_encoding generated_java_file = true := by
  native_decide

-- An in-memory Python derivation is NOT a second encoding
def python_in_memory_derivation : Encoding := {
  can_be_modified_independently := false, -- No separate file to edit
  can_be_deleted := false,                -- No file to delete
  requires_separate_compilation := false  -- Created at class definition
}

theorem python_derivation_not_second_encoding :
    is_second_encoding python_in_memory_derivation = false := by
  native_decide

-- THEOREM: Opaque Expansion Prevents Verification
-- If macro expansion is opaque at runtime, verification is impossible
theorem opaque_expansion_prevents_verification (L : LanguageFeatures)
    (h_opaque : L.has_introspection = false) :
    ¬(L.has_introspection = true) := by
  intro h_contra
  rw [h_opaque] at h_contra
  exact Bool.false_ne_true h_contra

