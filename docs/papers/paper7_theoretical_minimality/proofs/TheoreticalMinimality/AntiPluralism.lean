/-
AntiPluralism.lean - Anti-pluralism results
Theorems 4.1-4.2 from Paper 7
-/

import TheoreticalMinimality.Uniqueness
import Mathlib.Data.Fintype.Basic

/-- Theorem 4.1: Incoherence of Pluralism -/
theorem anti_pluralism (D : Domain) [Finite D.Query]
    (T1 T2 : Theory D) (h1 : T1.isMinimal) (h2 : T2.isMinimal)
    (h_equiv : Theory.queryEquivalent T1 T2) :
    T1 ≅ T2 := by
  exact theory_discovery_mechanical D T1 T2 h1 h2 h_equiv

/-- Corollary 4.1: Convention vs Discovery -/
theorem convention_vs_discovery {D : Domain} (T1 T2 : Theory D)
    (iso : TheoryIso T1 T2) :
    ∀ q ∈ D.queries, T1.mapping q = T2.mapping q := by
  intro q hq
  exact iso.answer_equiv q hq

/-- Multiple distinct minimal theories cannot exist -/
theorem no_multiple_minimal (D : Domain) [Finite D.Query] :
    ¬∃ T1 T2 : Theory D,
      T1.isMinimal ∧ T2.isMinimal ∧ Theory.queryEquivalent T1 T2 ∧ ¬(T1 ≅ T2) := by
  intro ⟨T1, T2, h1, h2, h_equiv, h_not_iso⟩
  have h_iso := anti_pluralism D T1 T2 h1 h2 h_equiv
  exact h_not_iso h_iso

/-- Isomorphic theories differ only in notation -/
theorem isomorphic_same_content {D : Domain} (T1 T2 : Theory D) 
    (h_iso : T1 ≅ T2) :
    ∀ q ∈ D.queries, T1.mapping q = T2.mapping q := by
  obtain ⟨iso⟩ := h_iso
  exact convention_vs_discovery T1 T2 iso

/-- Intrinsic dimension is bounded by the number of queries for finite domains. -/
theorem intrinsic_dimension_bounded : ∀ {D : Domain} [Fintype D.Query],
  D.intrinsicDimension ≤ Fintype.card D.Query := by
  classical
  intro D _
  -- Build a trivial complete theory of size |Query|
  let T : Theory D :=
    { numParams := Fintype.card D.Query
      params := fun _ => default
      mapping := fun _ => default }
  have h_complete : T.isComplete := by
    intro _q _hq; exact ⟨default, rfl⟩
  have h_nonempty : ∃ n, completeTheoryOfSize (D:=D) n := by
    obtain ⟨T₀, h₀⟩ := complete_theory_exists D
    exact ⟨T₀.size, ⟨T₀, h₀, rfl⟩⟩
  have h_T : completeTheoryOfSize (D:=D) T.size := ⟨T, h_complete, rfl⟩
  have h_le := Nat.find_min' h_nonempty h_T
  simpa [Domain.intrinsicDimension, T] using h_le

/-- Theorem 4.2: Learnability -/
theorem minimal_theory_learnable (D : Domain) [Fintype D.Query] :
    ∃ (sample_size : ℕ), 
      ∀ (T : Theory D), T.isMinimal → T.size ≤ sample_size := by
  -- Sample complexity is bounded by query space size
  -- For finite queries, minimal theory size is bounded
  use Fintype.card D.Query
  intro T h_min
  -- Minimal theories have bounded size (finite domain)
  have h_size := h_min.2.1
  rw [h_size]
  -- intrinsicDimension ≤ |Query| (by axiom)
  exact intrinsic_dimension_bounded (D := D)
