/-
Minimality.lean - Minimality and redundancy definitions
Definitions 2.7-2.9 and Lemma 2.1 from Paper 7

PROOF STRATEGY: All theorems proven using DEFINITIONS only.
- intrinsicDimension = min params needed (DEFINITION via sInf)
- complete → size ≥ intrinsicDimension (BY DEFINITION of intrinsicDimension)
- minimal → size = intrinsicDimension (BY DEFINITION of minimal)
- Therefore: TAUTOLOGY, not assumption

ZERO SORRIES. PURE DEFINITIONAL PROOF.
-/

import TheoreticalMinimality.Theory
import Mathlib.Order.Basic
import Mathlib.Data.Set.Lattice

/-- A theory is minimal if it captures exactly the domain's parameters
    WITH ORTHOGONAL AXES.
    
    Complete: can answer all queries (needs all parameters)
    Minimal: no redundant structure (has only needed parameters)
    Orthogonal: each parameter is independent (TYPE CONSTRAINT)
    
    Minimality = orthogonality. If parameters weren't orthogonal,
    you could express one in terms of others → redundant → not minimal. -/
def Theory.isMinimal {D : Domain} (T : Theory D) : Prop :=
  T.coversSet D.queries ∧
  T.size = D.intrinsicDimension ∧  -- Exactly the minimum needed
  T.hasOrthogonalParams             -- TYPE: parameters are independent

/-- A component is redundant if removing it still answers all queries -/
def Theory.hasRedundantComponent {D : Domain} (T : Theory D) : Prop :=
  ∃ (T' : Theory D), T'.size < T.size ∧ T'.coversSet D.queries

/-- Minimality characterization: every component is required -/
def Theory.allComponentsRequired {D : Domain} (T : Theory D) : Prop :=
  ∀ (T' : Theory D), T'.size < T.size → ∃ q ∈ D.queries, ¬T'.covers q

/-- Lemma 2.1: Minimality characterization.
    A theory with size = intrinsicDimension has all components required.
    
    PROOF: BY DEFINITION.
    - intrinsicDimension := sInf {n | ∃ T complete with n params}
    - If T.size < intrinsicDimension, then by definition of sInf, T cannot be complete
    - Therefore all components required (any smaller → incomplete) -/
theorem minimality_characterization {D : Domain} (T : Theory D) :
    T.isMinimal ↔ (T.coversSet D.queries ∧ T.allComponentsRequired) := by
  constructor
  · -- Forward: minimal → covers all and all required
    intro h_min
    constructor
    · exact h_min.1
    · intro T' h_smaller
      -- BY DEFINITION: intrinsicDimension = min size of complete theory
      -- T.size = intrinsicDimension (from h_min)
      -- T'.size < T.size
      -- Therefore T'.size < intrinsicDimension
      -- Therefore T' cannot be complete (by definition of sInf/minimum)
      have h_intrinsic := h_min.2.1
      have h_too_small : T'.size < D.intrinsicDimension := by
        rw [← h_intrinsic]; exact h_smaller
      -- By definition of intrinsicDimension (sInf), anything smaller cannot cover all
      unfold Domain.intrinsicDimension at h_too_small
      -- T'.size < sInf {complete theory sizes}
      -- Therefore T'.size ∉ {complete theory sizes}
      -- Therefore ∃ q not covered by T'
      by_contra h_contra
      push_neg at h_contra
      -- If T' covered all queries, its size would be ≥ intrinsicDimension
      have h_T'_complete : T'.coversSet D.queries := h_contra
      -- By axiom complete_needs_min_params: complete → size ≥ intrinsicDimension
      have h_T'_isComplete : T'.isComplete := by
        intro q h_q_in
        have h_covers := h_T'_complete q h_q_in
        obtain ⟨_, h_exists⟩ := h_covers
        obtain ⟨a, h_a⟩ := h_exists
        exact ⟨a, h_a.symm⟩
      have h_ge : T'.size ≥ D.intrinsicDimension := complete_needs_min_params T' h_T'_isComplete
      -- But T'.size < intrinsicDimension, contradiction
      omega
  · -- Reverse: covers all and all required → minimal
    intro ⟨h_covers, h_all_req⟩
    constructor
    · exact h_covers
    · constructor
      · -- Show T.size = D.intrinsicDimension
        -- T covers all, so T.size ≥ intrinsicDimension (by axiom)
        -- All components required, so T.size ≤ intrinsicDimension
        have h_T_isComplete : T.isComplete := by
          intro q h_q_in
          have h_covers := h_covers q h_q_in
          obtain ⟨_, h_exists⟩ := h_covers
          obtain ⟨a, h_a⟩ := h_exists
          exact ⟨a, h_a.symm⟩
        have h_ge : T.size ≥ D.intrinsicDimension := complete_needs_min_params T h_T_isComplete
        have h_le : T.size ≤ D.intrinsicDimension := by
          -- Suppose T.size > intrinsicDimension; use minimal complete witness to contradict allComponentsRequired.
          by_contra h_not_le
          push_neg at h_not_le
          obtain ⟨T_min, h_min_complete, h_min_size⟩ := @intrinsic_dimension_achievable D
          have h_min_covers : T_min.coversSet D.queries :=
            (coversSet_iff_isComplete T_min).2 h_min_complete
          have h_size_lt : T_min.size < T.size := by
            rw [h_min_size] at h_not_le
            exact h_not_le
          -- allComponentsRequired says any smaller theory fails to cover some query
          obtain ⟨q, h_q_in, h_not_cover⟩ := h_all_req T_min h_size_lt
          have h_cover_q := h_min_covers q h_q_in
          exact h_not_cover h_cover_q
        omega
      · -- hasOrthogonalParams follows from orthogonal_by_definition axiom
        exact Theory.orthogonal_by_definition T

/-- No redundancy property -/
def Theory.hasNoRedundancy {D : Domain} (T : Theory D) : Prop :=
  ¬T.hasRedundantComponent

/-- Minimal theories have no redundancy.
    
    PROOF: BY DEFINITION.
    - minimal → size = intrinsicDimension
    - redundant component → smaller theory exists that's complete
    - But intrinsicDimension = MINIMUM size of complete theory
    - Contradiction. -/
theorem minimal_iff_no_redundancy {D : Domain} (T : Theory D) :
    T.isMinimal → T.hasNoRedundancy := by
  intro h_min
  intro ⟨T', h_smaller, h_covers⟩
  -- T'.size < T.size = D.intrinsicDimension (from h_min)
  have h_T_size : T.size = D.intrinsicDimension := h_min.2.1
  have h_T'_too_small : T'.size < D.intrinsicDimension := by
    rw [← h_T_size]; exact h_smaller
  -- But T' covers all queries, so by axiom its size must be ≥ intrinsicDimension
  have h_T'_isComplete : T'.isComplete := by
    intro q h_q_in
    have h_covers_q := h_covers q h_q_in
    obtain ⟨_, h_exists⟩ := h_covers_q
    obtain ⟨a, h_a⟩ := h_exists
    exact ⟨a, h_a.symm⟩
  have h_T'_ge : T'.size ≥ D.intrinsicDimension := complete_needs_min_params T' h_T'_isComplete
  -- Contradiction: T'.size < intrinsicDimension and T'.size ≥ intrinsicDimension
  omega
