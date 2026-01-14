/-
  Paper 4: Decision-Relevant Uncertainty

  HardnessDistribution.lean - The Simplicity Tax Theorem

  Core insight: Problems have intrinsic complexity (required axes/DOF).
  Using a "simpler" tool that lacks native support for that complexity
  doesn't eliminate the work—it pushes it to users at each use site.

  Key results:
  - simplicityTax: |R \ A| work pushed to each use site when tool A < problem R
  - simplicityTax_grows: total external work grows with use sites
  - complete_tool_no_tax: tools with complete coverage have zero per-site tax
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace DecisionQuotient.HardnessDistribution

/-! ## Tool-Problem Mismatch Framework

A "tool" has native expressiveness (what it can represent directly).
A "problem" has required expressiveness (what must be represented).
When tool < problem, the gap must be filled externally.
-/

/-- A problem with intrinsic complexity measured in required "axes" (dimensions of variation).
    This corresponds to Paper 1's requiredAxesOf and Paper 2's DOF. -/
structure Problem where
  /-- The set of axes/dimensions this problem requires -/
  requiredAxes : Finset ℕ
  /-- Problems must require at least one axis -/
  nonempty : requiredAxes.Nonempty

/-- A tool with native expressiveness: the axes it can handle without external help. -/
structure Tool where
  /-- Axes the tool natively supports -/
  nativeAxes : Finset ℕ

/-- Learning cost for a tool (simple proxy: number of native axes). -/
def learningCost (T : Tool) : ℕ :=
  T.nativeAxes.card

/-- Compose two tools by unioning their native axes. -/
def compose (T₁ T₂ : Tool) : Tool :=
  ⟨T₁.nativeAxes ∪ T₂.nativeAxes⟩

/-- Meet of tools: intersection of native axes. -/
def toolInf (T₁ T₂ : Tool) : Tool :=
  ⟨T₁.nativeAxes ∩ T₂.nativeAxes⟩

/-- Expressiveness order: T₁ ≤ T₂ if T₁'s native axes are a subset of T₂'s. -/
def Tool.le (T₁ T₂ : Tool) : Prop :=
  T₁.nativeAxes ⊆ T₂.nativeAxes

instance : Lattice Tool where
  le := Tool.le
  sup := compose
  inf := toolInf
  le_refl := by
    intro T x hx
    exact hx
  le_trans := by
    intro a b c hab hbc x hx
    exact hbc (hab hx)
  le_antisymm := by
    intro a b hab hba
    cases a with
    | mk aAxes =>
      cases b with
      | mk bAxes =>
        have h : aAxes = bAxes := Finset.Subset.antisymm hab hba
        cases h
        rfl
  le_sup_left := by
    intro a b x hx
    simpa [compose] using (Finset.mem_union.mpr (Or.inl hx))
  le_sup_right := by
    intro a b x hx
    simpa [compose] using (Finset.mem_union.mpr (Or.inr hx))
  sup_le := by
    intro a b c ha hb x hx
    have hx' : x ∈ a.nativeAxes ∪ b.nativeAxes := by
      simpa [compose] using hx
    rcases Finset.mem_union.mp hx' with hxa | hxb
    · exact ha hxa
    · exact hb hxb
  inf_le_left := by
    intro a b x hx
    have hx' : x ∈ a.nativeAxes ∩ b.nativeAxes := by
      simpa [toolInf] using hx
    exact (Finset.mem_inter.mp hx').1
  inf_le_right := by
    intro a b x hx
    have hx' : x ∈ a.nativeAxes ∩ b.nativeAxes := by
      simpa [toolInf] using hx
    exact (Finset.mem_inter.mp hx').2
  le_inf := by
    intro a b c hab hbc x hx
    simpa [toolInf] using (Finset.mem_inter.mpr ⟨hab hx, hbc hx⟩)

section

variable (P : Problem) (T : Tool)

/-! ## The Simplicity Tax -/

/-- The "gap" between what a problem requires and what a tool provides.
    These are axes that must be handled externally (manually, per use site). -/
def expressiveGap : Finset ℕ := P.requiredAxes \ T.nativeAxes

/-- The simplicity tax: number of axes that must be specified externally per use site. -/
def simplicityTax : ℕ := (expressiveGap P T).card

/-- A tool is complete for a problem if it natively covers all required axes. -/
def isComplete : Prop := P.requiredAxes ⊆ T.nativeAxes

/-- A tool is incomplete for a problem if some required axes are missing. -/
def isIncomplete : Prop := ¬ isComplete P T

/-! ## Core Theorems -/

/-- **Theorem (Complete Tools Pay No Tax)**.
    If a tool natively supports all required axes, the simplicity tax is zero. -/
theorem complete_tool_no_tax (h : isComplete P T) : simplicityTax P T = 0 := by
  simp only [simplicityTax, expressiveGap]
  rw [Finset.sdiff_eq_empty_iff_subset.mpr h]
  simp

/-- **Theorem (Incomplete Tools Pay Positive Tax)**.
    If a tool lacks any required axis, the simplicity tax is positive. -/
theorem incomplete_tool_positive_tax (h : isIncomplete P T) : simplicityTax P T > 0 := by
  simp only [simplicityTax, expressiveGap, isIncomplete, isComplete] at *
  have hne : (P.requiredAxes \ T.nativeAxes).Nonempty := Finset.sdiff_nonempty.mpr h
  exact Finset.card_pos.mpr hne

/-- Total external work for n use sites = n × tax per site. -/
def totalExternalWork (n : ℕ) : ℕ := n * simplicityTax P T

/-- Total cost including learning cost and per-site external work. -/
def totalCost (T : Tool) (n : ℕ) : ℕ :=
  learningCost T + totalExternalWork P T n

/-- **Theorem (Simplicity Tax Grows Linearly)**.
    For incomplete tools, total external work grows linearly with use sites. -/
theorem simplicityTax_grows (h : isIncomplete P T) :
    ∀ n m : ℕ, n < m → totalExternalWork P T n < totalExternalWork P T m := by
  intro n m hnm
  simp only [totalExternalWork]
  have hpos := incomplete_tool_positive_tax P T h
  have : simplicityTax P T ≥ 1 := hpos
  calc n * simplicityTax P T < m * simplicityTax P T := Nat.mul_lt_mul_of_pos_right hnm hpos

/-- **Theorem (Simplicity Tax is Non-Negotiable)**.
    The gap axes MUST be specified somewhere. This work cannot be eliminated,
    only redistributed (to users, to configuration, to runtime checks, etc.). -/
theorem simplicityTax_conservation :
    simplicityTax P T + (P.requiredAxes ∩ T.nativeAxes).card = P.requiredAxes.card := by
  simp only [simplicityTax, expressiveGap]
  have := Finset.card_sdiff_add_card_inter P.requiredAxes T.nativeAxes
  omega

/-! ## Comparing Tools -/

/-- Tool T₁ dominates T₂ for problem P if T₁ has strictly lower simplicity tax. -/
def dominates (T₁ T₂ : Tool) : Prop :=
  simplicityTax P T₁ < simplicityTax P T₂

/-- **Theorem (More Expressive Tools Dominate)**.
    If T₁ covers strictly more of P's requirements than T₂, T₁ dominates T₂. -/
theorem more_expressive_dominates (T₁ T₂ : Tool)
    (h : (P.requiredAxes ∩ T₁.nativeAxes).card > (P.requiredAxes ∩ T₂.nativeAxes).card) :
    dominates P T₁ T₂ := by
  simp only [dominates, simplicityTax, expressiveGap]
  have h1 := Finset.card_sdiff_add_card_inter P.requiredAxes T₁.nativeAxes
  have h2 := Finset.card_sdiff_add_card_inter P.requiredAxes T₂.nativeAxes
  omega

/-- **Theorem (Complete Beats Incomplete)**.
    A complete tool always dominates an incomplete tool. -/
theorem complete_dominates_incomplete (T_complete T_incomplete : Tool)
    (hc : isComplete P T_complete) (hi : isIncomplete P T_incomplete) :
    dominates P T_complete T_incomplete := by
  simp only [dominates]
  have h1 := complete_tool_no_tax P T_complete hc
  have h2 := incomplete_tool_positive_tax P T_incomplete hi
  omega

/-! ## The Preference Fallacy

"I prefer simple tools" is only coherent when the problem is also simple.
When problem complexity exceeds tool expressiveness, "preferring simplicity"
means preferring to pay the simplicity tax at every use site.
-/

/-- **Theorem (Simplicity Preference Has Hidden Costs)**.
    If you use an incomplete tool for n sites, you pay n × tax in external work.
    A complete tool pays 0 external work regardless of n.

    The "simpler" tool is only simpler if you ignore the external work it creates. -/
theorem simplicity_preference_fallacy (T_simple T_complex : Tool)
    (h_simple_incomplete : isIncomplete P T_simple)
    (h_complex_complete : isComplete P T_complex)
    (n : ℕ) (hn : n > 0) :
    totalExternalWork P T_complex n < totalExternalWork P T_simple n := by
  simp only [totalExternalWork]
  have h1 := complete_tool_no_tax P T_complex h_complex_complete
  have h2 := incomplete_tool_positive_tax P T_simple h_simple_incomplete
  simp [h1]
  omega

/-! ## Optional Strengthenings -/

/-- Dominance is transitive. -/
theorem dominates_trans (T₁ T₂ T₃ : Tool)
    (h₁₂ : dominates P T₁ T₂) (h₂₃ : dominates P T₂ T₃) :
    dominates P T₁ T₃ := by
  simpa [dominates] using Nat.lt_trans h₁₂ h₂₃

/-- Amortization threshold: beyond some n*, the complete tool wins. -/
theorem amortization_threshold (T_simple T_complex : Tool)
    (h_simple_incomplete : isIncomplete P T_simple)
    (h_complex_complete : isComplete P T_complex) :
    ∃ n_star : ℕ, ∀ n > n_star, totalCost P T_complex n < totalCost P T_simple n := by
  refine ⟨learningCost T_complex, ?_⟩
  intro n hn
  have htax : simplicityTax P T_simple > 0 :=
    incomplete_tool_positive_tax P T_simple h_simple_incomplete
  simp [totalCost, totalExternalWork, complete_tool_no_tax P T_complex h_complex_complete]
  have h1 : learningCost T_complex < n := hn
  have h2 : n ≤ n * simplicityTax P T_simple := Nat.le_mul_of_pos_right _ htax
  have h3 :
      n * simplicityTax P T_simple ≤
        learningCost T_simple + n * simplicityTax P T_simple := Nat.le_add_left _ _
  exact lt_of_lt_of_le h1 (le_trans h2 h3)

/-- Composition (union) reduces or preserves simplicity tax. -/
theorem compose_reduces_tax (T₁ T₂ : Tool) :
    simplicityTax P (compose T₁ T₂) ≤ simplicityTax P T₁ ∧
    simplicityTax P (compose T₁ T₂) ≤ simplicityTax P T₂ := by
  constructor
  ·
    have hsubset :
        P.requiredAxes \ (T₁.nativeAxes ∪ T₂.nativeAxes) ⊆ P.requiredAxes \ T₁.nativeAxes := by
      refine Finset.sdiff_subset_sdiff (s:=P.requiredAxes) (t:=P.requiredAxes)
        (v:=T₁.nativeAxes) (u:=T₁.nativeAxes ∪ T₂.nativeAxes) ?_ ?_
      · intro x hx; exact hx
      · intro x hx; exact Finset.mem_union.mpr (Or.inl hx)
    simpa [simplicityTax, expressiveGap, compose] using (Finset.card_le_card hsubset)
  ·
    have hsubset :
        P.requiredAxes \ (T₁.nativeAxes ∪ T₂.nativeAxes) ⊆ P.requiredAxes \ T₂.nativeAxes := by
      refine Finset.sdiff_subset_sdiff (s:=P.requiredAxes) (t:=P.requiredAxes)
        (v:=T₂.nativeAxes) (u:=T₁.nativeAxes ∪ T₂.nativeAxes) ?_ ?_
      · intro x hx; exact hx
      · intro x hx; exact Finset.mem_union.mpr (Or.inr hx)
    simpa [simplicityTax, expressiveGap, compose] using (Finset.card_le_card hsubset)

/-- Tax is antitone with respect to the expressiveness order. -/
theorem simplicityTax_antitone (T₁ T₂ : Tool) (h : T₁ ≤ T₂) :
    simplicityTax P T₂ ≤ simplicityTax P T₁ := by
  have hsubset :
      P.requiredAxes \ T₂.nativeAxes ⊆ P.requiredAxes \ T₁.nativeAxes := by
    refine Finset.sdiff_subset_sdiff (s:=P.requiredAxes) (t:=P.requiredAxes)
      (v:=T₁.nativeAxes) (u:=T₂.nativeAxes) ?_ ?_
    · intro x hx; exact hx
    · exact h
  simpa [simplicityTax, expressiveGap] using (Finset.card_le_card hsubset)

/-- Paper 1's incompleteness result as a special case. -/
theorem paper1_is_special_case :
    isIncomplete P T ↔ ∃ a ∈ P.requiredAxes, a ∉ T.nativeAxes := by
  unfold isIncomplete isComplete
  simpa using (Finset.not_subset (s:=P.requiredAxes) (t:=T.nativeAxes))

end

end DecisionQuotient.HardnessDistribution
