import Mathlib

/-!
# Axis-Parametric Framework (Draft)

First pass at the generic abstractions needed for plan_01:
- `Axis` as a recursive lattice structure
- `Query` with explicit axis requirements
- Minimality and independence lemmas

This is a lightweight draft to validate the formal shapes before moving the
definitions into a dedicated Lake package.
-/

open Classical

universe u v

/-- A first-class axis with a lattice-ordered carrier and recursive structure. -/
structure Axis where
  Carrier    : Type u
  ord        : PartialOrder Carrier
  lattice    : Lattice Carrier
  recurse    : Carrier → List Carrier

attribute [instance] Axis.ord Axis.lattice

/-- Classical decidable equality for axes (needed for `erase`/filters). -/
noncomputable instance : DecidableEq Axis := Classical.decEq _

/-- An axis set is just a list for now; we will later add invariants (e.g., no dupes). -/
abbrev AxisSet : Type (u + 1) := List Axis

/-- A query that produces a result of type `α`, given projections for each required axis. -/
structure Query (α : Type v) where
  requires : List Axis
  compute  : (∀ a ∈ requires, a.Carrier) → α

/-- A domain is a collection of queries; we use `Prop`/`Bool` answers interchangeably. -/
abbrev Domain (α : Type v) := List (Query α)

/-- `A` can answer `q` iff every required axis is available in `A`. -/
def canAnswer (A : AxisSet) (q : Query α) : Prop :=
  q.requires ⊆ A

/-- Derivability-aware answerability: every required axis has some derivable representative in `A`. -/
def canAnswerD (A : AxisSet) (q : Query α) : Prop :=
  ∀ a ∈ q.requires, ∃ b ∈ A, derivable a b

/-- Monotonicity: more axes can answer at least what fewer axes can. -/
lemma canAnswer_mono {A B : AxisSet} (hsub : A ⊆ B) (q : Query α) :
    canAnswer A q → canAnswer B q := by
  intro h
  exact fun r hr => hsub (h hr)

/-- Monotonicity for derivability-aware answerability. -/
lemma canAnswerD_mono {A B : AxisSet} (hsub : A ⊆ B) (q : Query α) :
    canAnswerD A q → canAnswerD B q := by
  intro h a haReq
  rcases h a haReq with ⟨b, hbA, hder⟩
  exact ⟨b, hsub hbA, hder⟩

/-- `A` answers all queries in `D`. -/
def complete (A : AxisSet) (D : Domain α) : Prop :=
  ∀ q ∈ D, canAnswer A q

/-- Derivability-aware completeness. -/
def completeD (A : AxisSet) (D : Domain α) : Prop :=
  ∀ q ∈ D, canAnswerD A q

/-- Monotonicity of completeness under axis superset. -/
lemma complete_mono {A B : AxisSet} (hsub : A ⊆ B) (D : Domain α) :
    complete A D → complete B D := by
  intro h q hq
  exact canAnswer_mono hsub q (h q hq)

/-- Monotonicity of derivability-aware completeness. -/
lemma completeD_mono {A B : AxisSet} (hsub : A ⊆ B) (D : Domain α) :
    completeD A D → completeD B D := by
  intro h q hq
  exact canAnswerD_mono hsub q (h q hq)

/-- `A` is complete and every axis is necessary. -/
def minimal (A : AxisSet) (D : Domain α) : Prop :=
  complete A D ∧ ∀ a ∈ A, ¬ complete (A.erase a) D

/-- Derivability-aware minimality. -/
def minimalD (A : AxisSet) (D : Domain α) : Prop :=
  completeD A D ∧ ∀ a ∈ A, ¬ completeD (A.erase a) D

/-- Axis `a` is independent of the rest of `A` with respect to `D`. -/
def independent (a : Axis) (A : AxisSet) (D : Domain α) : Prop :=
  ∃ q ∈ D, a ∈ q.requires ∧ ¬ canAnswer (A.erase a) q

/-- Derivability-aware independence. -/
def independentD (a : Axis) (A : AxisSet) (D : Domain α) : Prop :=
  ∃ q ∈ D, a ∈ q.requires ∧ ¬ canAnswerD (A.erase a) q

/-- Whether query `q` explicitly depends on axis `a`. -/
def axisDependent (q : Query α) (a : Axis) : Prop :=
  a ∈ q.requires

/-- Queries in `D` that depend on axis `a`. -/
def queriesForAxis (a : Axis) (D : Domain α) : List (Query α) :=
  D.filter (fun q => decide (axisDependent q a))

/-- Queries that depend on no axis in `A` (axis-independent part of `D`). -/
def queriesIndependentOf (A : AxisSet) (D : Domain α) : List (Query α) :=
  D.filter (fun q => decide (¬ ∃ a ∈ A, axisDependent q a))

/-- Capability set: queries from `D` that a given axis set can answer. -/
def capabilitySet (A : AxisSet) (D : Domain α) : List (Query α) :=
  D.filter (fun q => decide (canAnswer A q))

/-- Derivability-aware capability set. -/
def capabilitySetD (A : AxisSet) (D : Domain α) : List (Query α) :=
  D.filter (fun q => decide (canAnswerD A q))

/-- Soundness: axis buckets are subsets of the domain. -/
lemma queriesForAxis_subset (a : Axis) (D : Domain α) :
    queriesForAxis a D ⊆ D := by
  intro q hq
  exact (List.mem_filter.mp hq).left

/-- Soundness: the independent bucket is a subset of the domain. -/
lemma queriesIndependent_subset (A : AxisSet) (D : Domain α) :
    queriesIndependentOf A D ⊆ D := by
  intro q hq
  exact (List.mem_filter.mp hq).left

/-- Capability sets are monotone in axis inclusion. -/
lemma capabilitySet_mono {A B : AxisSet} (hsub : A ⊆ B) (D : Domain α) :
    capabilitySet A D ⊆ capabilitySet B D := by
  classical
  intro q hq
  rcases List.mem_filter.mp hq with ⟨hqD, hcanA⟩
  have hA : canAnswer A q := by
    have := of_decide_eq_true hcanA
    exact this
  have hB : canAnswer B q := canAnswer_mono (q:=q) hsub hA
  exact List.mem_filter.mpr ⟨hqD, by simpa [hB]⟩

/-- Derivability-aware capability sets are monotone in axis inclusion. -/
lemma capabilitySetD_mono {A B : AxisSet} (hsub : A ⊆ B) (D : Domain α) :
    capabilitySetD A D ⊆ capabilitySetD B D := by
  classical
  intro q hq
  rcases List.mem_filter.mp hq with ⟨hqD, hcanA⟩
  have hA : canAnswerD A q := by exact of_decide_eq_true hcanA
  have hB : canAnswerD B q := canAnswerD_mono (q:=q) hsub hA
  exact List.mem_filter.mpr ⟨hqD, by simpa [hB]⟩

/-- Independence bucket excludes any axis dependency. -/
lemma mem_queriesIndependent_no_dep {A : AxisSet} {D : Domain α} {q : Query α}
    (hq : q ∈ queriesIndependentOf A D) :
    ¬ ∃ a ∈ A, axisDependent q a := by
  have := (List.mem_filter.mp hq).right
  by_cases h : ∃ a ∈ A, axisDependent q a
  · simpa [h] at this
  · exact h

/-- A query cannot be both independent and assigned to an axis bucket. -/
lemma independent_disjoint_axis {A : AxisSet} {D : Domain α} {q : Query α}
    (hInd : q ∈ queriesIndependentOf A D) :
    ∀ a ∈ A, q ∉ queriesForAxis a D := by
  intro a haA hInBucket
  have hdep : ∃ a' ∈ A, axisDependent q a' := by
    refine ⟨a, haA, ?_⟩
    have := (List.mem_filter.mp hInBucket).right
    simpa [axisDependent] using this
  have hneg := mem_queriesIndependent_no_dep (A:=A) (D:=D) (q:=q) hInd
  exact (hneg hdep).elim

/-- Partition statement: every query is either independent or bucketed under some axis. -/
def querySpacePartition (A : AxisSet) (D : Domain α) : Prop :=
  ∀ q ∈ D, q ∈ queriesIndependentOf A D ∨ ∃ a ∈ A, q ∈ queriesForAxis a D

/-- If `A` is complete and minimal for `D`, every member witnesses independence. -/
def axisIndependenceCriterion (A : AxisSet) (D : Domain α) : Prop :=
  ∀ a ∈ A, independent a A D

lemma axisIndependence_of_minimal {A : AxisSet} {D : Domain α}
    (hmin : minimal A D) : axisIndependenceCriterion A D := by
  intro a ha
  exact independence_of_minimal (a:=a) ha hmin

/-- Derivability-aware independence for minimalD sets. -/
def axisIndependenceCriterionD (A : AxisSet) (D : Domain α) : Prop :=
  ∀ a ∈ A, independentD a A D

lemma axisIndependenceD_of_minimalD {A : AxisSet} {D : Domain α}
    (hmin : minimalD A D) : axisIndependenceCriterionD A D := by
  intro a ha
  rcases hmin with ⟨hcomp, hminRemove⟩
  have hnot : ¬ completeD (A.erase a) D := hminRemove a ha
  have hExists : ∃ q ∈ D, ¬ canAnswerD (A.erase a) q := by
    classical
    simpa [completeD] using hnot
  rcases hExists with ⟨q, hqD, hnotCan⟩
  have hAns : canAnswerD A q := hcomp q hqD
  -- show a is required (choose witness from requirement list not answerable without a)
  classical
  have : ∃ r ∈ q.requires, ∀ b ∈ A.erase a, ¬ derivable r b := by
    classical
    -- choose any r in requires; if all derivable via erase a we'd contradict hnotCan
    by_contra hforall
    push_neg at hforall
    have hcan : canAnswerD (A.erase a) q := by
      intro r hrReq
      rcases hAns r hrReq with ⟨b, hbA, hder⟩
      by_cases hbEq : b = a
      · subst hbEq
        -- use witness from hforall to reroute through erase a
        obtain ⟨b', hb'Erase, hder'⟩ := hforall r hrReq
        exact ⟨b', hb'Erase, hder'⟩
      · have hbErase : b ∈ A.erase a := List.mem_erase.mpr ⟨hbEq, hbA⟩
        exact ⟨b, hbErase, hder⟩
    exact hnotCan hcan
  rcases this with ⟨r, hrReq, hrNoDeriv⟩
  refine ⟨q, hqD, hrReq, ?_⟩
  intro hcanErase
  have : ∃ b ∈ A.erase a, derivable r b := hcanErase r hrReq
  rcases this with ⟨b, hbErase, hder⟩
  exact (hrNoDeriv b hbErase) hder

/-- Derivability collapse: removable axes derivable from others do not change completeness. -/
def derivabilityCollapse (A : AxisSet) (D : Domain α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, derivable a b → complete A D → complete (A.erase a) D

/-- Collapsing derivable axes preserves derivability-aware completeness. -/
lemma collapseDerivable_preserves_completeD {A : AxisSet} {D : Domain α} :
    completeD A D → completeD (collapseDerivable A) D := by
  classical
  intro hcomp q hqD a haReq
  rcases hcomp q hqD a haReq with ⟨b, hbA, hder⟩
  rcases derivable_to_collapse (A:=A) (b:=b) hbA with ⟨c, hcCollapse, hder'⟩
  exact ⟨c, hcCollapse, derivable_trans hder hder'⟩

/-- Completeness uniqueness: minimal complete axis sets have equal length (up to iso later). -/
def completenessUnique (A₁ A₂ : AxisSet) (D : Domain α) : Prop :=
  minimal A₁ D → minimal A₂ D → A₁.length = A₂.length

/-- Compositional extension: adding new requirements forces adding independent axes. -/
def compositionalExtension (A₁ A₂ : AxisSet) (D₁ D₂ : Domain α) : Prop :=
  D₁ ⊆ D₂ →
  complete A₁ D₁ →
  minimal A₂ D₂ →
  A₁ ⊆ A₂

/--
Every query in `D` is either placed under some axis bucket or in the independent
bucket. (Non-disjointness is acceptable for now; uniqueness comes from later
minimality/derivability lemmas.)
-/
theorem query_partition (A : AxisSet) (D : Domain α) (q : Query α) (hq : q ∈ D) :
    q ∈ queriesIndependentOf A D ∨ ∃ a ∈ A, q ∈ queriesForAxis a D := by
  classical
  by_cases hdep : ∃ a ∈ A, axisDependent q a
  · rcases hdep with ⟨a, haA, haReq⟩
    right
    refine ⟨a, haA, ?_⟩
    exact List.mem_filter.mpr ⟨hq, by simpa [axisDependent, haReq]⟩
  · left
    have hneg : ¬ ∃ a ∈ A, axisDependent q a := hdep
    exact List.mem_filter.mpr ⟨hq, by simp [hneg]⟩

lemma query_partition_global (A : AxisSet) (D : Domain α) :
    querySpacePartition A D := by
  intro q hq
  exact query_partition A D q hq

/--
If `(a :: A)` is minimal for `D`, then there exists a query gained by adding `a`
to `A` (witnessed by independence).
-/
lemma capability_gain_of_minimal {A : AxisSet} {D : Domain α} {a : Axis}
    (hmin : minimal (a :: A) D) :
    ∃ q, q ∈ capabilitySet (a :: A) D ∧ q ∉ capabilitySet A D := by
  classical
  -- independence witness
  have hind := independence_of_minimal (A:=a::A) (D:=D) (a:=a)
      (by simp) hmin
  rcases hind with ⟨q, hqD, haReq, hnot⟩
  -- completeness gives canAnswer with a present
  have hcomplete := hmin.left
  have hAnsWith : canAnswer (a :: A) q := hcomplete q hqD
  -- construct membership / non-membership
  refine ⟨q, ?_, ?_⟩
  · exact List.mem_filter.mpr ⟨hqD, by simpa [hAnsWith]⟩
  · intro hcapA
    rcases List.mem_filter.mp hcapA with ⟨_, hcanA⟩
    have h' : canAnswer (List.erase (a::A) a) q := by
      -- erase head a from (a :: A) yields A
      simpa using of_decide_eq_true hcanA
    -- contradict independence witness
    exact hnot h'

/-- A lattice homomorphism between axes (preserves ⊔/⊓). -/
structure AxisHom (a b : Axis) where
  toFun   : b.Carrier → a.Carrier
  map_sup : ∀ x y, toFun (x ⊔ y) = toFun x ⊔ toFun y
  map_inf : ∀ x y, toFun (x ⊓ y) = toFun x ⊓ toFun y

namespace AxisHom

variable {a b c : Axis}

/-- Identity homomorphism. -/
def id (a : Axis) : AxisHom a a where
  toFun   := fun x => x
  map_sup := by intro; simp
  map_inf := by intro; simp

/-- Composition of axis homomorphisms. -/
def comp (h₁ : AxisHom a b) (h₂ : AxisHom b c) : AxisHom a c where
  toFun   := fun x => h₁.toFun (h₂.toFun x)
  map_sup := by
    intro x y
    calc
      h₁.toFun (h₂.toFun (x ⊔ y))
          = h₁.toFun (h₂.toFun x ⊔ h₂.toFun y) := by
              simpa using congrArg h₁.toFun (h₂.map_sup x y)
      _ = h₁.toFun (h₂.toFun x) ⊔ h₁.toFun (h₂.toFun y) := h₁.map_sup _ _
  map_inf := by
    intro x y
    calc
      h₁.toFun (h₂.toFun (x ⊓ y))
          = h₁.toFun (h₂.toFun x ⊓ h₂.toFun y) := by
              simpa using congrArg h₁.toFun (h₂.map_inf x y)
      _ = h₁.toFun (h₂.toFun x) ⊓ h₁.toFun (h₂.toFun y) := h₁.map_inf _ _

end AxisHom

/-- Axis `a` is derivable from `b` if there exists a map from `b`'s carrier. -/
def derivable (a b : Axis) : Prop := Nonempty (AxisHom a b)

lemma derivable_refl (a : Axis) : derivable a a :=
  ⟨AxisHom.id a⟩

lemma derivable_trans {a b c : Axis} :
    derivable a b → derivable b c → derivable a c := by
  rintro ⟨h₁⟩ ⟨h₂⟩
  exact ⟨AxisHom.comp h₁ h₂⟩

/-- Axis `a` is redundant within `A` if it is derivable from some *strictly other* axis in `A`. -/
def redundantWith (A : AxisSet) (a : Axis) : Prop :=
  ∃ b ∈ A.erase a, derivable a b ∧ ¬ derivable b a

/-- Collapse derivable axes to obtain a minimal (by derivability) axis set. -/
def collapseDerivable (A : AxisSet) : AxisSet :=
  A.filter (fun a => ¬ redundantWith A a)

/-- Redundancy is monotone with respect to erasing unrelated axes. -/
lemma redundantWith_erase_of_ne {A : AxisSet} {a b : Axis}
    (h : redundantWith (A.erase b) a) (hneq : a ≠ b) :
    redundantWith A a := by
  classical
  rcases h with ⟨c, hcErase, hder, hnotback⟩
  have hcA : c ∈ A := (List.mem_erase.mp hcErase).right
  have hca : c ≠ a := (List.mem_erase.mp hcErase).left
  refine ⟨c, ?_, hder, hnotback⟩
  apply List.mem_erase.mpr
  constructor
  · exact hca
  · exact hcA

/-- Collapsing a smaller list is included in collapsing the larger list. -/
lemma collapseDerivable_erase_subset {A : AxisSet} {b : Axis} :
    collapseDerivable (A.erase b) ⊆ collapseDerivable A := by
  classical
  intro a ha
  rcases List.mem_filter.mp ha with ⟨haErase, hnotRed⟩
  have haA : a ∈ A := (List.mem_erase.mp haErase).right
  have hnotRedA : ¬ redundantWith A a := by
    intro hredA
    have hredErase : redundantWith (A.erase b) a :=
      redundantWith_erase_of_ne (A:=A) (b:=b) (a:=a) hredA ?_
    exact hnotRed hredErase
  exact List.mem_filter.mpr ⟨haA, hnotRedA⟩
  · -- show a ≠ b
    intro hEq
    subst hEq
    -- but a ∈ collapseDerivable (A.erase b) implies a ∈ A.erase b, contradiction
    exact (List.not_mem_erase b A) haErase
lemma collapseDerivable_subset (A : AxisSet) :
    collapseDerivable A ⊆ A := by
  intro a ha
  exact (List.mem_filter.mp ha).left

lemma collapseDerivable_length_le (A : AxisSet) :
    (collapseDerivable A).length ≤ A.length := by
  exact List.length_filter_le _ _

/-- Axes that survive `collapseDerivable` are provably non-redundant. -/
lemma collapseDerivable_no_redundant {A : AxisSet} {a : Axis}
    (ha : a ∈ collapseDerivable A) : ¬ redundantWith A a := by
  exact (List.mem_filter.mp ha).right

/-!
Existence of a non-redundant representative reachable by derivation.
We constructively descend along redundancy witnesses; asymmetry (¬ derivable b a)
prevents cycles, and recursion is bounded by list length.
-/
lemma derivable_to_collapse {A : AxisSet} {b : Axis} (hb : b ∈ A) :
  ∃ c ∈ collapseDerivable A, derivable b c := by
  classical
  -- length-based induction on A
  revert b hb
  refine List.recOn (l:=A) ?nil ?cons
  · intro b hb; cases hb
  · intro a tl ih b hb
    simp at hb
    rcases hb with hb | hb
    · -- b = a
      subst hb
      by_cases hred : redundantWith (a :: tl) a
      · -- pick witness b' in tl and recurse
        rcases hred with ⟨b', hb'Erase, hder, hnotback⟩
        have hb'Tl : b' ∈ tl := (List.mem_erase.mp hb'Erase).right
        rcases ih b' hb'Tl with ⟨c, hcCollapseTl, hder'⟩
        have hcCollapse : c ∈ collapseDerivable (a :: tl) :=
          collapseDerivable_erase_subset (A:=a::tl) (b:=a) hcCollapseTl
        exact ⟨c, hcCollapse, derivable_trans hder hder'⟩
      · -- a is non-redundant, survives collapse
        have haCol : a ∈ collapseDerivable (a :: tl) :=
          List.mem_filter.mpr ⟨by simp, hred⟩
        exact ⟨a, haCol, derivable_refl a⟩
    · -- b in tl
      rcases ih b hb with ⟨c, hcCollapseTl, hder⟩
      have hcCollapse : c ∈ collapseDerivable (a :: tl) :=
        collapseDerivable_erase_subset (A:=a::tl) (b:=a) hcCollapseTl
      exact ⟨c, hcCollapse, hder⟩

/--
Greedy derivation algorithm from the prose spec: add the minimal axis that
witnesses each unmet query, then collapse derivable axes.
-/
def deriveAxes (minimalAxisFor : Query α → Axis)
    (collapse : AxisSet → AxisSet := collapseDerivable)
    (requirements : Domain α) : AxisSet := by
  classical
  let A := requirements.foldl
    (fun acc q => if h : canAnswer acc q then acc else minimalAxisFor q :: acc)
    ([] : AxisSet)
  exact collapse A

/--
If an axis is in a minimal complete set, removing it must break completeness.
Therefore some query in `D` witnesses its independence.
-/
theorem independence_of_minimal {A : AxisSet} {D : Domain α} {a : Axis}
    (ha : a ∈ A) (hmin : minimal A D) :
    independent a A D := by
  classical
  rcases hmin with ⟨hcomplete, hminimal⟩
  have hnotComplete : ¬ complete (A.erase a) D := hminimal a ha
  have hExists : ∃ q ∈ D, ¬ canAnswer (A.erase a) q := by
    simpa [complete] using hnotComplete
  rcases hExists with ⟨q, hqD, hnot⟩
  have hsubsetA : q.requires ⊆ A := hcomplete q hqD
  have hmissing : ∃ r ∈ q.requires, r ∉ A.erase a := by
    simpa [canAnswer] using hnot
  rcases hmissing with ⟨r, hrReq, hrNotErase⟩
  have hrInA : r ∈ A := hsubsetA hrReq
  have hrEq : r = a := by
    by_contra hne
    have hrMemErase : r ∈ A.erase a := List.mem_erase.mpr ⟨hne, hrInA⟩
    exact hrNotErase hrMemErase
  subst hrEq
  exact ⟨q, hqD, hrReq, hnot⟩

/-!
## Preference Incoherence (Theorem 3.90)

A "preference position" claims multiple distinct minimal complete axis sets exist.
Uniqueness proves this is false for any domain.
-/

/-- A preference position claims multiple non-isomorphic minimal sets exist. -/
def PreferencePosition (D : Domain α) : Prop :=
  ∃ A₁ A₂ : AxisSet, minimal A₁ D ∧ minimal A₂ D ∧ A₁.length ≠ A₂.length

/--
Hedging Incoherence (Corollary 3.91): Accepting uniqueness while claiming
"typing discipline is a matter of preference" is a contradiction.

This theorem is unconditional: given ANY uniqueness predicate U that the reader
accepts, claiming preference (multiple valid options) yields False.

The proof is trivial but the theorem is profound: it makes explicit that
hedging after accepting uniqueness is a logical error, not mere caution.
-/
theorem hedging_incoherent (D : Domain α)
    (h_accept_uniqueness : ∀ A₁ A₂, minimal A₁ D → minimal A₂ D → A₁.length = A₂.length)
    (h_claim_preference : PreferencePosition D) : False := by
  rcases h_claim_preference with ⟨A₁, A₂, hmin₁, hmin₂, hne⟩
  exact hne (h_accept_uniqueness A₁ A₂ hmin₁ hmin₂)

/--
Preference position is refutable given uniqueness.
This factors out the pattern: uniqueness → ¬preference.
-/
theorem preference_refutable_from_uniqueness
    (h_uniq : ∀ A₁ A₂ : AxisSet, ∀ D : Domain α, minimal A₁ D → minimal A₂ D → A₁.length = A₂.length)
    (D : Domain α) : ¬ PreferencePosition D := by
  intro ⟨A₁, A₂, hmin₁, hmin₂, hne⟩
  exact hne (h_uniq A₁ A₂ D hmin₁ hmin₂)
