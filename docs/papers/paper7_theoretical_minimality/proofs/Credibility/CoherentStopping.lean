/-
# Coherent Stopping Points
-/

import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find

open Classical

namespace CoherentStopping

/-- A task system with agent actions and external propagation dynamics. -/
structure TaskSystem where
  State : Type
  initial : State
  goal : State → Prop
  propagation : State → State → Prop

variable {T : TaskSystem}

/-- Reflexive transitive closure of propagation. -/
def propagates (s s' : T.State) : Prop :=
  Relation.ReflTransGen T.propagation s s'

/-- A state is goal-determined if all propagation paths lead to the goal. -/
def goalDetermined (s : T.State) : Prop :=
  ∀ s', propagates s s' → T.goal s'

/-- Coherence of stopping. -/
def coherentToStop (s : T.State) : Prop := goalDetermined s

/-- Incoherence of stopping. -/
def incoherentToStop (s : T.State) : Prop := ¬ goalDetermined s

/-- Coherence is stable under further propagation. -/
theorem goalDetermined_stable (s s' : T.State)
    (h1 : goalDetermined s) (h2 : propagates s s') :
    goalDetermined s' := by
  intro s'' hs''
  exact h1 _ (Relation.ReflTransGen.trans h2 hs'')

/-- Corollary: once coherent, always coherent along propagation. -/
theorem coherentToStop_absorbing (s s' : T.State)
    (h1 : coherentToStop s) (h2 : propagates s s') :
    coherentToStop s' := goalDetermined_stable s s' h1 h2

/-- Every state is either coherent or not. -/
theorem stopping_dichotomy (s : T.State) :
    coherentToStop s ∨ incoherentToStop s := Classical.em _

/-- The last element of a nonempty list as a `get`. -/
lemma get_last {α : Type _} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.get ⟨l.length - 1, Nat.sub_lt (by
      cases l with
      | nil => cases h rfl
      | cons _ _ => simp) (by decide)⟩ = l.getLast! := by
  cases l with
  | nil => cases h rfl
  | cons a t =>
      cases t with
      | nil => simp
      | cons b t =>
          -- goal: last element of a (nonempty) tail
          have hpos : (b :: t).length - 1 < (b :: t).length := by simp
          have hidx : (b :: t).length - 1 = t.length := by simp
          have hget : (b :: t).get ⟨t.length, by simpa [hidx] using hpos⟩ =
              (b :: t).getLast (by simp) := by
            have := List.get_length_sub_one (l := b :: t) hpos
            simpa [hidx] using this
          have hlast! : (b :: t).getLast! = (b :: t).getLast (by simp) := by
            have hlast? : (b :: t).getLast? = some ((b :: t).getLast (by simp)) :=
              List.getLast?_eq_getLast_of_ne_nil (l := b :: t) (by simp)
            simp [List.getLast!, hlast?]
          simpa [hidx, hlast!] using hget

/-- Minimal coherent index exists when the trajectory ends coherently. -/
theorem sufficiency_threshold_exists [Inhabited T.State]
    (trajectory : List T.State)
    (h_nonempty : trajectory ≠ [])
    (h_start_incoherent : incoherentToStop trajectory.head!)
    (h_end_coherent : coherentToStop trajectory.getLast!) :
    ∃ i : Fin trajectory.length,
      coherentToStop (trajectory.get i) ∧
      ∀ j : Fin trajectory.length, j.val < i.val → incoherentToStop (trajectory.get j) := by
  classical
  -- length positivity
  have hlen_pos : 0 < trajectory.length := by
    cases trajectory with
    | nil => cases h_nonempty rfl
    | cons _ _ => simp

  -- Last index is coherent
  have hlast_coh :
      coherentToStop (trajectory.get ⟨trajectory.length - 1, Nat.sub_lt hlen_pos (by decide)⟩) := by
    -- rewrite the given coherence of `getLast!` to the `get` form
    have h_eq :
        trajectory.get ⟨trajectory.length - 1, Nat.sub_lt hlen_pos (by decide)⟩ =
          trajectory.getLast! :=
      get_last (l := trajectory) h_nonempty
    exact h_eq ▸ h_end_coherent

  -- Predicate over natural indices
  let P : Nat → Prop := fun n => ∃ h : n < trajectory.length, coherentToStop (trajectory.get ⟨n, h⟩)

  -- Concrete existence witness: last index
  have h_exists : ∃ n, P n := by
    refine ⟨trajectory.length - 1, ⟨Nat.sub_lt hlen_pos (by decide), hlast_coh⟩⟩

  -- Choose minimal coherent index by value
  let nmin : Nat := Nat.find h_exists
  have hmin_spec : P nmin := Nat.find_spec h_exists
  rcases hmin_spec with ⟨h_nmin_lt, h_nmin_coh⟩

  -- Package as a Fin
  let i : Fin trajectory.length := ⟨nmin, h_nmin_lt⟩
  have hi_coh : coherentToStop (trajectory.get i) := by simpa using h_nmin_coh

  -- Minimality: any earlier index is incoherent
  have h_prev :
      ∀ j : Fin trajectory.length, j.val < i.val → incoherentToStop (trajectory.get j) := by
    intro j hj_lt
    by_cases hcoh : coherentToStop (trajectory.get j)
    · -- coherence before i contradicts minimality
      have hPj : P j.val := ⟨j.is_lt, by simpa using hcoh⟩
      have hmin_le : nmin ≤ j.val := Nat.find_min' h_exists hPj
      have hcontr : False := (not_lt_of_ge hmin_le) hj_lt
      exact hcontr.elim
    · -- already incoherent
      exact hcoh

  exact ⟨i, hi_coh, h_prev⟩

end CoherentStopping
