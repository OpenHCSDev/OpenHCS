/-
  SSOT Formalization - Formal Inconsistency Model

  This file responds to the critique that "inconsistency" was only in comments.
  Here we define ConfigSystem, inconsistency as a Prop, and prove that
  DOF > 1 implies the existence of inconsistent states.

  The interpretation "this models real configuration systems" still requires
  mapping to reality, but inconsistency is now a formal property Lean knows about.
-/

namespace Inconsistency

/-!
## Configuration System Model

A configuration system has multiple locations that can hold values for a fact.
Inconsistency means two locations disagree on the value.
-/

-- A value that a location can hold
abbrev Value := Nat

-- A location identifier
abbrev LocationId := Nat

-- A configuration system: maps locations to values
structure ConfigSystem where
  -- Number of independent locations encoding the same fact
  num_locations : Nat
  -- Value at each location
  value_at : LocationId → Value

-- Degrees of freedom = number of independent locations
def dof (c : ConfigSystem) : Nat := c.num_locations

-- Two valid locations hold different values
def locations_disagree (c : ConfigSystem) (l1 l2 : LocationId) : Prop :=
  l1 < c.num_locations ∧
  l2 < c.num_locations ∧
  l1 ≠ l2 ∧
  c.value_at l1 ≠ c.value_at l2

-- A configuration is inconsistent if any two locations disagree
def inconsistent (c : ConfigSystem) : Prop :=
  ∃ l1 l2, locations_disagree c l1 l2

-- A configuration is consistent if all locations agree
def consistent (c : ConfigSystem) : Prop :=
  ∀ l1 l2, l1 < c.num_locations → l2 < c.num_locations → c.value_at l1 = c.value_at l2

/-!
## Main Theorem: DOF > 1 Implies Potential Inconsistency

If there are 2+ independent locations, we can construct an inconsistent state
by setting them to different values.
-/

-- Create inconsistent state by setting loc 0 to 0 and loc 1 to 1
def make_inconsistent (n : Nat) : ConfigSystem where
  num_locations := n
  value_at := fun l => if l = 0 then 0 else 1

-- The constructed config is indeed inconsistent when n > 1
theorem make_inconsistent_is_inconsistent (n : Nat) (h : n > 1) :
    inconsistent (make_inconsistent n) := by
  unfold inconsistent locations_disagree make_inconsistent
  refine ⟨0, 1, ?_, ?_, ?_, ?_⟩
  · exact Nat.zero_lt_of_lt h
  · exact h
  · decide
  · simp only [ite_true]
    decide

/-!
## THE MAIN THEOREM

DOF > 1 implies there exists an inconsistent configuration.
This is now a formal property, not a comment.

The key insight: if you have 2+ independent locations, nothing prevents
setting them to different values. The "potential" for inconsistency is
demonstrated by constructing an actual inconsistent configuration.
-/

theorem dof_gt_one_implies_inconsistency_possible (n : Nat) (h : n > 1) :
    ∃ c : ConfigSystem, dof c = n ∧ inconsistent c := by
  refine ⟨make_inconsistent n, rfl, make_inconsistent_is_inconsistent n h⟩

-- Contrapositive: if you want to guarantee consistency, DOF must be ≤ 1
theorem consistency_requires_dof_le_one (n : Nat)
    (hall : ∀ c : ConfigSystem, dof c = n → consistent c) : n ≤ 1 := by
  match hn : n with
  | 0 => exact Nat.zero_le 1
  | 1 => exact Nat.le_refl 1
  | k + 2 =>
    -- n ≥ 2, so we can construct an inconsistent config
    have hgt : k + 2 > 1 := Nat.succ_lt_succ (Nat.zero_lt_succ k)
    have hincon := make_inconsistent_is_inconsistent (k + 2) hgt
    have hcons := hall (make_inconsistent (k + 2)) rfl
    -- But make_inconsistent is not consistent
    unfold consistent at hcons
    unfold inconsistent locations_disagree at hincon
    obtain ⟨l1, l2, hl1, hl2, _, hdiff⟩ := hincon
    have := hcons l1 l2 hl1 hl2
    exact absurd this hdiff

-- The unique optimum: DOF = 1 is the only value that:
-- 1. Allows encoding the fact (DOF ≥ 1)
-- 2. Guarantees consistency (DOF ≤ 1)
theorem ssot_is_unique_optimum (n : Nat) : (n ≥ 1 ∧ n ≤ 1) ↔ n = 1 := by
  omega

end Inconsistency

