import Mathlib.Data.Fintype.Card

/-!
  LWD Converse Counting Lemmas

  These lemmas formalize the finite counting core behind the paper's converse:
  to separate `a` colliding classes with zero error, any tag channel with `L`
  bits must satisfy `a ≤ 2^L`.
-/

namespace LWDConverse

/-- Any zero-error decoder for `a` colliding classes needs at least `a` outcomes. -/
theorem collision_block_requires_outcomes {a m : Nat}
    (decode : Fin a → Fin m) (hinj : Function.Injective decode) :
    a ≤ m := by
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective decode hinj

/-- With `L` tag bits, the number of tag outcomes is at most `2^L`. -/
theorem collision_block_requires_bits {a L : Nat}
    (decode : Fin a → Fin (2 ^ L)) (hinj : Function.Injective decode) :
    a ≤ 2 ^ L := by
  exact collision_block_requires_outcomes decode hinj

/-- Maximal-barrier special case: `k` colliding classes force `k ≤ 2^L`. -/
theorem maximal_barrier_requires_bits {k L : Nat}
    (decode : Fin k → Fin (2 ^ L)) (hinj : Function.Injective decode) :
    k ≤ 2 ^ L := by
  exact collision_block_requires_bits decode hinj

/-- Impossibility form: too few tag bits rules out zero-error separation. -/
theorem impossible_when_bits_too_small {a L : Nat}
    (hsmall : 2 ^ L < a) :
    ¬ ∃ decode : Fin a → Fin (2 ^ L), Function.Injective decode := by
  intro h
  rcases h with ⟨decode, hinj⟩
  have hle : a ≤ 2 ^ L := collision_block_requires_bits decode hinj
  exact Nat.not_lt_of_ge hle hsmall

end LWDConverse

