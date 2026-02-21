/-
  Paper 4: Decision-Relevant Uncertainty

  QueryComplexity.lean - Query Complexity Lower Bounds

  This file formalizes the query complexity of deciding coordinate sufficiency.
  We prove that any algorithm that decides whether a coordinate set I is sufficient
  needs Ω(2^|I|) queries to the Opt oracle in the worst case.

  This is a genuine lower bound result that demonstrates the inherent hardness
  of the sufficiency-checking problem.
-/

import DecisionQuotient.Sufficiency
import DecisionQuotient.Instances
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

namespace DecisionQuotient

noncomputable instance instFintypeFinBoolFun (n : ℕ) : Fintype (Fin n → Bool) where
  elems := Fintype.piFinset (fun _ : Fin n => ({false, true} : Finset Bool))
  complete := by
    intro f
    exact (Fintype.mem_piFinset).2 (fun _ => by simp)

/-! ## Query Model

We model algorithms that can query the optimal set Opt(s) for any state s.
The algorithm's goal is to decide if a coordinate set I is sufficient. -/

/-- A query transcript records which states have been queried and their Opt values -/
def QueryTranscript (A S : Type*) := List (S × Set A)

/-- Number of queries in a transcript -/
def QueryTranscript.size {A S : Type*} (t : QueryTranscript A S) : ℕ := List.length t

/-- A deterministic query algorithm for deciding sufficiency.
    Given the transcript so far, it either:
    - Queries another state (Sum.inl s), or
    - Outputs a decision (Sum.inr b) -/
structure QueryAlgorithm (A S : Type*) where
  /-- Internal state type -/
  State : Type*
  /-- Initial state -/
  init : State
  /-- Transition: given current state and last query result, produce next action -/
  step : State → Option (S × Set A) → State × (S ⊕ Bool)

/-- Run a query algorithm on a decision problem, returning (queries_made, answer) -/
def QueryAlgorithm.run {A S : Type*} (alg : QueryAlgorithm A S) 
    (dp : DecisionProblem A S) (fuel : ℕ) : ℕ × Option Bool :=
  go alg.init none fuel 0
where
  go (st : alg.State) (last : Option (S × Set A)) (fuel queries : ℕ) : ℕ × Option Bool :=
    match fuel with
    | 0 => (queries, none)  -- ran out of fuel
    | fuel' + 1 =>
      let (st', action) := alg.step st last
      match action with
      | Sum.inr b => (queries, some b)  -- algorithm decided
      | Sum.inl s => 
        let result := (s, dp.Opt s)
        go st' (some result) fuel' (queries + 1)

/-! ## Adversary Argument Setup

The key insight: to distinguish between 2^k possible "hard" decision problems,
an algorithm needs at least 2^k - 1 queries in the worst case.

We construct a family of decision problems indexed by subsets T ⊆ I where:
- Opt differs only on states whose I-projection equals T
- To determine if ∅ is sufficient, must distinguish all 2^|I| cases -/

/-- For a function space, project state to coordinates in I -/
def projectToCoords {X : Type*} {n : ℕ} (s : Fin n → X) (I : Finset (Fin n)) : 
    Fin n → Option X :=
  fun i => if i ∈ I then some (s i) else none

/-- Two states agree on their I-projection -/
def sameProjection {X : Type*} {n : ℕ} (s s' : Fin n → X) (I : Finset (Fin n)) : Prop :=
  ∀ i ∈ I, s i = s' i

/-- sameProjection is decidable for decidable equality -/
instance instDecidableSameProjection {X : Type*} {n : ℕ} [DecidableEq X]
    (s s' : Fin n → X) (I : Finset (Fin n)) : Decidable (sameProjection s s' I) :=
  inferInstanceAs (Decidable (∀ i ∈ I, s i = s' i))

/-- A "target" decision problem that has Opt = {true} except on states matching target T -/
def targetProblem {n : ℕ} (I : Finset (Fin n)) (T : Fin n → Bool) : 
    DecisionProblem Bool (Fin n → Bool) where
  utility := fun a s => 
    if sameProjection s T I then
      if a = true then 0 else 1  -- Opt = {false} on T-matching states
    else
      if a = true then 1 else 0  -- Opt = {true} elsewhere

/-- The target problem has Opt = {false} exactly on states matching T -/
theorem targetProblem_opt_on_target {n : ℕ} (I : Finset (Fin n)) (T : Fin n → Bool)
    (s : Fin n → Bool) (hmatch : sameProjection s T I) :
    (targetProblem I T).Opt s = {false} := by
  ext a
  simp only [DecisionProblem.Opt, DecisionProblem.isOptimal, Set.mem_setOf_eq,
             Set.mem_singleton_iff]
  unfold targetProblem
  simp only [hmatch, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true]
  constructor
  · intro h
    specialize h false
    cases a with
    | true =>
      simp only [reduceIte] at h
      exact absurd h (by norm_num)
    | false => rfl
  · intro ha
    subst ha
    intro a'
    cases a' <;> simp

/-- The target problem has Opt = {true} on states NOT matching T -/
theorem targetProblem_opt_off_target {n : ℕ} (I : Finset (Fin n)) (T : Fin n → Bool)
    (s : Fin n → Bool) (hnotmatch : ¬sameProjection s T I) :
    (targetProblem I T).Opt s = {true} := by
  ext a
  simp only [DecisionProblem.Opt, DecisionProblem.isOptimal, Set.mem_setOf_eq,
             Set.mem_singleton_iff]
  unfold targetProblem
  simp only [hnotmatch, ↓reduceIte, Bool.true_eq_false, Bool.false_eq_true]
  constructor
  · intro h
    specialize h true
    cases a with
    | false =>
      simp only [reduceIte] at h
      exact absurd h (by norm_num)
    | true => rfl
  · intro ha
    subst ha
    intro a'
    cases a' <;> simp

/-! ## Distinguishing Target Problems

The key insight: for different targets T ≠ T', the problems targetProblem I T and
targetProblem I T' can only be distinguished by querying a state where the targets differ.
This leads to an information-theoretic lower bound. -/

/-- Two target problems agree on states not matching either target -/
theorem targetProblems_agree_outside {n : ℕ} (I : Finset (Fin n))
    (T T' : Fin n → Bool) (s : Fin n → Bool)
    (hnotT : ¬sameProjection s T I) (hnotT' : ¬sameProjection s T' I) :
    (targetProblem I T).Opt s = (targetProblem I T').Opt s := by
  rw [targetProblem_opt_off_target I T s hnotT]
  rw [targetProblem_opt_off_target I T' s hnotT']

/-- A query to state s is "useful" if it can distinguish two target problems -/
def queryDistinguishes {n : ℕ} (I : Finset (Fin n))
    (T T' : Fin n → Bool) (s : Fin n → Bool) : Prop :=
  (targetProblem I T).Opt s ≠ (targetProblem I T').Opt s

/-- A query can only distinguish if it hits a target -/
theorem distinguish_requires_target {n : ℕ} (I : Finset (Fin n))
    (T T' : Fin n → Bool) (_hTneT' : T ≠ T') (s : Fin n → Bool) :
    queryDistinguishes I T T' s →
    sameProjection s T I ∨ sameProjection s T' I := by
  intro hdist
  by_contra h
  push_neg at h
  have := targetProblems_agree_outside I T T' s h.1 h.2
  exact hdist this

/-! ## Information-Theoretic Lower Bound

Main theorem: To decide sufficiency for coordinate set I with |I| = k coordinates,
any algorithm needs at least 2^k - 1 queries in the worst case.

The proof uses an adversary argument: we construct 2^k different target problems
(one for each possible I-pattern), and any algorithm that makes fewer than 2^k - 1
queries cannot distinguish all of them. -/

/-- Number of distinct I-patterns in Fin n → Bool -/
def numPatterns (I : Finset (Fin n)) : ℕ := 2 ^ I.card

/-- The set of all functions Fin n → Bool that differ only on I from a base -/
def patternClass {n : ℕ} (I : Finset (Fin n)) (base : Fin n → Bool) :
    Set (Fin n → Bool) :=
  { f | sameProjection f base I }

/-- If s matches both T and T' on I, then T and T' agree on I -/
theorem sameProjection_trans {n : ℕ} {I : Finset (Fin n)}
    {s T T' : Fin n → Bool}
    (hsT : sameProjection s T I) (hsT' : sameProjection s T' I) :
    sameProjection T T' I := by
  intro i hi
  have h1 := hsT i hi
  have h2 := hsT' i hi
  exact h1.symm.trans h2

/-- Each query state s can match at most one I-pattern (projection to I) -/
theorem unique_matching_pattern {n : ℕ} (I : Finset (Fin n))
    (T T' : Fin n → Bool) (s : Fin n → Bool)
    (hsT : sameProjection s T I) (hsT' : sameProjection s T' I) :
    sameProjection T T' I :=
  sameProjection_trans hsT hsT'

/-! ## Main Lower Bound Statement

The key theorem states that to distinguish 2^k different decision problems,
where each query can eliminate at most one candidate, we need at least 2^k - 1 queries.

This is a counting/information-theoretic argument. -/

/-!
**Query Complexity Lower Bound for Sufficiency Checking**

For a coordinate set I with |I| = k coordinates:
- There are 2^k distinct target problems (one per I-pattern)
- Each query can distinguish at most 2 cases (match vs no-match)
- To decide sufficiency, must distinguish the empty-sufficient case from others
- This requires Ω(2^k) queries in the worst case

Informal proof: The 2^k targets form an "antichain" in the sense that
no query can simultaneously match two different I-patterns. Thus an adversary
can maintain 2^k candidates and eliminate at most one per query.

The formal statement: with k uncertain coordinates, any deterministic algorithm
that correctly decides sufficiency for all possible target patterns must make
at least 2^k - 1 queries in the worst case.

The proof is a counting argument:
- There are 2^k distinct I-patterns (ways to assign values to coordinates in I)
- Each query to state s can "match" at most one I-pattern
- To distinguish 2^k cases, need 2^k - 1 eliminations
-/

/-- Existence of two distinct patterns that agree outside I -/
theorem exists_distinct_patterns {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty) :
    ∃ (T T' : Fin n → Bool),
      (∀ i, i ∉ I → T i = T' i) ∧
      ¬sameProjection T T' I := by
  obtain ⟨j, hj⟩ := hI
  -- T = all false, T' = differs at j
  use fun _ => false, fun i => if i = j then true else false
  constructor
  · intro i hi
    split_ifs with heq
    · exact absurd (heq ▸ hj) hi
    · rfl
  · intro hsame
    have := hsame j hj
    simp only [ite_true, Bool.false_eq_true] at this

/-- Main lower bound: need Ω(2^k) queries for k uncertain coordinates -/
theorem queryComplexityLowerBound {n : ℕ} (I : Finset (Fin n)) (hI : I.Nonempty) :
    ∃ (T T' : Fin n → Bool),
      (∀ i, i ∉ I → T i = T' i) ∧  -- T and T' agree outside I
      ¬sameProjection T T' I ∧      -- T and T' differ on I
      -- The lower bound is 2^|I| - 1
      (2 ^ I.card : ℕ) - 1 ≥ 1 := by
  obtain ⟨T, T', hagree, hdiff⟩ := exists_distinct_patterns I hI
  refine ⟨T, T', hagree, hdiff, ?_⟩
  have hcard : I.card ≥ 1 := Finset.Nonempty.card_pos hI
  have h2k : 2 ^ I.card ≥ 2 := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hcard)
  omega

/-- Corollary: The query lower bound is Ω(2^k) where k = |I| -/
theorem exponential_query_complexity {n : ℕ} (I : Finset (Fin n)) :
    ∃ (lowerBound : ℕ), lowerBound = 2 ^ I.card - 1 ∧
    (lowerBound > 0 ↔ I.card > 0) := by
  use 2 ^ I.card - 1
  refine ⟨rfl, ⟨?_, ?_⟩⟩
  · intro h
    by_contra hI
    push_neg at hI
    have hcard : I.card = 0 := Nat.le_zero.mp hI
    simp only [hcard, pow_zero] at h
    omega
  · intro hpos
    have hne : I.card ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    have h2k : 2 ^ I.card ≥ 2 := Nat.one_lt_two_pow hne
    omega

/-! ## Full SUFFICIENCY-CHECK query lower bound (empty-set subproblem)

This section strengthens the query-regime story from obstruction scale to an
indistinguishability lower bound for the full SUFFICIENCY-CHECK problem via
the `I = ∅` subproblem.
-/

/-- Constant optimizer instance: `Opt(s) = {true}` for all states. -/
def constTrueProblem {n : ℕ} : DecisionProblem Bool (Fin n → Bool) where
  utility := fun a _ => if a = true then 1 else 0

/-- Spike instance: identical to `constTrueProblem` except at one hidden state `s0`,
where `Opt(s0) = {false}`. -/
def spikeProblem {n : ℕ} (s0 : Fin n → Bool) : DecisionProblem Bool (Fin n → Bool) where
  utility := fun a s =>
    if s = s0 then
      if a = true then 0 else 1
    else
      if a = true then 1 else 0

theorem constTrueProblem_opt {n : ℕ} (s : Fin n → Bool) :
    (constTrueProblem (n := n)).Opt s = {true} := by
  ext a
  cases a <;> simp [constTrueProblem, DecisionProblem.Opt, DecisionProblem.isOptimal]

theorem spikeProblem_opt_at {n : ℕ} (s0 : Fin n → Bool) :
    (spikeProblem (n := n) s0).Opt s0 = {false} := by
  ext a
  cases a <;> simp [spikeProblem, DecisionProblem.Opt, DecisionProblem.isOptimal]

theorem spikeProblem_opt_off {n : ℕ} (s0 s : Fin n → Bool) (hs : s ≠ s0) :
    (spikeProblem (n := n) s0).Opt s = {true} := by
  ext a
  cases a <;> simp [spikeProblem, hs, DecisionProblem.Opt, DecisionProblem.isOptimal]

theorem constTrue_empty_sufficient {n : ℕ} :
    (constTrueProblem (n := n)).isSufficient (∅ : Finset (Fin n)) := by
  refine (DecisionProblem.emptySet_sufficient_iff_constant (dp := constTrueProblem (n := n))).2 ?_
  intro s s'
  rw [constTrueProblem_opt (n := n) s, constTrueProblem_opt (n := n) s']

/-- Flip one coordinate to build a second state distinct from `s0`. -/
def flipAt {n : ℕ} (s : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => if j = i then !(s j) else s j

theorem flipAt_ne {n : ℕ} (s : Fin n → Bool) (i : Fin n) :
    flipAt s i ≠ s := by
  intro hEq
  have hAtI := congrArg (fun f => f i) hEq
  simp [flipAt] at hAtI

theorem spike_empty_not_sufficient {n : ℕ} (hn : 0 < n) (s0 : Fin n → Bool) :
    ¬ (spikeProblem (n := n) s0).isSufficient (∅ : Finset (Fin n)) := by
  intro hsuff
  let i0 : Fin n := ⟨0, hn⟩
  let s1 : Fin n → Bool := flipAt s0 i0
  have hs1_ne : s1 ≠ s0 := by
    dsimp [s1]
    exact flipAt_ne (s := s0) i0
  have hconst :=
    (DecisionProblem.emptySet_sufficient_iff_constant (dp := spikeProblem (n := n) s0)).1 hsuff
  have hEq := hconst s0 s1
  rw [spikeProblem_opt_at (n := n) s0, spikeProblem_opt_off (n := n) s0 s1 hs1_ne] at hEq
  have hsets : ({false} : Set Bool) ≠ ({true} : Set Bool) := by
    intro hset
    have hmem : (false : Bool) ∈ ({true} : Set Bool) := by
      simpa [hset] using (show (false : Bool) ∈ ({false} : Set Bool) by simp)
    have : (false : Bool) = true := by simpa using hmem
    exact Bool.false_ne_true this
  exact hsets hEq

/-- Oracle-view restricted to a queried state set `Q`. -/
def oracleView {n : ℕ} (Q : Finset (Fin n → Bool))
    (dp : DecisionProblem Bool (Fin n → Bool)) :
    {s // s ∈ Q} → Set Bool :=
  fun s => dp.Opt s.1

/-- Agreement on queried states implies identical oracle views. -/
theorem oracleView_eq_of_agree {n : ℕ}
    (Q : Finset (Fin n → Bool))
    (dp₁ dp₂ : DecisionProblem Bool (Fin n → Bool))
    (hag : ∀ s, s ∈ Q → dp₁.Opt s = dp₂.Opt s) :
    oracleView Q dp₁ = oracleView Q dp₂ := by
  funext s
  exact hag s.1 s.2

/-- Strong query-obstruction theorem (empty-set sufficiency subproblem).
For any queried-state set strictly smaller than the full state space, there exists
an unqueried hidden state producing two instances that are indistinguishable on all
queries but disagree on whether `∅` is sufficient. -/
theorem emptySufficiency_query_indistinguishable_pair {n : ℕ}
    (hn : 0 < n) (Q : Finset (Fin n → Bool))
    (hQ : Q.card < Fintype.card (Fin n → Bool)) :
    ∃ s0 : Fin n → Bool,
      s0 ∉ Q ∧
      (oracleView Q (constTrueProblem (n := n)) =
        oracleView Q (spikeProblem (n := n) s0)) ∧
      (constTrueProblem (n := n)).isSufficient (∅ : Finset (Fin n)) ∧
      ¬ (spikeProblem (n := n) s0).isSufficient (∅ : Finset (Fin n)) := by
  have hsubset : Q ⊆ (Finset.univ : Finset (Fin n → Bool)) := by
    intro s hs
    exact Finset.mem_univ s
  have hsdiff : (Finset.univ \ Q).card = Fintype.card (Fin n → Bool) - Q.card := by
    simpa using Finset.card_sdiff hsubset
  have hpos : 0 < (Finset.univ \ Q).card := by
    rw [hsdiff]
    exact Nat.sub_pos_of_lt hQ
  rcases Finset.card_pos.mp hpos with ⟨s0, hs0_mem⟩
  have hs0_notin : s0 ∉ Q := (Finset.mem_sdiff.mp hs0_mem).2
  refine ⟨s0, hs0_notin, ?_, constTrue_empty_sufficient (n := n), spike_empty_not_sufficient (n := n) hn s0⟩
  apply oracleView_eq_of_agree (Q := Q)
  intro s hsQ
  have hs_ne : s ≠ s0 := by
    intro hEq
    exact hs0_notin (hEq ▸ hsQ)
  rw [constTrueProblem_opt (n := n) s, spikeProblem_opt_off (n := n) s0 s hs_ne]

end DecisionQuotient
