/-
  Paper 4: Decision-Relevant Uncertainty

  Hardness/QBF.lean - Minimal QBF (∃∀-SAT) encoding

  This module provides a lightweight quantified Boolean formula framework
  for Σ₂ᴾ reductions. It is intentionally minimal: CNF over a sum of
  variables (existential X and universal Y), evaluation, and the
  ∃x ∀y satisfiability predicate.
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic

namespace DecisionQuotient

open Classical

/-! ## Generic CNF over an arbitrary variable type -/

/-- A Boolean literal over an arbitrary variable type. -/
structure QLiteral (Var : Type*) where
  var : Var
  polarity : Bool
  deriving DecidableEq, Repr

def QLiteral.map {Var W : Type*} (f : Var → W) (l : QLiteral Var) : QLiteral W :=
  { var := f l.var, polarity := l.polarity }

/-- Evaluate a literal under an assignment. -/
def QLiteral.eval {Var : Type*} (l : QLiteral Var) (assignment : Var → Bool) : Bool :=
  if l.polarity then assignment l.var else !assignment l.var

lemma QLiteral.eval_map {Var W : Type*} (f : Var → W) (l : QLiteral Var) (a : W → Bool) :
    QLiteral.eval (QLiteral.map f l) a = QLiteral.eval l (fun v => a (f v)) := by
  cases l
  simp [QLiteral.map, QLiteral.eval]

/-- A CNF clause is a disjunction of literals. -/
abbrev QClause (Var : Type*) := List (QLiteral Var)

/-- Map a clause by mapping its literals. -/
def QClause.map {Var W : Type*} (f : Var → W) (c : QClause Var) : QClause W :=
  List.map (fun l => QLiteral.map f l) c

/-- Evaluate a clause under an assignment. -/
def QClause.eval {Var : Type*} (c : QClause Var) (assignment : Var → Bool) : Bool :=
  c.any (fun l => QLiteral.eval l assignment)

lemma QClause.eval_map {Var W : Type*} (f : Var → W) (c : QClause Var) (a : W → Bool) :
    QClause.eval (QClause.map f c) a = QClause.eval c (fun v => a (f v)) := by
  induction c with
  | nil =>
      simp [QClause.map, QClause.eval]
  | cons l ls ih =>
      have ih' :
          ls.any ((fun l => l.eval a) ∘ fun l => QLiteral.map f l) =
            ls.any (fun l => l.eval fun v => a (f v)) := by
        simpa [QClause.map, QClause.eval, Function.comp] using ih
      simp [QClause.map, QClause.eval, QLiteral.eval_map, ih', Function.comp]

/-- A CNF formula is a conjunction of clauses. -/
abbrev QCNF (Var : Type*) := List (QClause Var)

/-- Map a CNF by mapping each clause. -/
def QCNF.map {Var W : Type*} (f : Var → W) (φ : QCNF Var) : QCNF W :=
  List.map (fun c => QClause.map f c) φ

/-- Evaluate a CNF formula under an assignment. -/
def QCNF.eval {Var : Type*} (φ : QCNF Var) (assignment : Var → Bool) : Bool :=
  φ.all (fun c => QClause.eval c assignment)

lemma QCNF.eval_map {Var W : Type*} (f : Var → W) (φ : QCNF Var) (a : W → Bool) :
    QCNF.eval (QCNF.map f φ) a = QCNF.eval φ (fun v => a (f v)) := by
  induction φ with
  | nil =>
      simp [QCNF.map, QCNF.eval]
  | cons c cs ih =>
      have ih' :
          cs.all ((fun c => c.eval a) ∘ fun c => QClause.map f c) =
            cs.all (fun c => c.eval fun v => a (f v)) := by
        simpa [QCNF.map, QCNF.eval, Function.comp] using ih
      simp [QCNF.map, QCNF.eval, QClause.eval_map, ih', Function.comp]

/-- Boolean evaluation agrees with the propositional predicate. -/
theorem qcnf_eval_eq_true_iff {Var : Type*} (φ : QCNF Var) (a : Var → Bool) :
    φ.eval a = true ↔ (∀ c ∈ φ, QClause.eval c a = true) := by
  unfold QCNF.eval
  induction φ with
  | nil =>
      simp
  | cons c cs ih =>
      simp [List.all_cons, ih]

/-! ## ∃∀-SAT (Σ₂ᴾ) Instances -/

abbrev AssignX (nx : ℕ) := Fin nx → Bool
abbrev AssignY (ny : ℕ) := Fin ny → Bool

/-- An ∃∀-SAT instance: a CNF over variables X ⊕ Y. -/
structure ExistsForallCNF where
  nx : ℕ
  ny : ℕ
  formula : QCNF (Sum (Fin nx) (Fin ny))

namespace ExistsForallCNF

/-- Combine X and Y assignments into a single assignment over `Sum`. -/
def sumAssignment {nx ny : ℕ} (x : AssignX nx) (y : AssignY ny) : Sum (Fin nx) (Fin ny) → Bool
  | Sum.inl i => x i
  | Sum.inr j => y j

/-- Satisfied by a pair of assignments. -/
def satisfiedBy (φ : ExistsForallCNF) (x : AssignX φ.nx) (y : AssignY φ.ny) : Prop :=
  φ.formula.eval (sumAssignment x y) = true

/-- ∃x ∀y satisfiability predicate. -/
def satisfiable (φ : ExistsForallCNF) : Prop :=
  ∃ x : AssignX φ.nx, ∀ y : AssignY φ.ny, φ.satisfiedBy x y

/-! ## Padding a universal variable (for ny = 0) -/

def embedVar {nx ny : ℕ} : Sum (Fin nx) (Fin ny) → Sum (Fin nx) (Fin (ny + 1))
  | Sum.inl i => Sum.inl i
  | Sum.inr j => Sum.inr (Fin.castLT j (Nat.lt_succ_of_lt j.isLt))

def padUniversal (φ : ExistsForallCNF) : ExistsForallCNF where
  nx := φ.nx
  ny := φ.ny + 1
  formula := QCNF.map (embedVar) φ.formula

def restrictY {ny : ℕ} (y : AssignY (ny + 1)) : AssignY ny :=
  fun j => y (Fin.castLT j (Nat.lt_succ_of_lt j.isLt))

lemma sumAssignment_embed {nx ny : ℕ} (x : AssignX nx) (y : AssignY (ny + 1)) :
    (fun v => sumAssignment x y (embedVar v)) = sumAssignment x (restrictY y) := by
  funext v
  cases v <;> simp [sumAssignment, restrictY, embedVar]

lemma eval_padUniversal (φ : ExistsForallCNF) (x : AssignX φ.nx) (y : AssignY (φ.ny + 1)) :
    (padUniversal φ).formula.eval (sumAssignment x y) =
      φ.formula.eval (sumAssignment x (restrictY y)) := by
  have hmap := (QCNF.eval_map (f := embedVar) (φ := φ.formula) (a := sumAssignment x y))
  simpa [padUniversal, sumAssignment_embed] using hmap

theorem satisfiable_iff_padUniversal (φ : ExistsForallCNF) :
    satisfiable φ ↔ satisfiable (padUniversal φ) := by
  constructor
  · intro hsat
    rcases hsat with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro y
    have hy := hx (restrictY y)
    have hmap := eval_padUniversal φ x y
    simpa [ExistsForallCNF.satisfiedBy] using hmap.trans hy
  · intro hsat
    rcases hsat with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro y
    -- extend y by ignoring the extra coordinate (set it to false)
    let y' : AssignY (φ.ny + 1) :=
      fun j =>
        if h : (j : Nat) < φ.ny then y ⟨j, h⟩ else false
    have := hx y'
    -- reduce to the original formula
    have hrest : restrictY y' = y := by
      funext j
      simp [restrictY, y', Fin.castLT, Fin.ext_iff]
    have hmap := eval_padUniversal φ x y'
    have h := hmap.symm.trans this
    simpa [ExistsForallCNF.satisfiedBy, hrest] using h

end ExistsForallCNF

end DecisionQuotient
