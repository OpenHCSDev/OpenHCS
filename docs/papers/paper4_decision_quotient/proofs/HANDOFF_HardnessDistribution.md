# Simplicity Tax Theorem - Handoff Document

## Context

**File**: `docs/papers/proofs/DecisionQuotient/HardnessDistribution.lean`
**Status**: FULLY PROVEN (zero `sorry`)
**Last verified**: 2026-01-14

## Core Theorem

**Claim**: Using a simple tool for a complex problem is necessarily harder than using a tool matched to the problem's complexity.

**Formalization**: Problems have `requiredAxes`. Tools have `nativeAxes`. The gap `requiredAxes \ nativeAxes` is the **simplicity tax**—work pushed to users at each use site.

## Build Command

```bash
cd docs/papers/proofs
lake build DecisionQuotient.HardnessDistribution
```

## Current Theorems (All Proven)

| Theorem | Statement | Non-tautological? |
|---------|-----------|-------------------|
| `complete_tool_no_tax` | complete → tax = 0 | Yes (set theory) |
| `incomplete_tool_positive_tax` | incomplete → tax > 0 | Yes (set theory) |
| `simplicityTax_conservation` | tax + covered = required | Yes (partition) |
| `simplicityTax_grows` | n < m → n×tax < m×tax | Yes (arithmetic) |
| `more_expressive_dominates` | more coverage → lower tax | Yes (conservation) |
| `complete_dominates_incomplete` | complete beats incomplete | Yes (combines above) |
| `simplicity_preference_fallacy` | "prefer simple" backfires | Yes (main result) |

The key non-tautological insight is `simplicityTax_conservation`:
```lean
simplicityTax P T + (P.requiredAxes ∩ T.nativeAxes).card = P.requiredAxes.card
```
This is a partition of the required set—you can't reduce the total, only shift where it's paid.

## Optional Strengthening Proofs

### 1. Transitivity of Dominance

**Claim**: If T₁ dominates T₂ and T₂ dominates T₃, then T₁ dominates T₃.

```lean
theorem dominates_trans (T₁ T₂ T₃ : Tool)
    (h₁₂ : dominates P T₁ T₂) (h₂₃ : dominates P T₂ T₃) :
    dominates P T₁ T₃
```

**Proof sketch**: `dominates` is defined as `<` on ℕ, which is transitive.

**Difficulty**: Easy (one-liner with `Nat.lt_trans`)

### 2. Amortization Threshold

**Claim**: There exists a threshold n* such that for n > n*, the complex tool's learning cost is amortized.

```lean
/-- Learning cost for a complex tool -/
def learningCost (T : Tool) : ℕ := T.nativeAxes.card  -- or some function

/-- Total cost including learning -/
def totalCost (T : Tool) (n : ℕ) : ℕ :=
  learningCost T + totalExternalWork P T n

/-- Amortization threshold -/
theorem amortization_threshold (T_simple T_complex : Tool)
    (h_simple_incomplete : isIncomplete P T_simple)
    (h_complex_complete : isComplete P T_complex) :
    ∃ n_star : ℕ, ∀ n > n_star, totalCost P T_complex n < totalCost P T_simple n
```

**Proof sketch**:
- T_complex: totalCost = learningCost + 0×n = learningCost (constant)
- T_simple: totalCost = 0 + tax×n (grows linearly)
- For n > learningCost / tax, complex wins

**Difficulty**: Medium (need division and careful handling of ℕ)

### 3. Tool Composition

**Claim**: When composing tools, the simplicity tax of the composition relates to individual taxes.

```lean
/-- Compose two tools: union of native axes -/
def compose (T₁ T₂ : Tool) : Tool where
  nativeAxes := T₁.nativeAxes ∪ T₂.nativeAxes

/-- Composition reduces or preserves tax -/
theorem compose_reduces_tax (T₁ T₂ : Tool) :
    simplicityTax P (compose T₁ T₂) ≤ simplicityTax P T₁ ∧
    simplicityTax P (compose T₁ T₂) ≤ simplicityTax P T₂
```

**Proof sketch**: Union is larger, so gap is smaller or equal.

**Difficulty**: Easy (Finset monotonicity)

### 4. Partial Order on Tools

**Claim**: Tools form a partial order by expressiveness, and tax is antitone w.r.t. this order.

```lean
/-- T₁ ≤ T₂ if T₁'s native axes are a subset of T₂'s -/
def Tool.le (T₁ T₂ : Tool) : Prop := T₁.nativeAxes ⊆ T₂.nativeAxes

instance : LE Tool where le := Tool.le
instance : Preorder Tool where
  le := Tool.le
  le_refl := fun T => Finset.Subset.refl _
  le_trans := fun _ _ _ h₁ h₂ => Finset.Subset.trans h₁ h₂

/-- Tax is antitone: more expressive → less tax -/
theorem simplicityTax_antitone (T₁ T₂ : Tool) (h : T₁ ≤ T₂) :
    simplicityTax P T₂ ≤ simplicityTax P T₁
```

**Proof sketch**: Larger native set → smaller gap → smaller tax.

**Difficulty**: Easy (Finset.card_le_card + sdiff monotonicity)

### 5. Lattice Structure

**Claim**: Tools form a lattice with ⊓ = intersection, ⊔ = union of native axes.

```lean
instance : Lattice Tool where
  sup := compose  -- union
  inf := fun T₁ T₂ => ⟨T₁.nativeAxes ∩ T₂.nativeAxes⟩
  le_sup_left := ...
  le_sup_right := ...
  sup_le := ...
  inf_le_left := ...
  inf_le_right := ...
  le_inf := ...
```

**Difficulty**: Medium (need to prove all lattice axioms)

### 6. Connection to Paper 1's Axis Impossibility

**Claim**: The simplicity tax theorem generalizes Paper 1's `fixed_axis_incompleteness`.

Paper 1 says: "If axis a ∉ A, then A cannot answer queries requiring a."
Paper 4 says: "If you try anyway, you pay |missing axes| × n."

```lean
/-- Restate Paper 1's claim in Paper 4's language -/
theorem paper1_is_special_case :
    isIncomplete P T ↔ ∃ a ∈ P.requiredAxes, a ∉ T.nativeAxes
```

**Proof sketch**: Definition unfolding. `¬(R ⊆ A)` ↔ `∃ a ∈ R, a ∉ A`.

**Difficulty**: Trivial (definitional)

## Implementation Notes

1. **Standalone requirement**: Do NOT import from other papers. Users should be able to run proofs with a single `lake build`.

2. **Abstraction level**: Use `Finset ℕ` for axes. This is intentionally abstract—the theorems hold for any finite set of requirements.

3. **Mathlib dependencies**: Only `Mathlib.Data.Finset.Basic`, `Mathlib.Data.Finset.Card`, `Mathlib.Tactic`.

## LaTeX Reference

Section 6.4 of Paper 4: `docs/papers/paper4_decision_quotient/latex/content/06_implications_for_software_architecture.tex`

| LaTeX | Lean |
|-------|------|
| Definition 6.5 (Problem and Tool) | `Problem`, `Tool` |
| Definition 6.6 (Expressive Gap) | `expressiveGap` |
| Theorem 6.6 (Complete No Tax) | `complete_tool_no_tax` |
| Theorem 6.7 (Incomplete Positive Tax) | `incomplete_tool_positive_tax` |
| Theorem 6.8 (Tax Conservation) | `simplicityTax_conservation` |
| Theorem 6.9 (Tax Grows) | `simplicityTax_grows` |
| Theorem 6.10 (Complete Dominates) | `complete_dominates_incomplete` |
| Corollary 6.11 (Simplicity Fallacy) | `simplicity_preference_fallacy` |

## Success Criteria

1. `lake build DecisionQuotient.HardnessDistribution` completes with no errors
2. All theorems proven (no `sorry`)
3. Each optional strengthening proof compiles independently
4. No imports from Papers 1-3 (standalone)

