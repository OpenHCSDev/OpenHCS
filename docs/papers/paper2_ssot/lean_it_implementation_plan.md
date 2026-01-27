# Lean Implementation Plan: Information-Theoretic Foundations for Paper 2

## Goal

Formalize the information-theoretic claims in paper2_it that are currently argued informally. This closes the gap between the paper's IT framing and the Lean proofs.

## Current State

**Already proven (in `proofs/Ssot/`):**
- `Coherence.lean`: DOF=1 ↔ coherence, oracle arbitrariness, forcing theorem
- `Bounds.lean`: O(1) vs O(n) complexity (combinatorial)
- `Foundations.lean`: Trichotomy, mechanism exhaustiveness, model completeness
- `Requirements.lean`: Necessity of hooks + introspection

**Missing:** Entropy, mutual information, Fano's inequality, conditional entropy for derivation

---

## Phase 1: Entropy Foundations

**Goal:** Define Shannon entropy for finite discrete distributions

### File: `proofs/Ssot/Entropy.lean`

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Basic

/-- Finite probability distribution over n outcomes -/
structure FiniteDist (n : ℕ) where
  prob : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ prob i
  sum_one : ∑ i, prob i = 1

/-- Shannon entropy of a finite distribution -/
noncomputable def entropy {n : ℕ} (p : FiniteDist n) : ℝ :=
  -∑ i, if p.prob i = 0 then 0 else p.prob i * Real.log (p.prob i)

/-- Uniform distribution over n outcomes -/
def uniform (n : ℕ) (hn : n > 0) : FiniteDist n := ...

/-- Entropy of uniform distribution is log n -/
theorem entropy_uniform (n : ℕ) (hn : n > 0) :
    entropy (uniform n hn) = Real.log n := ...
```

### Theorems to prove:
1. `entropy_nonneg`: H(X) ≥ 0
2. `entropy_le_log_card`: H(X) ≤ log |support|
3. `entropy_uniform`: H(Uniform_n) = log n
4. `entropy_zero_iff`: H(X) = 0 ↔ X is deterministic

### Dependencies:
- Mathlib `Real.log` properties
- Summation over `Fin n`

### Effort: 3-4 days

---

## Phase 2: Joint and Conditional Entropy

**Goal:** Define H(X,Y), H(X|Y), and prove chain rule

### File: `proofs/Ssot/ConditionalEntropy.lean`

```lean
import Ssot.Entropy

/-- Joint distribution over two finite spaces -/
structure JointDist (m n : ℕ) where
  prob : Fin m → Fin n → ℝ
  nonneg : ∀ i j, 0 ≤ prob i j
  sum_one : ∑ i, ∑ j, prob i j = 1

/-- Marginal distribution on first coordinate -/
def marginal1 {m n : ℕ} (p : JointDist m n) : FiniteDist m := ...

/-- Conditional entropy H(Y|X) -/
noncomputable def condEntropy {m n : ℕ} (p : JointDist m n) : ℝ :=
  ∑ x, (marginal1 p).prob x * entropy (conditional p x)

/-- Joint entropy H(X,Y) -/
noncomputable def jointEntropy {m n : ℕ} (p : JointDist m n) : ℝ := ...
```

### Theorems to prove:
1. `chain_rule`: H(X,Y) = H(X) + H(Y|X)
2. `cond_entropy_nonneg`: H(Y|X) ≥ 0
3. `cond_entropy_le_entropy`: H(Y|X) ≤ H(Y)
4. `cond_entropy_zero_iff_deterministic`: H(Y|X) = 0 ↔ Y = f(X) for some f

### Key theorem for paper:
```lean
/-- Derivation implies zero conditional entropy -/
theorem derived_zero_cond_entropy {m n : ℕ} (p : JointDist m n)
    (f : Fin m → Fin n) (h : ∀ x y, p.prob x y > 0 → y = f x) :
    condEntropy p = 0 := ...
```

### Effort: 4-5 days

---

## Phase 3: Mutual Information

**Goal:** Define I(X;Y) and prove properties

### File: `proofs/Ssot/MutualInformation.lean`

```lean
import Ssot.ConditionalEntropy

/-- Mutual information I(X;Y) = H(X) - H(X|Y) -/
noncomputable def mutualInfo {m n : ℕ} (p : JointDist m n) : ℝ :=
  entropy (marginal1 p) - condEntropy (transpose p)
```

### Theorems to prove:
1. `mi_nonneg`: I(X;Y) ≥ 0
2. `mi_symmetric`: I(X;Y) = I(Y;X)
3. `mi_eq_entropy_minus_cond`: I(X;Y) = H(X) - H(X|Y)
4. `mi_zero_iff_independent`: I(X;Y) = 0 ↔ X ⊥ Y
5. `mi_eq_entropy_iff_deterministic`: I(X;Y) = H(X) ↔ X = f(Y)

### Key theorem for paper:
```lean
/-- Perfect recovery requires MI ≥ entropy -/
theorem recovery_requires_mi (p : JointDist m n)
    (h : ∃ f : Fin n → Fin m, ∀ x y, p.prob x y > 0 → f y = x) :
    mutualInfo p = entropy (marginal1 p) := ...
```

### Effort: 2-3 days

---

## Phase 4: Fano's Inequality

**Goal:** Prove Fano's inequality

### File: `proofs/Ssot/Fano.lean`

```lean
import Ssot.MutualInformation

/-- Binary entropy function -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  if p = 0 ∨ p = 1 then 0
  else -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- Fano's inequality -/
theorem fano_inequality {n : ℕ} (hn : n ≥ 2) (p : JointDist n n)
    (estimator : Fin n → Fin n)
    (P_e : ℝ) (hPe : P_e = ∑ x, ∑ y, if estimator y ≠ x then p.prob x y else 0) :
    condEntropy p ≤ binaryEntropy P_e + P_e * Real.log (n - 1) := ...
```

### Corollary for paper:
```lean
/-- If MI < log K - δ, error is bounded away from zero -/
theorem fano_converse {K : ℕ} (hK : K ≥ 2) (p : JointDist K n)
    (δ : ℝ) (hδ : δ > 0)
    (hMI : mutualInfo p < Real.log K - δ) :
    ∀ est : Fin n → Fin K, errorProb p est > 0 := ...
```

### Effort: 5-7 days (hardest part)

---

## Phase 5: Side Information Bound

**Goal:** Prove the log₂k bound for resolution

### File: `proofs/Ssot/SideInfoBound.lean`

```lean
import Ssot.Fano

/-- k-way incoherence has entropy log k under uniform prior -/
theorem incoherence_entropy (k : ℕ) (hk : k ≥ 2) :
    entropy (uniform k (by omega)) = Real.log k := entropy_uniform k _

/-- Resolution requires log k bits of side information -/
theorem resolution_requires_log_k (k : ℕ) (hk : k ≥ 2)
    (p : JointDist k n)  -- joint dist of source S and side-info Y
    (h_uniform : marginal1 p = uniform k (by omega))
    (h_resolves : ∃ f, errorProb p f = 0) :
    mutualInfo p ≥ Real.log k := by
  -- If error = 0, then H(S|Y) = 0, so I(S;Y) = H(S) = log k
  ...
```

### Link to existing Lean:
```lean
/-- Connect IT bound to combinatorial DOF bound -/
theorem side_info_eq_dof (k : ℕ) (hk : k ≥ 1) :
    (Real.log k) / (Real.log 2) = Real.logb 2 k := ...

/-- DOF = k implies log₂k bits needed -/
theorem dof_implies_side_info_bound (s : EncodingSystem) (hk : s.dof = k) (hk2 : k ≥ 2) :
    sideInfoRequired s ≥ Real.logb 2 k := ...
```

### Effort: 2-3 days

---

## Phase 6: Integration with Existing Proofs

**Goal:** Connect new IT theorems to existing combinatorial proofs

### File: `proofs/Ssot/ITBridge.lean`

```lean
import Ssot.SideInfoBound
import Ssot.Coherence
import Ssot.Bounds

/-- The IT capacity theorem: C₀ = 1 -/
theorem zero_incoherence_capacity :
    (∀ s : EncodingSystem, s.dof = 1 → ¬s.is_incoherent) ∧  -- achievability
    (∀ n > 1, ∃ s : EncodingSystem, s.dof = n ∧ s.is_incoherent) ∧  -- converse
    (∀ n > 0, (∀ s, s.dof = n → ¬s.is_incoherent) → n = 1) :=  -- capacity = 1
  ⟨dof_one_incoherence_impossible,
   dof_gt_one_incoherence_possible,
   determinate_truth_forces_ssot⟩

/-- Derivation in encoding systems corresponds to zero conditional entropy -/
theorem encoding_derivation_zero_entropy (D : DerivationSystem E)
    (e1 e2 : E) (h : D.derived_from e1 e2) :
    -- In the induced joint distribution, H(e2|e1) = 0
    condEntropyEncoding D e1 e2 = 0 := ...

/-- Rate-complexity has IT interpretation -/
theorem rate_complexity_it_interpretation :
    -- DOF = 1: I(F; all_locations) = H(F), complexity O(1)
    -- DOF = k: I(F; each_location) = H(F), must update k, complexity O(k)
    ∀ s : EncodingSystem, modificationComplexity s = s.dof :=
  coherence_restoration_eq_dof
```

### Effort: 2-3 days

---

## File Structure

```
proofs/Ssot/
├── Basic.lean           (existing)
├── SSOT.lean            (existing)
├── Coherence.lean       (existing)
├── Bounds.lean          (existing)
├── Foundations.lean     (existing)
├── Requirements.lean    (existing)
├── Derivation.lean      (existing)
├── Dof.lean             (existing)
│
├── Entropy.lean         (NEW - Phase 1)
├── ConditionalEntropy.lean  (NEW - Phase 2)
├── MutualInformation.lean   (NEW - Phase 3)
├── Fano.lean            (NEW - Phase 4)
├── SideInfoBound.lean   (NEW - Phase 5)
└── ITBridge.lean        (NEW - Phase 6)
```

---

## Implementation Order

```
Week 1:
  ├── Day 1-2: Entropy.lean (basic definitions)
  ├── Day 3-4: Entropy.lean (theorems)
  └── Day 5: ConditionalEntropy.lean (definitions)

Week 2:
  ├── Day 1-2: ConditionalEntropy.lean (chain rule, etc.)
  ├── Day 3-4: MutualInformation.lean
  └── Day 5: Start Fano.lean (binary entropy)

Week 3:
  ├── Day 1-3: Fano.lean (main inequality)
  ├── Day 4: SideInfoBound.lean
  └── Day 5: ITBridge.lean

Week 4:
  ├── Day 1-2: Polish and edge cases
  ├── Day 3: Update paper theorem references
  └── Day 4-5: Buffer / debugging
```

---

## Risk Mitigation

**Risk 1: Mathlib API churn**
- Mitigation: Pin Mathlib version, use stable APIs

**Risk 2: Real analysis edge cases (0 * log 0 = 0 convention)**
- Mitigation: Handle explicitly in definitions with `if p = 0 then 0 else ...`

**Risk 3: Fano proof complexity**
- Mitigation: Follow Cover & Thomas proof structure exactly; break into lemmas

**Risk 4: Scope creep (full SW formalization)**
- Mitigation: Explicitly out of scope. SW connection remains prose.

---

## Success Criteria

After implementation, the paper can claim:

> All theorems are machine-checked in Lean 4, including:
> - Zero-incoherence capacity theorem (Theorem X)
> - Side information bound via entropy (Theorem Y)
> - Fano-style converse (Theorem Z)
> - Derivation implies zero conditional entropy (Theorem W)
>
> The Slepian-Wolf and Körner graph entropy connections are interpretive
> and follow from standard information theory.

---

## Estimated Total Effort

| Phase | Effort | Cumulative |
|-------|--------|------------|
| 1. Entropy | 3-4 days | 4 days |
| 2. Conditional Entropy | 4-5 days | 9 days |
| 3. Mutual Information | 2-3 days | 12 days |
| 4. Fano's Inequality | 5-7 days | 19 days |
| 5. Side Info Bound | 2-3 days | 22 days |
| 6. Integration | 2-3 days | 25 days |
| Buffer | 3-5 days | 30 days |

**Total: ~4 weeks of focused work**

This assumes familiarity with Lean 4 and Mathlib. Add 1-2 weeks if learning curve needed.
