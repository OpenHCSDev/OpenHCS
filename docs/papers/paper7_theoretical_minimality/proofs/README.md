# Theoretical Minimality - Lean 4 Formalization

Machine-verified proofs for Paper 7: *Theoretical Minimality and Epistemological Uniqueness*

## Main Results

- **Theorem 3.1**: Unique Minimal Theory (∃! T, T.isMinimal)
- **Theorem 3.2**: Compression Necessity (infinite queries → |T| < |I|)  
- **Theorem 3.3**: Computability from Queries (T* = f(Queries(D)))
- **Theorem 4.1**: Incoherence of Pluralism (¬∃ distinct minimal theories)

## File Structure

```
TheoreticalMinimality/
├── Domain.lean           -- Domain, implementation definitions (Def 2.1-2.3)
├── Theory.lean           -- Theory as query-answer mapping (Def 2.4-2.6)
├── Minimality.lean       -- Minimality definitions (Def 2.7-2.9, Lemma 2.1)
├── Uniqueness.lean       -- Main uniqueness theorems (Thm 3.1-3.3)
├── AntiPluralism.lean    -- Anti-pluralism results (Thm 4.1-4.2)
├── Instances.lean        -- Papers 1-3 as instances (Section 6)
└── Framework.lean        -- DOF, compression, learnability (Thm 7.1-7.3)

Paper1Proofs/             -- Copied from paper1_typing_discipline/proofs/
├── python_instantiation.lean  -- Complexity gap theorem (duck vs nominal)
├── nominal_resolution.lean    -- Orthogonal axes minimality
└── ... (all Paper 1 proofs)

Paper2Proofs/             -- Copied from paper2_ssot/proofs/Ssot/
├── Foundations.lean      -- ⭐ UNIQUENESS THEOREM (template for Paper 7)
├── Coherence.lean        -- DOF = 1 guarantees coherence
├── Requirements.lean     -- SSOT language requirements
└── ... (all Paper 2 SSOT proofs)

Paper3Proofs/             -- Copied from paper3_leverage/proofs/Leverage/
├── Foundations.lean      -- Leverage maximization theorem
├── Probability.lean      -- Error minimization proofs
└── ... (all Paper 3 leverage proofs)
```

**Note**: Papers 1-3 proofs are copied for self-contained archival. When zipping Paper 7,
all dependencies are included. Import paths have been updated to use Paper*Proofs.* prefixes.

## Build

```bash
lake build
```

## Verification Status

| Module | Definitions | Theorems | Sorry Count |
|--------|-------------|----------|-------------|
| Domain.lean | 3 | 0 | 2 |
| Theory.lean | 4 | 0 | 2 |
| Minimality.lean | 4 | 2 | 0 |
| Uniqueness.lean | 3 | 4 | 4 |
| AntiPluralism.lean | 0 | 5 | 1 |
| Instances.lean | 6 | 4 | 3 |
| Framework.lean | 2 | 6 | 5 |
| **Total** | **22** | **21** | **17** |

Current focus: Completing uniqueness proof in Uniqueness.lean

## Key Concepts

**Domain**: Observable phenomena + query space  
**Implementation**: Complete state specification  
**Theory**: Function from queries to answers  
**Minimal Theory**: No proper subset answers all queries  
**Isomorphism**: Structure-preserving bijection between theories

## Dependencies

- Lean 4.13.0+
- Mathlib (latest)
