# Lean 4 Credibility Proofs - Handoff Document

## Goal
Get all Lean 4 proofs in `docs/papers/paper5_credibility/proofs/` to compile successfully with `lake build`.

## Current Status
**Last action**: Added credibility domain distinction (mathematical vs social) to Basic.lean

---

## NEW: Credibility Domain Distinction (2026-01-14)

### What was added

**LaTeX** (`content/03_foundations.tex`):
- Section 2.0: Two Credibility Domains
- Definition 2.0a: Mathematical Credibility (logical soundness, audience = verifier)
- Definition 2.0b: Social Credibility (institutional acceptance, audience = humans)
- Theorem 2.0c: Domain Independence (orthogonality proof)
- Corollary 2.0d: Costly Signal Domain-Specificity
- Remark: The Pientka Phenomenon (conflict between domains)

**Lean** (`Credibility/Basic.lean`):
- `CredibilityDomain` inductive type (mathematical | social)
- `DomainSignalCost` structure with costs for both domains
- `isCostlyInMathDomain` / `isCostlyInSocialDomain` predicates
- `isCheapTalkInMathDomain` / `isCheapTalkInSocialDomain` predicates
- `domain_independence_math_not_implies_social` theorem (PROVEN)
- `domain_independence_social_not_implies_math` theorem (PROVEN)
- `machine_proof_domain_specificity` theorem (PROVEN)

### What still needs to be done

1. **Fix pre-existing CheapTalk.lean errors** (lines 33, 250)
2. **Add domain-parameterized versions of cheap talk theorems**:
   - `cheapTalkBound_in_domain : CredibilityDomain → ...`
   - Show that the bound formula applies within each domain separately
3. **Cross-domain interaction theorems** (optional, more advanced):
   - Formalize when high C_M can eventually shift C_S (e.g., via third-party verification)
   - Formalize when high C_S provides no information about C_M

### Build status

```bash
lake build Credibility.Basic  # ✅ PASSES (warnings only)
lake build                     # ❌ FAILS (pre-existing CheapTalk.lean issues)
```

---

## Previous Status
**Previous action**: Fixed type mismatch errors in `Leverage.lean` and `Impossibility.lean`

**Build command**: `lake build` (run from `docs/papers/paper5_credibility/proofs/`)

## Files in the Project

| File | Status | Notes |
|------|--------|-------|
| `Credibility/Basic.lean` | ⚠️ Warnings | Compiles but has unused variable warnings |
| `Credibility/CheapTalk.lean` | ⚠️ Warnings | Compiles but has unused variable warnings |
| `Credibility/CostlySignals.lean` | ⚠️ Warnings | Compiles but has linter suggestions |
| `Credibility/Leverage.lean` | ❓ Just Fixed | Fixed `div_le_div_of_nonneg_left` and `mul_le_mul_of_nonpos_left` argument order issues |
| `Credibility/Impossibility.lean` | ❓ Just Fixed | Fixed `div_lt_div_iff` → `div_lt_div_iff₀` and `mul_le_mul_of_nonneg_left` issues |

## Recent Fixes Applied

### Impossibility.lean (lines 176-220)
1. Changed `div_lt_div_iff` to `div_lt_div_iff₀` (Lean 4/Mathlib4 naming)
2. Rewrote the final `calc` step to properly use `mul_le_mul_of_nonneg_left` with correct argument structure

### Leverage.lean (lines 55-73)
1. Changed direct call to `div_le_div_of_nonneg_left` to use `div_le_div_iff₀` with `rw` then `mul_le_mul_of_nonneg_left`
2. The issue was argument order mismatch with the Mathlib4 API

## Next Steps

1. **Run `lake build`** to verify the fixes work
2. **If errors remain**: Check the exact error messages and fix accordingly
3. **Once compiling**: Optionally clean up linter warnings (unused variables, etc.)

## Common Patterns in This Codebase

- Uses Mathlib4 for real number proofs (`Real.exp`, `Real.log`, etc.)
- Division lemmas use `₀` suffix: `div_lt_iff₀`, `div_le_div_iff₀`
- Positivity conditions often need explicit `linarith` or `nlinarith` proofs
- `cheapTalkBound` is defined as `p / (p + (1 - p) * q)`

## Key Theorems Being Proved

1. **asymptotic_impossibility** (Impossibility.lean): As claim magnitude M → ∞, cheap-talk credibility → 0
2. **leverage_monotone** (Leverage.lean): Shorter text achieves at least as much leverage
3. **brevity_principle** (Leverage.lean): Wrapper around leverage_monotone

## Build Environment
- Lean 4 v4.27.0-rc1
- Uses Mathlib4
- lakefile.lean configured for the project

