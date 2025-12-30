# Paper 2: SSOT Formalization — Unarguability Checklist

## What Made Paper 1 Unarguable

| Element | Paper 1 Status | Why It's Unarguable |
|---------|----------------|---------------------|
| Machine-checked proofs | 111 theorems, 0 sorry | Can't argue with `lake build` |
| Derived requirements | Capability gap from axioms | Not asserted, proven |
| Precise definitions | Formal in Lean | No wiggle room |
| Completeness theorems | Proves enumeration is exhaustive | Can't say "you missed X" |
| Preemptive rebuttals | Appendix addresses all objections | Reviewer's job done for them |
| Empirical validation | 13 case studies, PR #44 | Not just theory |
| Impossibility results | Information-theoretic bounds | Unconditional |

---

## Paper 2 Requirements (Matching Paper 1)

### Core Theorems to Machine-Check

- [ ] **Theorem 3.2**: Definition-time hooks are NECESSARY for structural SSOT
- [ ] **Theorem 3.4**: Introspection is NECESSARY for verifiable SSOT
- [ ] **Theorem 3.6**: Definition hooks + introspection are SUFFICIENT (completeness)
- [ ] **Theorem 6.1**: SSOT → O(1) modification complexity
- [ ] **Theorem 6.2**: Non-SSOT → Ω(n) modification complexity
- [ ] **Theorem 6.3**: Complexity gap is unbounded

### Definitions to Formalize in Lean

- [ ] `EditSpace` — set of valid modifications
- [ ] `Fact` — atomic unit of specification
- [ ] `Encodes(L, F)` — location L encodes fact F
- [ ] `DOF(C, F)` — degrees of freedom
- [ ] `SSOT(C, F)` — DOF = 1
- [ ] `Derived(L₁, L₂)` — L₂ derived from L₁
- [ ] `DefinitionTimeHook` — language feature predicate
- [ ] `Introspectable` — language feature predicate

### Language Evaluation (Exhaustive)

- [ ] Python: Prove satisfies all criteria
- [ ] Java: Prove fails (reflection too late)
- [ ] C++: Prove fails (templates opaque)
- [ ] Rust: Prove fails (macros opaque at runtime)
- [ ] TypeScript: Prove fails (types erased)
- [ ] Go, Kotlin, Swift, C#: Same pattern

### Preemptive Rebuttals

- [ ] "SSOT definition is too narrow" → Definition is derived from correctness
- [ ] "Other languages can approximate" → Approximation ≠ guarantee
- [ ] "Runtime metaprogramming suffices" → Too late for structure
- [ ] "Build tools can help" → External to language, not verifiable
- [ ] "This is just about Python" → Criteria derived first, Python evaluated second

### Empirical Validation

- [ ] Same 13 case studies, reanalyzed for DOF
- [ ] Before/after modification counts
- [ ] Concrete edit scenarios

---

## Folder Structure

```
docs/papers/paper2_ssot/
├── CHECKLIST.md          ← This file
├── latex/
│   ├── ssot_paper.tex    ← Main paper
│   └── references.bib    ← Shared with Paper 1
└── working/
    └── drafts/           ← Iteration drafts

proofs/ssot/
├── Basic.lean            ← EditSpace, Fact, Encodes, DOF
├── SSOT.lean             ← SSOT definition, optimality
├── Derivation.lean       ← Derivation relation
├── Requirements.lean     ← Necessity proofs
├── Completeness.lean     ← Iff theorem
├── Bounds.lean           ← O(1) vs Ω(n)
└── Languages.lean        ← Feature predicates, evaluations
```

---

## Timeline

- [ ] Lean proof skeleton (2-3 hours)
- [ ] Core theorems implemented (4-6 hours)
- [ ] `lake build` passes with 0 sorry (verify)
- [ ] LaTeX draft via same methodology as Paper 1 (4-6 hours)
- [ ] Preemptive rebuttals appendix (2 hours)
- [ ] Final review (2 hours)

**Total: 15-20 hours**

---

## Success Criteria

Paper 2 is unarguable when:

1. `cd proofs/ssot && lake build` succeeds with 0 sorry
2. Every theorem in the paper has a Lean counterpart
3. Language evaluations are exhaustive (top 10 TIOBE)
4. Complexity bounds are proven, not claimed
5. Appendix preempts all objections
6. Same structure as Paper 1 (readers know what to expect)

