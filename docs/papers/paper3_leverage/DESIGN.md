# Paper 3: Leverage-Driven Software Architecture

## Mathematical Foundations for Architectural Decision-Making

### Overview

This paper provides a unifying mathematical framework where Papers 1 and 2 are instances. The core insight: **architectural decisions should maximize leverage (capabilities per degree of freedom) to minimize error probability**.

---

## 1. Core Definitions

### Definition 1.1 (Architecture State Space)
An architecture A is a tuple (C, S, T, R) where:
- C = set of components (modules, services, endpoints, etc.)
- S = state space = ∏ᵢ Sᵢ (product of component state spaces)
- T = transformations: S → S (valid state transitions)
- R = requirements the architecture must satisfy

### Definition 1.2 (Degrees of Freedom - DOF)
DOF(A) = dim(S) = number of independent state variables in A

**Examples:**
- n independent services → DOF = n (each can be modified independently)
- n use sites with copied code → DOF = n
- 1 source with n derived sites → DOF = 1 (only source is independent)
- k API endpoints → DOF = k
- m configuration parameters → DOF = m

### Definition 1.3 (Capability Set)
Cap: Architecture → P(Requirements)
Cap(A) = {r ∈ Requirements | A satisfies r}

### Definition 1.4 (Leverage)
L(A) = |Cap(A)| / DOF(A)

**Interpretation**: How many capabilities does the architecture provide per degree of freedom?

**Special cases:**
- L = ∞: Infinite leverage (e.g., metaprogramming: 1 source, unlimited capabilities)
- L = 1: Linear (n capabilities from n DOF)
- L < 1: Negative leverage (more DOF than capabilities - antipattern)

### Definition 1.5 (Modification Complexity)
M(A, δR) = expected # of independent changes needed to implement requirement change δR

**Theorem 1.6 (DOF-Modification Correspondence)**
M(A, δR) ≤ DOF(A) with equality when δR affects all components.

---

## 2. Probability Model

### Axiom 2.1 (Independent Errors)
Each DOF has independent error probability p (constant per-component error rate).

### Axiom 2.2 (Error Propagation)
Errors in independent DOF compound multiplicatively.

### Theorem 2.3 (Error Probability Bound)
For architecture A with DOF(A) = n and per-component error rate p:

**P_error(A) = 1 - (1-p)^n**

For small p (p << 1):
**P_error(A) ≈ n·p**

**Proof:**
(1-p)^n = exp(n·ln(1-p)) ≈ exp(-n·p) ≈ 1 - n·p for small p.

**Corollary 2.4 (DOF-Error Monotonicity)**
DOF(A₁) < DOF(A₂) ⟹ P_error(A₁) < P_error(A₂)

---

## 3. Main Theorems

### Theorem 3.1 (Leverage-Error Tradeoff)
For fixed capability set C, maximizing leverage minimizes error probability.

**Proof:**
- L = |C|/DOF, so max L ⟹ min DOF (for fixed |C|)
- By Corollary 2.4: min DOF ⟹ min P_error
- Therefore: max L ⟹ min P_error ∎

### Theorem 3.2 (Metaprogramming Dominance)
Metaprogramming (derivation from single source) achieves unbounded leverage.

**Proof:**
- Source S can derive unlimited capabilities: |Cap(meta)| → ∞
- DOF(meta) = 1 (only source is independent)
- L_meta = |Cap|/1 → ∞ ∎

### Theorem 3.3 (SSOT Optimality for Structural Facts)
For structural facts, SSOT achieves optimal (infinite) leverage.

**Formal statement:**
Given structural fact F with n use sites:
- SSOT: DOF = 1, M(change F) = 1
- Non-SSOT: DOF = n, M(change F) = n
- L_SSOT / L_non-SSOT = n

**Proof:** Cite Paper 2, Theorem 2.2 (SSOT Optimality)

### Theorem 3.4 (Architectural Decision Criterion)
Given requirements R, optimal architecture A* satisfies:
1. Cap(A*) ⊇ R (feasibility: meets all requirements)
2. ∀A' with Cap(A') ⊇ R: L(A*) ≥ L(A') (optimality: maximum leverage)

**Interpretation:** Choose the architecture with fewest DOF that still meets requirements.

### Theorem 3.5 (Expected Error Bound)
E[# errors in A] ≤ p · DOF(A)

where p = per-component error probability.

**Proof:**
By linearity of expectation:
E[errors] = Σᵢ P(error in DOFᵢ) = Σᵢ p = n·p = p·DOF(A) ∎

### Theorem 3.6 (Leverage Composition)
For modular architecture A = A₁ ⊕ A₂:
- DOF(A) = DOF(A₁) + DOF(A₂)
- If modules are independent: L(A) ≥ min(L(A₁), L(A₂))

**Proof:** Leverage is bounded below by worst submodule.

---

## 4. Instances (Applications)

### 4.1 SSOT (Single Source of Truth) - Paper 2
- **Domain**: Structural facts in codebases
- **DOF_SSOT**: 1 (single definition)
- **DOF_non-SSOT**: n (scattered definitions)
- **Leverage**: L = n (cite Paper 2, Theorem 6.3)
- **Theorem**: Python uniquely provides SSOT for structural facts (Paper 2, Theorem 4.2)

### 4.2 Nominal Typing - Paper 1
- **Domain**: Type disciplines
- **Capabilities**: {provenance, identity, enumeration, conflict resolution}
- **DOF_nominal**: Requires B axis (bases/names)
- **DOF_duck**: Only S axis (shape)
- **Leverage**: Nominal > Duck (4 capabilities vs 0 for provenance)
- **Theorem**: Nominal strictly dominates (Paper 1, Theorem 3.5)

### 4.3 Microservices Architecture
- **DOF**: n services
- **Capabilities**: Independent scaling, deployment, team autonomy, fault isolation
- **Leverage calculation**:
  - Monolith: DOF = 1, Cap = {scaling, fault-tolerance}
  - n Services: DOF = n, Cap = {independent-scale, independent-deploy, ...}
  - Optimal n: Maximize |Cap|/n subject to communication overhead

### 4.4 API Design
- **DOF**: k endpoints
- **Leverage**: |use-cases| / k
- **High leverage**: Generic endpoint (GET /resources/:id) → many use cases
- **Low leverage**: Specific endpoint per use case → 1:1 ratio

### 4.5 Configuration Systems
- **DOF**: m configuration parameters
- **Convention over configuration**: DOF = 0 for defaults, pay DOF only when customizing
- **Leverage**: Capabilities / (m - m_defaulted)

### 4.6 Database Schema
- **DOF**: Tables × Columns
- **Normalization**: Reduce DOF while preserving capabilities
- **Denormalization**: Increase DOF for performance (explicit tradeoff)

---

## 5. Lean Proof Structure

```
proofs/leverage/
├── lakefile.lean                    # Build configuration
└── Leverage/
    ├── Foundations.lean             # Definitions 1.1-1.5
    ├── Probability.lean             # Axioms 2.1-2.2, Theorem 2.3-2.4
    ├── Theorems.lean                # Theorems 3.1-3.6
    ├── SSOT.lean                    # Instance 4.1 (imports ../ssot/)
    ├── Typing.lean                  # Instance 4.2 (imports Paper 1 proofs)
    ├── Microservices.lean           # Instance 4.3
    ├── APIs.lean                    # Instance 4.4
    ├── Configuration.lean           # Instance 4.5
    └── Examples.lean                # Concrete calculations
```

---

## 6. Paper Structure

### Abstract
- First formal framework for architectural decision-making
- Leverage = capabilities / DOF
- P(error) ~ DOF, so max leverage ⟹ min error
- Unifies SSOT (Paper 2) and nominal typing (Paper 1) as instances
- Machine-checked in Lean 4

### 1. Introduction
- Architectural decisions lack formal framework
- Propose: Leverage maximization as universal principle
- Show: Papers 1 & 2 are instances

### 2. Foundations
- Definitions 1.1-1.5
- Probability model (Axioms 2.1-2.2)

### 3. Main Results
- Theorems 3.1-3.6
- Proofs

### 4. Instances
- 4.1-4.6 with concrete examples

### 5. Empirical Validation
- Case studies from OpenHCS
- Quantify leverage for each architectural decision

### 6. Related Work
- Software architecture metrics (coupling, cohesion)
- Design patterns
- Technical debt

### 7. Conclusion
- Leverage as unifying principle
- Decision procedure: max L subject to Cap(A) ⊇ R

### Appendix A: Lean Proofs
- Full proof listings

---

## 7. Key Theorems to Machine-Check in Lean

**Must prove (0 sorries):**
1. Theorem 2.3 (Error Probability Bound)
2. Theorem 3.1 (Leverage-Error Tradeoff)
3. Theorem 3.2 (Metaprogramming Dominance)
4. Theorem 3.5 (Expected Error Bound)
5. Theorem 3.6 (Leverage Composition)

**Can reference Papers 1 & 2:**
- Theorem 3.3 (SSOT Optimality) ← Paper 2
- Instance 4.2 (Nominal Typing) ← Paper 1

---

## 8. Relationship to Papers 1 & 2

### Paper 1: Nominal Typing
- **Leverage perspective**: Nominal typing has higher leverage than duck typing
- B axis provides 4 capabilities (provenance, identity, enumeration, conflict)
- Duck typing: 0 of these capabilities
- Same DOF cost (both are typing disciplines)
- Therefore: L_nominal > L_duck

### Paper 2: SSOT
- **Leverage perspective**: SSOT achieves infinite leverage
- 1 source (DOF = 1) → unlimited derivations
- L = ∞ (theoretically maximal)
- Python uniquely provides this for structural facts

### Paper 3: Unifying Framework
- Shows both are instances of leverage maximization
- Provides decision procedure applicable beyond PL
- Extends to system architecture, APIs, schemas, configuration

---

## 9. Target Venues

### Primary: ICSE (International Conference on Software Engineering)
- Broader audience than TOPLAS
- Architecture focus
- Empirical validation valued

### Secondary: FSE (Foundations of Software Engineering)
- Theory + practice blend
- Formal methods track

### Fallback: IEEE Software (if need broader impact)
- Practitioner audience
- Shorter format

---

## 10. Implementation Plan

1. **Phase 1**: Lean proofs (Foundations, Probability, Theorems)
2. **Phase 2**: SSOT/Typing instances (link to Papers 1 & 2)
3. **Phase 3**: New instances (Microservices, APIs, Config)
4. **Phase 4**: LaTeX paper (TOPLAS template for consistency)
5. **Phase 5**: Case studies from OpenHCS
6. **Phase 6**: Verify 0 sorries, all theorems cited exist

---

## Status: Ready for Implementation

All mathematical foundations designed. Ready to write Lean proofs and LaTeX.
