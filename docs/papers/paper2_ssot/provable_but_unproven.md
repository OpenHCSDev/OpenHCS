# Paper 2 IT Claims: Provable but Not Yet Formalized

Claims I believe are **true and provable** but not currently in the Lean formalization.

## 1. Fano-Style Converse (Theorem 6.2 in paper)

**Claim:** If $I(F;S) < \log K - \delta$ for $\delta > 0$, then any estimator $\hat{F}(S)$ has error probability bounded away from zero.

**Why provable:** This is standard Fano's inequality. The proof is in Cover & Thomas. Formalizing it requires:
- Define entropy $H(X) = -\sum p(x) \log p(x)$
- Define mutual information $I(X;Y) = H(X) - H(X|Y)$
- Prove Fano: $H(X|\hat{X}) \leq H_b(P_e) + P_e \log(|X|-1)$
- Apply to get the bound

**Lean approach:** Mathlib has entropy definitions. The proof is mechanical once you have the inequality.

## 2. Side-Information Bound as Entropy Argument (Theorem 3.8)

**Claim:** Resolution of $k$-way incoherence requires $\geq \log_2 k$ bits of side information.

**Currently proven:** The Lean proves `coherence_restoration_eq_dof` combinatorially (you need to specify which of $k$ locations is authoritative).

**What's missing:** The explicit entropy formulation: $H(S) = \log_2 k$ for uniform $S$ over $k$ alternatives, and $I(S;Y) \geq H(S)$ for perfect recovery.

**Why provable:** This is the source coding converse. Uniform distribution over $k$ symbols has entropy $\log_2 k$. Lossless recovery requires rate $\geq$ entropy.

## 3. Mutual Information Calculation (Section 6.4 worked example)

**Claim:** For $K=4$ values and $I(F;S)=1$ bit, Fano gives $P_e \gtrsim 0.19$.

**Why provable:** Direct calculation. $H(F|S) = 2 - 1 = 1$ bit. Solve $H_b(P_e) + P_e \log_2 3 \geq 1$ numerically.

**Lean approach:** This is computational. Define binary entropy, prove monotonicity, use interval arithmetic or exact rational bounds.

## 4. Derivation as Perfect Correlation

**Claim:** If $L_d$ is derived from $L_s$, then $H(L_d | L_s) = 0$.

**Why provable:** By definition of derivation, $L_d = f(L_s)$ for some deterministic $f$. Conditional entropy of a deterministic function of $X$ given $X$ is zero.

**Lean approach:**
```
theorem derived_zero_conditional_entropy
    (h : derives L_s L_d) : H(L_d | L_s) = 0
```
Requires formalizing conditional entropy and deterministic dependence.

## 5. DOF as Effective Rate in Multi-Terminal Model

**Claim:** DOF counts "independent sources" in the Slepian-Wolf sense. Derived locations contribute zero effective rate because $H(L_d | L_s) = 0$.

**Why provable:** In Slepian-Wolf, source $Y$ correlated with $X$ can be encoded at rate $H(Y|X)$. If $Y = f(X)$, then $H(Y|X) = 0$, so $Y$ needs zero rate given $X$.

**Lean approach:** Formalize the SW rate region, show derived locations lie on the boundary where their individual rate is 0.

## 6. Confusability Graph Connection

**Claim:** The "incoherence graph" (Definition 2.27) relates to Körner's confusability graph, and zero incoherence corresponds to graph with $|V| \leq 1$.

**Why provable:** The incoherence graph has vertices = independent locations, edges = potential disagreement. Zero incoherence requires the graph to be trivial (at most one vertex). This parallels zero-error capacity where capacity > 0 requires non-trivial independence number.

**Lean approach:** Define graph structure, prove the characterization theorem connecting graph size to achievability.

## 7. Rate-Incoherence Function is a Step Function (Theorem 2.22)

**Claim:**
$$R(\epsilon) = \begin{cases} 1 & \epsilon = 0 \\ \infty & \epsilon > 0 \end{cases}$$

**Currently proven:** The $\epsilon = 0$ case is proven (DOF=1 achieves zero incoherence).

**What's missing:** Formal statement that any DOF $\geq 1$ is achievable when $\epsilon > 0$ (i.e., no upper bound on rate when you tolerate incoherence).

**Why provable:** If you don't require coherence, you can have arbitrarily many independent locations. The constraint disappears.

---

## Summary Table

| Claim | In Lean? | Provable? | Difficulty |
|-------|----------|-----------|------------|
| DOF=1 ↔ coherence | Yes | - | - |
| Oracle arbitrariness | Yes | - | - |
| Trichotomy exhaustiveness | Yes | - | - |
| Model completeness (source_hooks unique) | Yes | - | - |
| Fano converse with entropy | No | Yes | Medium (need Mathlib entropy) |
| Side-info = log₂k entropy argument | No | Yes | Medium |
| Mutual info worked example | No | Yes | Easy (calculation) |
| Derivation = zero conditional entropy | No | Yes | Easy |
| SW rate region connection | No | Yes | Hard (full SW formalization) |
| Confusability graph characterization | No | Yes | Medium |
| Step function rate-incoherence | Partial | Yes | Easy |

---

## Recommendation

The highest-value additions to the Lean formalization would be:

1. **Entropy/MI definitions** - unlocks most of the IT claims
2. **Fano's inequality** - the workhorse converse tool
3. **Derivation → zero conditional entropy** - makes the "correlation" claim precise

These are all standard results with known proofs. The formalization effort is mechanical, not creative.
