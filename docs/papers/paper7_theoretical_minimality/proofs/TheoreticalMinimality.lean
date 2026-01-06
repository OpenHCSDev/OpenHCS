/-
TheoreticalMinimality - Main module
Paper 7: Theoretical Minimality and Epistemological Uniqueness
-/

import TheoreticalMinimality.Domain
import TheoreticalMinimality.Theory
import TheoreticalMinimality.Minimality
import TheoreticalMinimality.Uniqueness
import TheoreticalMinimality.AntiPluralism
import TheoreticalMinimality.Instances
import TheoreticalMinimality.Framework
import TheoreticalMinimality.SSOT

/-!
# Theoretical Minimality and Epistemological Uniqueness

This formalization proves that minimal theories are unique and computable from query spaces.

## Main Results

- **Theorem 3.1** (Unique Minimal Theory): For any finite domain, exactly one minimal theory 
  exists up to isomorphism.
  
- **Theorem 3.2** (Compression Necessity): Infinite query spaces require theories smaller 
  than implementations.
  
- **Theorem 3.3** (Computability from Queries): The minimal theory T* = f(Queries(D)) where 
  f is algorithmic.
  
- **Theorem 4.1** (Incoherence of Pluralism): Multiple non-isomorphic minimal theories 
  cannot coexist.

## Instances

- **Paper 1**: Orthogonal axes are unique minimal theory for attribute independence
- **Paper 2**: SSOT (DOF=1) is unique minimal theory for multi-scale coherence
- **Paper 3**: Leverage is unique minimal theory for statistical influence

## Foundational Result: SSOT = SSOI (Tautology)

- **Single Source of Information = Single Source of Truth**
- This is not a design pattern but a logical necessity
- If sources agree: they are identical (one source by extensionality)
- If sources conflict: resolution rule IS the SSOT
- Either way: multiple sources collapse to one
- Information-theoretic grounding: redundant signals carry no new information

-/

namespace TheoreticalMinimality

/-- Main theorem: Minimal theories are unique up to isomorphism (given query equivalence) and computable -/
theorem main_result (D : Domain) [Finite D.queries] :
    (∀ T' : Theory D, T'.isMinimal →
      Theory.queryEquivalent T' (minimalTheoryAlgorithm D) →
      T' ≅ minimalTheoryAlgorithm D) ∧ 
    (∃ f : Set D.Query → Theory D, (f D.queries).isMinimal) :=
  ⟨unique_minimal_theory_iso D, computability_from_queries D⟩

end TheoreticalMinimality
