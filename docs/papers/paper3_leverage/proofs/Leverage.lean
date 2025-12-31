/-
# Leverage-Driven Software Architecture

Main entry point for all leverage framework proofs.

This formalization supports Paper 3: "Leverage-Driven Software Architecture:
A Probabilistic Framework for Design Decisions"

Key modules:
- Foundations: Core definitions (Architecture, DOF, Capabilities, Leverage)
- Probability: Error probability model and theorems
- Theorems: Main results (leverage-error tradeoff, optimality criteria)
- SSOT: Instance showing Paper 2 fits the framework
- Typing: Instance showing Paper 1 fits the framework
- Examples: Concrete calculations for microservices, APIs, configuration, etc.

Statistics:
- Total theorems: 50+
- Sorries: 0 (all proofs complete)
- Lines: ~850+

All proofs are definitional or use decidable tactics (native_decide, omega, simp).
No axioms except standard Lean/Mathlib axioms.

Author: Formalized for Paper 3
Date: 2025-12-31
-/

import Leverage.Foundations
import Leverage.Probability
import Leverage.Theorems
import Leverage.SSOT
import Leverage.Typing
import Leverage.Examples
import Leverage.WeightedLeverage

/-!
## Summary of Key Results

### Foundations (Leverage/Foundations.lean)
- `Architecture`: Core structure with DOF and capabilities
- `ssot_dof_eq_one`: SSOT has DOF = 1
- `lower_dof_higher_leverage`: Same caps, lower DOF → higher leverage
- `ssot_max_leverage`: SSOT maximizes leverage for fixed capabilities
- `leverage_antimonotone_dof`: Leverage is anti-monotone in DOF

### Probability (Leverage/Probability.lean)
- `ErrorRate`: Discrete probability model
- `lower_dof_lower_errors`: Lower DOF → fewer expected errors
- `ssot_minimal_errors`: SSOT minimizes expected errors
- `compose_increases_error`: Composition increases error (DOF adds)

### Main Theorems (Leverage/Theorems.lean)
- `leverage_error_tradeoff`: Max leverage ⟹ min error (Theorem 3.1)
- `metaprogramming_unbounded_leverage`: Metaprog achieves unbounded leverage (Theorem 3.2)
- `optimal_minimizes_error`: Optimal architecture minimizes error (Theorem 3.4)
- `ssot_dominates_non_ssot`: SSOT dominates non-SSOT (same caps)
- `ssot_pareto_optimal`: SSOT is Pareto-optimal

### SSOT Instance (Leverage/SSOT.lean)
- `ssot_leverage_dominance`: SSOT dominates non-SSOT by factor n
- `ssot_modification_complexity`: Modification ratio = n
- `ssot_unbounded_advantage`: Advantage grows unbounded
- `only_definition_hooks_achieve_ssot`: Python uniqueness (cites Paper 2)

### Typing Instance (Leverage/Typing.lean)
- `nominal_dominates_duck`: Nominal > duck leverage (Theorem 4.2.6)
- `capability_gap`: Gap = 4 B-dependent capabilities
- `nominal_strict_dominance`: Nominal wins on all metrics
- `complexity_gap_unbounded`: Type checking gap unbounded

### Examples (Leverage/Examples.lean)
- Microservices vs Monolith calculations
- REST API design (generic vs specific)
- Configuration (convention over configuration)
- Database normalization
- Error probability scaling

### Weighted Leverage (Leverage/WeightedLeverage.lean)
- ValueFunction structure (assigns values to capabilities)
- weighted_leverage definition (generalized leverage metric)
- Performance/reliability/security as value functions
- `cache_optimal_for_performance`: Cache wins under performance value
- `direct_optimal_for_maintainability`: Direct wins under uniform value
- `pareto_optimal_iff_value_optimal`: Every Pareto-optimal architecture is optimal for SOME value function
- Universal principle: All architectural "tradeoffs" are weighted leverage maximization
-/
