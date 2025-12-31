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
- Total theorems: 40+
- Sorries: Multiple (to be completed)
- Lines: ~500+

Author: Formalized for Paper 3
Date: 2025-12-30
-/

import Leverage.Foundations
import Leverage.Probability
import Leverage.Theorems
import Leverage.SSOT
import Leverage.Typing
import Leverage.Examples
