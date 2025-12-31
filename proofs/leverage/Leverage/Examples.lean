/-
# Leverage Framework - Concrete Examples

This module provides concrete calculations of leverage for various
architectural decisions.

Examples:
- Microservices vs Monolith
- REST API design
- Configuration systems
- Database normalization

Author: Examples for Paper 3
Date: 2025-12-30
-/

import Leverage.Foundations
import Leverage.Theorems

namespace Leverage.Examples

/-- Example 1: Microservices Architecture -/
section Microservices

/-- Monolithic architecture: single deployment unit -/
def monolith_arch (caps : Set String) : Architecture :=
  { components := sorry  -- Single component
  , requirements := caps }

/-- Microservices architecture: n independent services -/
def microservices_arch (n : Nat) (caps : Set String) : Architecture :=
  { components := sorry  -- n components
  , requirements := caps }

/-- Calculate DOF for monolith -/
axiom monolith_dof : (monolith_arch sorry).dof = 1

/-- Calculate DOF for n microservices -/
axiom microservices_dof (n : Nat) : (microservices_arch n sorry).dof = n

/-- Capabilities gained by microservices -/
def microservice_capabilities : Set String :=
  { "independent_scaling"
  , "independent_deployment"
  , "fault_isolation"
  , "team_autonomy"
  , "polyglot_persistence" }

/-- Example calculation: 5 microservices -/
example :
    let mono := monolith_arch {"basic_functionality"}
    let micro := microservices_arch 5 ({"basic_functionality"} ∪ microservice_capabilities)
    micro.capabilities.ncard > mono.capabilities.ncard ∧
    micro.dof > mono.dof := by
  sorry

end Microservices

/-- Example 2: REST API Design -/
section APIs

/-- Specific endpoints: one per use case -/
def specific_api (n_usecases : Nat) : Architecture :=
  { components := sorry  -- n endpoints
  , requirements := sorry }

/-- Generic endpoint: handles many use cases -/
def generic_api (n_usecases : Nat) : Architecture :=
  { components := sorry  -- 1 generic endpoint
  , requirements := sorry }

axiom specific_api_dof (n : Nat) : (specific_api n).dof = n
axiom generic_api_dof (n : Nat) : (generic_api n).dof = 1

/-- Example: 10 use cases -/
example :
    let spec := specific_api 10
    let gen := generic_api 10
    gen.leverage > spec.leverage := by
  sorry
  -- L(gen) = 10/1 = 10
  -- L(spec) = 10/10 = 1
  -- 10 > 1

end APIs

/-- Example 3: Configuration Systems -/
section Configuration

/-- Explicit configuration: must set every parameter -/
def explicit_config (n_params : Nat) : Architecture :=
  { components := sorry
  , requirements := sorry }

/-- Convention over configuration: only set overrides -/
def convention_config (n_params : Nat) (n_overrides : Nat) : Architecture :=
  { components := sorry
  , requirements := sorry }

axiom explicit_config_dof (n : Nat) : (explicit_config n).dof = n
axiom convention_config_dof (n m : Nat) : (convention_config n m).dof = m

/-- Example: 100 parameters, 5 overrides -/
example :
    let explicit := explicit_config 100
    let convention := convention_config 100 5
    convention.leverage > explicit.leverage := by
  sorry
  -- Same capabilities (100 parameters configurable)
  -- L(explicit) = 100/100 = 1
  -- L(convention) = 100/5 = 20
  -- 20 > 1

end Configuration

/-- Example 4: Database Schema Design -/
section Database

/-- Denormalized schema: redundant data -/
def denormalized_schema (n_redundant : Nat) : Architecture :=
  { components := sorry
  , requirements := sorry }

/-- Normalized schema: single source of truth for each fact -/
def normalized_schema : Architecture :=
  { components := sorry
  , requirements := sorry }

axiom denorm_dof (n : Nat) : (denormalized_schema n).dof = n
axiom norm_dof : normalized_schema.dof = 1

/-- Example: Customer address stored in 3 tables (denorm) vs 1 (norm) -/
example :
    let denorm := denormalized_schema 3
    let norm := normalized_schema
    norm.leverage > denorm.leverage := by
  sorry

end Database

/-- Example 5: Error Probability Calculation -/
section ErrorProbability

open Probability

/-- Given p = 0.01 (1% error per component) -/
axiom example_error_rate : per_component_error_rate = 0.01

/-- Calculate error probability for various DOF -/
example : error_probability 1 < 0.01 := by sorry
example : error_probability 10 < 0.10 := by sorry
example : error_probability 100 < 1.0 := by sorry

/-- Show error grows approximately linearly for small p -/
example (h : per_component_error_rate = 0.01) :
    |error_probability 10 - 0.10| < 0.005 := by
  sorry

end ErrorProbability

end Leverage.Examples
