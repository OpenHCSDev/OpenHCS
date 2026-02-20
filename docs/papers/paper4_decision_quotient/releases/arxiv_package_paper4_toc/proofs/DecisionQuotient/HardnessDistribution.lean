/-
  Paper 4: Decision Quotient

  HardnessDistribution.lean - Hardness distribution grounded in Papers 2-4

  GROUNDING:
  - Hardness := DOF (Paper 2) - the minimal independent encoding count
  - Error sites := DOF (Paper 2) - where inconsistencies can occur
  - Centralization := moving DOF to shared component
  - Conservation := information-theoretic: you can't encode less than the fact requires
  - Leverage connection := capabilities / DOF (Paper 3)

  Key insight: "Hardness" is not abstract - it IS the DOF count.
  A fact requires k independent bits to encode. You either:
  1. Pay k once (central: type system encodes it)
  2. Pay k × n times (distributed: each site re-encodes it)

  LaTeX reference: Section 6.4 (Hardness Distribution: Right Place vs Wrong Place)
-/

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace DecisionQuotient.HardnessDistribution

/-! ## Grounding in Paper 2: DOF as Hardness

From Paper 2 (Dof.lean):
- An Encoding is a (fact, location, value) tuple
- DOF = |minimalIndependentCore(encodings)|
- DOF is the count of encodings not derivable from others

Hardness IS DOF: the minimum number of independent specifications required.
-/

/-- A specification problem: something that must be encoded at use sites.
    intrinsicDOF is the minimum independent encodings required (from Paper 2). -/
structure SpecificationProblem where
  /-- Minimum independent encodings required (Paper 2: size of minimal independent core) -/
  intrinsicDOF : ℕ
  /-- Must specify at least one thing -/
  dof_pos : intrinsicDOF > 0

/-- A solution architecture partitions DOF between central and per-site.

    Central: encoded once in shared component (type system, library, framework)
    Distributed: encoded at each use site

    Conservation: central + distributed ≥ intrinsic (you can't compress below DOF) -/
structure SolutionArchitecture (P : SpecificationProblem) where
  /-- DOF handled centrally (paid once) -/
  centralDOF : ℕ
  /-- DOF handled per-site (paid n times) -/
  distributedDOF : ℕ
  /-- Conservation: must cover the intrinsic DOF -/
  conservation : centralDOF + distributedDOF ≥ P.intrinsicDOF

/-! ## Error Sites = DOF (Paper 2 Connection)

From Paper 2: each independent encoding is a site where inconsistency can occur.
Error sites for a solution = 1 (central component) + n × distributedDOF (per-site encodings).
-/

/-- Total error sites: central component (1 if any central DOF) + per-site encodings -/
def errorSites (S : SolutionArchitecture P) (n : ℕ) : ℕ :=
  (if S.centralDOF > 0 then 1 else 0) + n * S.distributedDOF

/-- Total specification effort: DOF paid once centrally + DOF paid n times distributed -/
def totalDOF (S : SolutionArchitecture P) (n : ℕ) : ℕ :=
  S.centralDOF + n * S.distributedDOF

/-! ## Hardness Conservation (Information-Theoretic)

You cannot encode k independent facts with fewer than k independent specifications.
This is not an axiom - it follows from the definition of independence in Paper 2.
-/

/-- Theorem: Conservation is a structure invariant -/
theorem dof_conservation (P : SpecificationProblem) (S : SolutionArchitecture P) :
    S.centralDOF + S.distributedDOF ≥ P.intrinsicDOF :=
  S.conservation

/-! ## Centralization Dominance

Core theorem: for n > 1, centralizing DOF reduces both total effort and error sites.
-/

/-- Distributed DOF multiplies with use sites -/
theorem distributed_multiplies (S : SolutionArchitecture P) (n₁ n₂ : ℕ)
    (hn : n₁ < n₂) (hd : S.distributedDOF > 0) :
    totalDOF S n₁ < totalDOF S n₂ := by
  unfold totalDOF
  have h : n₁ * S.distributedDOF < n₂ * S.distributedDOF := Nat.mul_lt_mul_of_pos_right hn hd
  omega

/-- Lower distributed DOF means lower total DOF for any n ≥ 1 -/
theorem less_distributed_less_total (P : SpecificationProblem)
    (S₁ S₂ : SolutionArchitecture P) (n : ℕ) (hn : n ≥ 1)
    (hc : S₁.centralDOF = S₂.centralDOF)
    (hd : S₁.distributedDOF < S₂.distributedDOF) :
    totalDOF S₁ n < totalDOF S₂ n := by
  unfold totalDOF
  have h : n * S₁.distributedDOF < n * S₂.distributedDOF := by
    apply Nat.mul_lt_mul_of_pos_left hd
    omega
  omega

/-- Zero distributed DOF means constant total DOF (independent of n) -/
theorem centralized_constant (S : SolutionArchitecture P) (n₁ n₂ : ℕ)
    (h : S.distributedDOF = 0) :
    totalDOF S n₁ = totalDOF S n₂ := by
  unfold totalDOF
  simp [h]

/-- Zero distributed DOF means minimal error sites (just 1 for central component) -/
theorem centralized_minimal_errors (S : SolutionArchitecture P) (n : ℕ)
    (hc : S.centralDOF > 0) (hd : S.distributedDOF = 0) :
    errorSites S n = 1 := by
  unfold errorSites
  simp [hc, hd]

/-- Positive distributed DOF means error sites grow with n -/
theorem distributed_errors_grow (S : SolutionArchitecture P) (n : ℕ) (hn : n > 0)
    (hd : S.distributedDOF > 0) :
    errorSites S n ≥ n := by
  unfold errorSites
  have h : n * S.distributedDOF ≥ n := Nat.le_mul_of_pos_right n hd
  omega

/-! ## Right vs Wrong Hardness -/

/-- Hardness is in the right place if distributed DOF is zero -/
def isRightHardness (S : SolutionArchitecture P) : Prop :=
  S.distributedDOF = 0

/-- Hardness is in the wrong place if distributed DOF is positive -/
def isWrongHardness (S : SolutionArchitecture P) : Prop :=
  S.distributedDOF > 0

/-- Right hardness dominates wrong hardness for large n -/
theorem right_dominates_wrong (P : SpecificationProblem)
    (S_right S_wrong : SolutionArchitecture P)
    (hr : isRightHardness S_right)
    (hw : isWrongHardness S_wrong)
    (n : ℕ) (hn : n > S_right.centralDOF) :
    totalDOF S_right n < totalDOF S_wrong n := by
  unfold isRightHardness at hr
  unfold isWrongHardness at hw
  unfold totalDOF
  simp [hr]
  -- S_right.centralDOF < n * S_wrong.distributedDOF + S_wrong.centralDOF
  have h1 : n * S_wrong.distributedDOF ≥ n := Nat.le_mul_of_pos_right n hw
  omega

/-! ## Leverage Connection (Paper 3)

From Paper 3: Leverage = capabilities / DOF
Centralization increases leverage by reducing per-site DOF.
-/

/-- Leverage of a solution: capabilities per unit of total DOF -/
def leverageRatio (capabilities : ℕ) (S : SolutionArchitecture P) (n : ℕ) : ℕ × ℕ :=
  (capabilities, totalDOF S n)

/-- Centralized solutions have higher leverage (same capabilities, lower DOF) -/
theorem centralized_higher_leverage (P : SpecificationProblem)
    (S_central S_distrib : SolutionArchitecture P)
    (caps : ℕ) (n : ℕ) (hn : n ≥ 1)
    (hc_eq : S_central.centralDOF = S_distrib.centralDOF + S_distrib.distributedDOF)
    (hd_zero : S_central.distributedDOF = 0)
    (hd_pos : S_distrib.distributedDOF > 0) :
    totalDOF S_central n ≤ totalDOF S_distrib n := by
  unfold totalDOF
  simp [hd_zero]
  have h : n * S_distrib.distributedDOF ≥ S_distrib.distributedDOF := by
    apply Nat.le_mul_of_pos_left
    omega
  omega

/-! ## Type System Instantiation -/

/-- Native type system: all DOF centralized -/
def nativeTypeSystem (P : SpecificationProblem) : SolutionArchitecture P where
  centralDOF := P.intrinsicDOF
  distributedDOF := 0
  conservation := by omega

/-- Manual approach: all DOF distributed -/
def manualApproach (P : SpecificationProblem) : SolutionArchitecture P where
  centralDOF := 0
  distributedDOF := P.intrinsicDOF
  conservation := by omega

/-- Native type system has right hardness -/
theorem native_is_right (P : SpecificationProblem) :
    isRightHardness (nativeTypeSystem P) := by
  unfold isRightHardness nativeTypeSystem
  rfl

/-- Manual approach has wrong hardness (when DOF > 0) -/
theorem manual_is_wrong (P : SpecificationProblem) :
    isWrongHardness (manualApproach P) := by
  unfold isWrongHardness manualApproach
  exact P.dof_pos

/-- For n > intrinsicDOF, native dominates manual -/
theorem native_dominates_manual (P : SpecificationProblem) (n : ℕ)
    (hn : n > P.intrinsicDOF) :
    totalDOF (nativeTypeSystem P) n < totalDOF (manualApproach P) n := by
  apply right_dominates_wrong
  · exact native_is_right P
  · exact manual_is_wrong P
  · unfold nativeTypeSystem; exact hn

/-- Error sites: native has 1, manual has n × intrinsicDOF -/
theorem native_minimal_errors (P : SpecificationProblem) (n : ℕ) :
    errorSites (nativeTypeSystem P) n = 1 := by
  apply centralized_minimal_errors
  · unfold nativeTypeSystem; exact P.dof_pos
  · unfold nativeTypeSystem; rfl

theorem manual_errors_grow (P : SpecificationProblem) (n : ℕ) (hn : n > 0) :
    errorSites (manualApproach P) n ≥ n := by
  apply distributed_errors_grow
  · exact hn
  · exact manual_is_wrong P

/-! ## Simplicity-Tax Named Corollaries (LaTeX Section 8 Handles) -/

/-- Simplicity tax in this model is exactly distributed DOF. -/
def simplicityTax (P : SpecificationProblem) (S : SolutionArchitecture P) : ℕ :=
  S.distributedDOF

/-- Conservation restated with SimplicityTax notation. -/
theorem simplicityTax_conservation (P : SpecificationProblem) (S : SolutionArchitecture P) :
    S.centralDOF + simplicityTax P S ≥ P.intrinsicDOF := by
  simpa [simplicityTax] using dof_conservation P S

/-- Positive simplicity tax implies total work grows with use-site count. -/
theorem simplicityTax_grows (P : SpecificationProblem) (S : SolutionArchitecture P)
    (n₁ n₂ : ℕ) (hn : n₁ < n₂) (htax : simplicityTax P S > 0) :
    totalDOF S n₁ < totalDOF S n₂ := by
  have hd : S.distributedDOF > 0 := by
    simpa [simplicityTax] using htax
  exact distributed_multiplies S n₁ n₂ hn hd

/-- Amortization threshold instantiated by native-vs-manual architecture. -/
theorem amortization_threshold_native_manual (P : SpecificationProblem) (n : ℕ)
    (hn : n > P.intrinsicDOF) :
    totalDOF (nativeTypeSystem P) n < totalDOF (manualApproach P) n := by
  exact native_dominates_manual P n hn

/-! ## Extension: Non-Additive Site-Cost Models -/

/-- A cost function is eventually constant if it stabilizes after some index. -/
def IsEventuallyConstant (f : ℕ → ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, f n = f N

/-- In the linear model, distributedDOF = 0 implies eventual constancy. -/
theorem totalDOF_eventually_constant_of_zero_distributed (S : SolutionArchitecture P)
    (h0 : S.distributedDOF = 0) :
    IsEventuallyConstant (fun n => totalDOF S n) := by
  refine ⟨0, ?_⟩
  intro n _
  simpa using (centralized_constant S n 0 h0)

/-- In the linear model, eventual constancy forces distributedDOF = 0. -/
theorem zero_distributed_of_totalDOF_eventually_constant (S : SolutionArchitecture P)
    (hconst : IsEventuallyConstant (fun n => totalDOF S n)) :
    S.distributedDOF = 0 := by
  by_contra hne
  have hd : S.distributedDOF > 0 := Nat.pos_of_ne_zero hne
  rcases hconst with ⟨N, hN⟩
  have hEq : totalDOF S (N + 1) = totalDOF S N := by
    exact hN (N + 1) (Nat.le_succ N)
  have hLt : totalDOF S N < totalDOF S (N + 1) :=
    distributed_multiplies S N (N + 1) (Nat.lt_succ_self N) hd
  exact (ne_of_lt hLt) hEq.symm

/-- Saturation criterion for the linear model: iff distributedDOF = 0. -/
theorem totalDOF_eventually_constant_iff_zero_distributed (S : SolutionArchitecture P) :
    IsEventuallyConstant (fun n => totalDOF S n) ↔ S.distributedDOF = 0 := by
  constructor
  · exact zero_distributed_of_totalDOF_eventually_constant S
  · exact totalDOF_eventually_constant_of_zero_distributed S

/-- A canonical saturating site-cost function in the generalized model. -/
def saturatingSiteCost (K : ℕ) (n : ℕ) : ℕ :=
  if n ≤ K then n else K

/-- Generalized total cost with arbitrary per-site accumulation. -/
def generalizedTotalDOF (central : ℕ) (siteCost : ℕ → ℕ) (n : ℕ) : ℕ :=
  central + siteCost n

/-- Saturating site cost is eventually constant. -/
theorem saturatingSiteCost_eventually_constant (K : ℕ) :
    IsEventuallyConstant (saturatingSiteCost K) := by
  refine ⟨K, ?_⟩
  intro n hn
  unfold saturatingSiteCost
  by_cases hle : n ≤ K
  · have hEq : n = K := Nat.le_antisymm hle hn
    simp [hle, hEq]
  · simp [hle]

/-- Generalized total with saturating site cost is eventually constant. -/
theorem generalizedTotal_with_saturation_eventually_constant (central K : ℕ) :
    IsEventuallyConstant (fun n => generalizedTotalDOF central (saturatingSiteCost K) n) := by
  refine ⟨K, ?_⟩
  intro n hn
  unfold generalizedTotalDOF saturatingSiteCost
  by_cases hle : n ≤ K
  · have hEq : n = K := Nat.le_antisymm hle hn
    simp [hle, hEq]
  · simp [hle]

/-- Any linear representation of a saturating cost must have zero slope. -/
theorem linear_represents_saturating_only_zero_slope (c d K : ℕ)
    (hrep : ∀ n, c + n * d = generalizedTotalDOF c (saturatingSiteCost K) n) :
    d = 0 := by
  have hK : c + K * d = generalizedTotalDOF c (saturatingSiteCost K) K := hrep K
  have hK1 : c + (K + 1) * d = generalizedTotalDOF c (saturatingSiteCost K) (K + 1) := hrep (K + 1)
  unfold generalizedTotalDOF saturatingSiteCost at hK hK1
  have hEq : c + K * d = c + (K + 1) * d := by
    calc
      c + K * d = c + K := by simpa using hK
      _ = c + (K + 1) * d := by
        have hk : ¬ (K + 1 ≤ K) := Nat.not_succ_le_self K
        simpa [hk] using hK1.symm
  have hEq' : c + K * d = c + K * d + d := by
    simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hEq
  omega

/-- Therefore positive-slope linear models cannot realize saturation for all n. -/
theorem no_positive_slope_linear_represents_saturating (c d K : ℕ)
    (hd : d > 0) :
    ¬ (∀ n, c + n * d = generalizedTotalDOF c (saturatingSiteCost K) n) := by
  intro hrep
  have hzero : d = 0 := linear_represents_saturating_only_zero_slope c d K hrep
  exact (Nat.ne_of_gt hd) hzero

end DecisionQuotient.HardnessDistribution
