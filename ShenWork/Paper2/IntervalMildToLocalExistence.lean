/-
  ShenWork/Paper2/IntervalMildToLocalExistence.lean

  Bridge from the Picard gradient-form mild solution package to the local
  existence wrappers in `IntervalDomainExistence`.

  The two Duhamel operators are not definitionally identical:
  * `IntervalGradientDuhamelMap.intervalGradientDuhamelMap` is the full
    gradient-divergence mild map with the chemotactic flux term.
  * `IntervalDomainExistence.intervalDuhamelOperator` is the older
    logistic-only helper operator used by `localExistence_of_fp_and_regularity`.

  The bridge below records the exact frontiers needed to identify them: the
  full Neumann semigroup must be identified with the older helper semigroup,
  the logistic Duhamel integrals must agree, and the chemotaxis contribution
  must vanish (for instance in the zero-sensitivity branch).
-/
import ShenWork.Paper2.IntervalMildToClassical

open scoped Topology

namespace ShenWork.IntervalMildToLocalExistence

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.Paper2

/-- The remaining classical-side core after the restart-cosine bootstrap has
discharged positivity, chemical nonnegativity, the elliptic equation for the
resolver, and the Neumann boundary conditions.

This is intentionally smaller than a full `IsPaper2ClassicalSolution`: the two
fields here are exactly the pieces not supplied by `GradientMildSolutionData`
and the restart-cosine/half-step regularity chain. -/
structure GradientMildClassicalCoreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0) : Prop where
  hpde_u :
    ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)
  hclassicalRegularity :
    intervalDomainClassicalRegularity D.T D.u
      (mildChemicalConcentration p D.u)

/-- Assemble the `RegularityBootstrap` predicate for the Picard gradient mild
solution once the already-proved mild-to-classical side hypotheses are supplied.

The closed-interval spatial `C²` and one-sided Neumann inputs needed by
`mildChemical_ellipticPDE` and `mildSolution_neumannBC` are read from the
`intervalDomainClassicalRegularity` field of `hclassical`. -/
theorem regularityBootstrap_of_gradientMildSolutionData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    RegularityBootstrap p D.T u0 D.u := by
  let v : ℝ → intervalDomainPoint → ℝ := mildChemicalConcentration p D.u
  have hC2 : ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1) := by
    intro t ht0 htT
    exact (hclassical.regularity.2.2.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hN0 : ∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro t ht0 htT
    exact (hclassical.regularity.2.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hN1 : ∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
    intro t ht0 htT
    exact (hclassical.regularity.2.2.2.2.2.1 t ⟨ht0, htT⟩).1.2
  refine ⟨v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT
    exact mildSolution_strictlyPositive p D ht0 (le_of_lt htT) x
  · intro t x ht0 htT
    exact mildChemical_nonneg p D.hnonneg D.hcont ht0 (le_of_lt htT) x
  · simpa [v] using mildSolution_parabolicPDE p D hclassical
  · simpa [v] using mildChemical_ellipticPDE_of_closedC2_neumann p D hC2 hN0 hN1
  · simpa [v] using mildSolution_neumannBC_of_closedC2_neumann p D hC2 hN0 hN1
  · simpa [v] using mildSolution_classicalRegularity p D hclassical
  · exact mildSolution_initialTrace p D hInitialApproach

/-- Assemble `RegularityBootstrap` using restart-cosine regularity for the
elliptic PDE and Neumann boundary conditions.  This removes the direct
`ContDiffOn`/one-sided-Neumann extraction previously needed for those two
conjuncts. -/
theorem regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    RegularityBootstrap p D.T u0 D.u := by
  let v : ℝ → intervalDomainPoint → ℝ := mildChemicalConcentration p D.u
  refine ⟨v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x ht0 htT
    exact mildSolution_strictlyPositive p D ht0 (le_of_lt htT) x
  · intro t x ht0 htT
    exact mildChemical_nonneg p D.hnonneg D.hcont ht0 (le_of_lt htT) x
  · simpa [v] using mildSolution_parabolicPDE p D hclassical
  · simpa [v] using
      mildChemical_ellipticPDE_of_restartCosineRepresentations p D H
  · simpa [v] using
      mildSolution_neumannBC_of_restartCosineRepresentations p D H
  · simpa [v] using mildSolution_classicalRegularity p D hclassical
  · exact mildSolution_initialTrace p D hInitialApproach

/-- Assemble `RegularityBootstrap` from the half-step source regularity and
series-agreement package, first turning it into restart-cosine representations. -/
theorem regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    RegularityBootstrap p D.T u0 D.u :=
  regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations
    p D (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R)
    hInitialApproach hclassical

/-- Build the full classical-solution package from Picard gradient mild data and
the remaining classical core.

The core supplies the parabolic equation for `u` and the full classical
regularity bundle.  Positivity and chemical nonnegativity come from the mild
solution data; the elliptic resolver equation and Neumann boundary conditions
are recovered from the regularity bundle via the closed-`C²`/one-sided-Neumann
resolver bridge. -/
theorem isPaper2ClassicalSolution_of_gradientMildSolutionData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (C : GradientMildClassicalCoreData p D) :
    IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u) := by
  let v : ℝ → intervalDomainPoint → ℝ := mildChemicalConcentration p D.u
  have hC2 : ∀ t, 0 < t → t < D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1) := by
    intro t ht0 htT
    exact (C.hclassicalRegularity.2.2.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hN0 : ∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    intro t ht0 htT
    exact (C.hclassicalRegularity.2.2.2.2.2.1 t ⟨ht0, htT⟩).1.1
  have hN1 : ∀ t, 0 < t → t < D.T →
      Filter.Tendsto (deriv (intervalDomainLift (D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
    intro t ht0 htT
    exact (C.hclassicalRegularity.2.2.2.2.2.1 t ⟨ht0, htT⟩).1.2
  refine IsPaper2ClassicalSolution.of_components
    (D := intervalDomain) (p := p) (T := D.T)
    (u := D.u) (v := v)
    D.hT ?hreg ?hpos ?hv_nonneg ?hpde_u ?hpde_v ?hneumann
  · simpa [v] using C.hclassicalRegularity
  · intro t x ht0 htT
    exact mildSolution_strictlyPositive p D ht0 (le_of_lt htT) x
  · intro t x ht0 htT
    exact mildChemical_nonneg p D.hnonneg D.hcont ht0 (le_of_lt htT) x
  · simpa [v] using C.hpde_u
  · simpa [v] using mildChemical_ellipticPDE_of_closedC2_neumann p D hC2 hN0 hN1
  · simpa [v] using mildSolution_neumannBC_of_closedC2_neumann p D hC2 hN0 hN1

/-- `RegularityBootstrap` using only the remaining classical core instead of a
full classical-solution hypothesis. -/
theorem regularityBootstrap_of_gradientMildSolutionData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    RegularityBootstrap p D.T u0 D.u :=
  regularityBootstrap_of_gradientMildSolutionData p D hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_and_coreData p D C)

/-- Build the full classical-solution package from Picard gradient mild data,
restart-cosine regularity, and the remaining parabolic/core-regularity fields.

The positivity, chemical nonnegativity, elliptic resolver equation, and Neumann
boundary conditions are all supplied by the already-proved mild/restart chain. -/
theorem isPaper2ClassicalSolution_of_gradientMildSolutionData_of_restartCosineRepresentations
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (C : GradientMildClassicalCoreData p D) :
    IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u) := by
  refine IsPaper2ClassicalSolution.of_components
    (D := intervalDomain) (p := p) (T := D.T)
    (u := D.u) (v := mildChemicalConcentration p D.u)
    D.hT C.hclassicalRegularity ?hpos ?hv_nonneg ?hpde_u ?hpde_v ?hneumann
  · intro t x ht0 htT
    exact mildSolution_strictlyPositive p D ht0 (le_of_lt htT) x
  · intro t x ht0 htT
    exact mildChemical_nonneg p D.hnonneg D.hcont ht0 (le_of_lt htT) x
  · exact C.hpde_u
  · exact mildChemical_ellipticPDE_of_restartCosineRepresentations p D H
  · exact mildSolution_neumannBC_of_restartCosineRepresentations p D H

/-- Build the full classical-solution package from the half-step restart data,
which first produces restart-cosine representations. -/
theorem isPaper2ClassicalSolution_of_gradientMildSolutionData_of_halfStepRestartData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (C : GradientMildClassicalCoreData p D) :
    IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u) :=
  isPaper2ClassicalSolution_of_gradientMildSolutionData_of_restartCosineRepresentations
    p D (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R) C

/-- Restart-cosine `RegularityBootstrap` using only the remaining classical core
instead of a full classical-solution hypothesis. -/
theorem regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    RegularityBootstrap p D.T u0 D.u :=
  regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations
    p D H hInitialApproach
      (isPaper2ClassicalSolution_of_gradientMildSolutionData_of_restartCosineRepresentations
        p D H C)

/-- Half-step restart `RegularityBootstrap` using only the remaining classical
core instead of a full classical-solution hypothesis. -/
theorem regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    RegularityBootstrap p D.T u0 D.u :=
  regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData
    p D R hInitialApproach
      (isPaper2ClassicalSolution_of_gradientMildSolutionData_of_halfStepRestartData
        p D R C)

/-- Direct local existence from the Picard gradient mild solution package after
assembling `RegularityBootstrap`.  This avoids the older logistic-only Duhamel
fixed-point theorem. -/
theorem localExistence_of_gradientMildSolutionData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData p D hInitialApproach hclassical
  exact localExistence_of_regularityBootstrap p u0 hu0 D.hT hreg

/-- Direct local existence from the Picard gradient mild solution package, with
elliptic/Neumann regularity discharged by restart-cosine representations. -/
theorem localExistence_of_gradientMildSolutionData_of_restartCosineRepresentations
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations
      p D H hInitialApproach hclassical
  exact localExistence_of_regularityBootstrap p u0 hu0 D.hT hreg

/-- Direct local existence from Picard gradient mild data, with restart-cosine
regularity produced from the half-step source and series package. -/
theorem localExistence_of_gradientMildSolutionData_of_halfStepRestartData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData
      p D R hInitialApproach hclassical
  exact localExistence_of_regularityBootstrap p u0 hu0 D.hT hreg

/-- Direct local existence from Picard gradient mild data using only the
remaining classical core. -/
theorem localExistence_of_gradientMildSolutionData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData_and_coreData
      p D hInitialApproach C
  exact localExistence_of_regularityBootstrap p u0 hu0 D.hT hreg

/-- Direct local existence from restart-cosine Picard gradient mild data using
only the remaining classical core. -/
theorem localExistence_of_gradientMildSolutionData_of_restartCosineRepresentations_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hclassical :
      IsPaper2ClassicalSolution intervalDomain p D.T D.u
        (mildChemicalConcentration p D.u) :=
    isPaper2ClassicalSolution_of_gradientMildSolutionData_of_restartCosineRepresentations
      p D H C
  exact localExistence_of_gradientMildSolutionData_of_restartCosineRepresentations
    p hu0 D H hInitialApproach hclassical

/-- Direct local existence from half-step restart Picard gradient mild data using
only the remaining classical core. -/
theorem localExistence_of_gradientMildSolutionData_of_halfStepRestartData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_of_restartCosineRepresentations_and_coreData
    p hu0 D (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R)
    hInitialApproach C

/-- Exact componentwise bridge between the gradient-form mild map and the older
`intervalDuhamelOperator`.

This theorem does not hide the mathematical mismatch: the older operator has no
chemotaxis term and uses the older helper semigroup.  Equality follows exactly
when the initial semigroup terms agree, the chemotaxis Duhamel contribution
vanishes, and the logistic Duhamel terms agree. -/
theorem intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_frontiers
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint)
    (hinit :
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hchem :
      (-p.χ₀) *
          (∫ s in (0 : ℝ)..t,
            deriv
              (fun z =>
                intervalFullSemigroupOperator (t - s)
                  (chemFluxLifted p (u s)) z) x.1) =
        0)
    (hlog :
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (u s)) x.1) :
    intervalGradientDuhamelMap p u0 u t x =
      intervalDuhamelOperator p u0 u t x := by
  unfold intervalGradientDuhamelMap intervalDuhamelOperator
  rw [hinit, hchem, hlog]
  simp only [logisticLifted]
  ring

/-- The chemotaxis Duhamel contribution in `intervalGradientDuhamelMap`
vanishes in the zero-sensitivity branch. -/
theorem intervalGradientDuhamelMap_chemTerm_zero_of_chi_zero
    (p : CM2Params) (hχ : p.χ₀ = 0)
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) :
    (-p.χ₀) *
        (∫ s in (0 : ℝ)..t,
          deriv
            (fun z =>
              intervalFullSemigroupOperator (t - s)
                (chemFluxLifted p (u s)) z) x.1) =
      0 := by
  simp [hχ]

/-- Zero-sensitivity RHS bridge: after the full/helper semigroup and logistic
Duhamel terms are identified, the gradient-form map equals the older
`intervalDuhamelOperator`. -/
theorem intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_chi_zero
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint)
    (hχ : p.χ₀ = 0)
    (hinit :
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog :
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (u s)) x.1) :
    intervalGradientDuhamelMap p u0 u t x =
      intervalDuhamelOperator p u0 u t x :=
  intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_frontiers
    p u t x hinit
    (intervalGradientDuhamelMap_chemTerm_zero_of_chi_zero p hχ u t x)
    hlog

/-- Positive-time fixed-point bridge.  Once the gradient-divergence Duhamel RHS
is identified with the older `intervalDuhamelOperator` RHS, the Picard mild
equation gives the older fixed-point equation on `(0, T]`. -/
theorem intervalDuhamel_fixedPoint_pos_of_gradientMildSolutionData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (hDuhamelEq : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u0 D.u t x =
        intervalDuhamelOperator p u0 D.u t x) :
    ∀ t x, 0 < t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x := by
  intro t x ht0 htT
  rw [D.hmild t ht0 htT x]
  exact hDuhamelEq t ht0 htT x

/-- Positive-time old fixed-point equation in the zero-sensitivity branch from
the componentwise Duhamel frontiers. -/
theorem intervalDuhamel_fixedPoint_pos_of_gradientMildSolutionData_chi_zero
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (hχ : p.χ₀ = 0)
    (hinit : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (D.u s)) x.1) :
    ∀ t x, 0 < t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x := by
  refine intervalDuhamel_fixedPoint_pos_of_gradientMildSolutionData p D ?_
  intro t ht0 htT x
  exact intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_chi_zero
    p D.u t x hχ (hinit t ht0 htT x) (hlog t ht0 htT x)

/-- Closed-time fixed-point bridge for `localExistence_of_fp_and_regularity`.

`GradientMildSolutionData.hmild` is only a positive-time equation, while the old
local-existence wrapper asks for `0 ≤ t ≤ T`.  Thus the endpoint `t = 0` is kept
as a separate exact-value hypothesis. -/
theorem intervalDuhamel_fixedPoint_of_gradientMildSolutionData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hDuhamelEq : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u0 D.u t x =
        intervalDuhamelOperator p u0 D.u t x) :
    ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x := by
  intro t x ht0 htT
  by_cases htpos : 0 < t
  · exact intervalDuhamel_fixedPoint_pos_of_gradientMildSolutionData
      p D hDuhamelEq t x htpos htT
  · have ht_le_zero : t ≤ 0 := le_of_not_gt htpos
    have ht_eq : t = 0 := le_antisymm ht_le_zero ht0
    subst t
    exact hzero x

/-- Closed-time old fixed-point equation in the zero-sensitivity branch from
the componentwise Duhamel frontiers and the separate `t = 0` endpoint value. -/
theorem intervalDuhamel_fixedPoint_of_gradientMildSolutionData_chi_zero
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (hχ : p.χ₀ = 0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hinit : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (D.u s)) x.1) :
    ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x :=
  intervalDuhamel_fixedPoint_of_gradientMildSolutionData p D hzero
    (fun t ht0 htT x =>
      intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_chi_zero
        p D.u t x hχ (hinit t ht0 htT x) (hlog t ht0 htT x))

/-- Route through `localExistence_of_fp_and_regularity` after supplying the
operator-equivalence bridge and the exact `t = 0` fixed-point value required by
that older wrapper. -/
theorem localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hDuhamelEq : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u0 D.u t x =
        intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x :=
    intervalDuhamel_fixedPoint_of_gradientMildSolutionData
      p D hzero hDuhamelEq
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData p D hInitialApproach hclassical
  exact localExistence_of_fp_and_regularity p u0 hu0 D.hT hfp hreg

/-- Route through `localExistence_of_fp_and_regularity`, using restart-cosine
representations to discharge the elliptic and Neumann regularity conjuncts. -/
theorem
    localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_restartCosineRepresentations
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hDuhamelEq : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u0 D.u t x =
        intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x :=
    intervalDuhamel_fixedPoint_of_gradientMildSolutionData
      p D hzero hDuhamelEq
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations
      p D H hInitialApproach hclassical
  exact localExistence_of_fp_and_regularity p u0 hu0 D.hT hfp hreg

/-- Route through `localExistence_of_fp_and_regularity`, with restart-cosine
regularity produced from the half-step source and series package. -/
theorem localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_halfStepRestartData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hDuhamelEq : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u0 D.u t x =
        intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_restartCosineRepresentations
    p hu0 D (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R)
    hzero hDuhamelEq hInitialApproach hclassical

/-- Route through `localExistence_of_fp_and_regularity` in the zero-sensitivity
branch, constructing the old fixed-point hypothesis directly from
`GradientMildSolutionData` and the componentwise Duhamel frontiers. -/
theorem localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (hχ : p.χ₀ = 0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hinit : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (D.u s)) x.1)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x :=
    intervalDuhamel_fixedPoint_of_gradientMildSolutionData_chi_zero
      p D hχ hzero hinit hlog
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData p D hInitialApproach hclassical
  exact localExistence_of_fp_and_regularity p u0 hu0 D.hT hfp hreg

/-- Zero-sensitivity route through `localExistence_of_fp_and_regularity`, with
elliptic/Neumann regularity discharged by restart-cosine representations. -/
theorem
    localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_restartCosineRepresentations
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hχ : p.χ₀ = 0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hinit : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (D.u s)) x.1)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x :=
    intervalDuhamel_fixedPoint_of_gradientMildSolutionData_chi_zero
      p D hχ hzero hinit hlog
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations
      p D H hInitialApproach hclassical
  exact localExistence_of_fp_and_regularity p u0 hu0 D.hT hfp hreg

/-- Zero-sensitivity route through `localExistence_of_fp_and_regularity`, with
restart-cosine regularity produced from the half-step source and series package. -/
theorem localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_halfStepRestartData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hχ : p.χ₀ = 0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hinit : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (D.u s)) x.1)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_restartCosineRepresentations
    p hu0 D (hasRestartCosineRepresentations_of_gradientMildHalfStepRestartData D R)
    hχ hzero hinit hlog hInitialApproach hclassical

/-- Version that explicitly routes through
`IntervalDomainExistence.localExistence_of_fp_and_regularity`.

The extra `hfp` hypothesis is deliberately the fixed-point equation for the old
`intervalDuhamelOperator`; it is not supplied by `GradientMildSolutionData.hmild`,
whose equation is for `intervalGradientDuhamelMap`. -/
theorem localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData p D hInitialApproach hclassical
  exact localExistence_of_fp_and_regularity p u0 hu0 D.hT hfp hreg

/-- Old-fixed-point route through `localExistence_of_fp_and_regularity`, using
restart-cosine representations for the elliptic and Neumann conjuncts. -/
theorem localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp_of_restartCosineRepresentations
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations
      p D H hInitialApproach hclassical
  exact localExistence_of_fp_and_regularity p u0 hu0 D.hT hfp hreg

/-- Old-fixed-point route through `localExistence_of_fp_and_regularity`, with
restart-cosine regularity produced from the half-step source and series package. -/
theorem localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp_of_halfStepRestartData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u)) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u := by
  have hreg : RegularityBootstrap p D.T u0 D.u :=
    regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData
      p D R hInitialApproach hclassical
  exact localExistence_of_fp_and_regularity p u0 hu0 D.hT hfp hreg

/-- Old-Duhamel routed local existence using only the remaining classical core. -/
theorem localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hDuhamelEq : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u0 D.u t x =
        intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq
    p hu0 D hzero hDuhamelEq hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_and_coreData p D C)

/-- Old-Duhamel routed local existence with restart-cosine data and only the
remaining classical core. -/
theorem
    localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_restartCosineRepresentations_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hDuhamelEq : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u0 D.u t x =
        intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_restartCosineRepresentations
    p hu0 D H hzero hDuhamelEq hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_of_restartCosineRepresentations
      p D H C)

/-- Old-Duhamel routed local existence with half-step restart data and only the
remaining classical core. -/
theorem
    localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_halfStepRestartData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hDuhamelEq : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalGradientDuhamelMap p u0 D.u t x =
        intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_halfStepRestartData
    p hu0 D R hzero hDuhamelEq hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_of_halfStepRestartData
      p D R C)

/-- Zero-sensitivity old-Duhamel route using only the remaining classical core. -/
theorem localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (hχ : p.χ₀ = 0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hinit : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (D.u s)) x.1)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel
    p hu0 D hχ hzero hinit hlog hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_and_coreData p D C)

/-- Zero-sensitivity old-Duhamel route with restart-cosine data and only the
remaining classical core. -/
theorem
    localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_restartCosineRepresentations_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hχ : p.χ₀ = 0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hinit : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (D.u s)) x.1)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_restartCosineRepresentations
    p hu0 D H hχ hzero hinit hlog hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_of_restartCosineRepresentations
      p D H C)

/-- Zero-sensitivity old-Duhamel route with half-step restart data and only the
remaining classical core. -/
theorem
    localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_halfStepRestartData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hχ : p.χ₀ = 0)
    (hzero : ∀ x : intervalDomainPoint,
      D.u 0 x = intervalDuhamelOperator p u0 D.u 0 x)
    (hinit : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      intervalFullSemigroupOperator t (intervalDomainLift u0) x.1 =
        intervalSemigroupOperator 1 t (intervalDomainLift u0) x.1)
    (hlog : ∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) =
        ∫ s in Set.Icc 0 t,
          intervalSemigroupOperator 1 (t - s)
            (logisticLifted p (D.u s)) x.1)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_halfStepRestartData
    p hu0 D R hχ hzero hinit hlog hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_of_halfStepRestartData
      p D R C)

/-- Old-fixed-point route using only the remaining classical core. -/
theorem localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp
    p hu0 D hfp hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_and_coreData p D C)

/-- Old-fixed-point route with restart-cosine data and only the remaining
classical core. -/
theorem
    localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp_of_restartCosineRepresentations_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp_of_restartCosineRepresentations
    p hu0 D H hfp hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_of_restartCosineRepresentations
      p D H C)

/-- Old-fixed-point route with half-step restart data and only the remaining
classical core. -/
theorem
    localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp_of_halfStepRestartData_and_coreData
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    (hfp : ∀ t x, 0 ≤ t → t ≤ D.T →
      D.u t x = intervalDuhamelOperator p u0 D.u t x)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u0 D.u t x - u0 x| < ε)
    (C : GradientMildClassicalCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_and_intervalDuhamel_fp_of_halfStepRestartData
    p hu0 D R hfp hInitialApproach
    (isPaper2ClassicalSolution_of_gradientMildSolutionData_of_halfStepRestartData
      p D R C)

end ShenWork.IntervalMildToLocalExistence
