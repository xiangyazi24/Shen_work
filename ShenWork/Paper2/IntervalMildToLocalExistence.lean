/-
  ShenWork/Paper2/IntervalMildToLocalExistence.lean

  Bridge from the Picard gradient-form mild solution package to the local
  existence wrappers in `IntervalDomainExistence`.

  The two Duhamel operators are intentionally not identified here:
  * `IntervalGradientDuhamelMap.intervalGradientDuhamelMap` is the full
    gradient-divergence mild map with the chemotactic flux term.
  * `IntervalDomainExistence.intervalDuhamelOperator` is the older
    logistic-only operator used by `localExistence_of_fp_and_regularity`.

  Hence the theorem that calls `localExistence_of_fp_and_regularity` keeps the
  old fixed-point equation as an explicit hypothesis.
-/
import ShenWork.Paper2.IntervalMildToClassical

open scoped Topology

namespace ShenWork.IntervalMildToLocalExistence

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildToClassical
open ShenWork.Paper2

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
  · simpa [v] using mildChemical_ellipticPDE p D hC2 hN0 hN1
  · simpa [v] using mildSolution_neumannBC p D hC2 hN0 hN1
  · simpa [v] using mildSolution_classicalRegularity p D hclassical
  · exact mildSolution_initialTrace p D hInitialApproach

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

end ShenWork.IntervalMildToLocalExistence
