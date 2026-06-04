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
