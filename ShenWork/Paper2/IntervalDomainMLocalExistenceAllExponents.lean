/-
  Unconditional local classical existence for the faithful general-m domain
  and every positive exponent admitted by CM2Params.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildClassicalRegularityFromJointUT
import ShenWork.Paper2.IntervalDomainMConjugateMildInitialTrace
import ShenWork.Paper2.IntervalDuhamelIntegrability

open MeasureTheory Set

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainM intervalMeasure)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM conjugateMildSolutionDataM_exists_paperPositive
    positiveFloorPicardDataM_exists_uniform conjugateMildSolutionDataM_of_picardData)

/-- The datum bound stored by the faithful positive-strip fixed point extends
to its zero extension on the real line. -/
theorem ConjugateMildSolutionDataM.lift_datum_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ y, |intervalDomainLift u₀ y| ≤ D.M := by
  intro y
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · simpa [intervalDomainLift, hy] using D.datum_bound ⟨y, hy⟩
  · simp [intervalDomainLift, hy, D.hM.le]

/-- Every faithful general-m mild datum produces its concrete classical
solution and initial trace. -/
theorem intervalDomainM_classicalSolution_of_mildData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (D : ConjugateMildSolutionDataM p u₀) :
    IsPaper2ClassicalSolution intervalDomainM p D.T D.u
        (ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration p D.u) ∧
      InitialTrace intervalDomainM u₀ D.u := by
  have hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀_cont
  exact ⟨conjugateMildM_isPaper2ClassicalSolution
      D hu₀_cont
        (ShenWork.Paper2.ConjugateMildSolutionDataM.lift_datum_bound D) hu₀_meas,
    conjugateMildSolutionDataM_initialTrace p hu₀_cont D⟩

/-- Faithful local classical existence on `intervalDomainM` for arbitrary
paper-positive data and all positive exponents. -/
theorem intervalDomainM_localExistence_paperPositive_allExponents
    (p : CM2Params) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomainM u₀ →
        ∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomainM p T u v ∧
          InitialTrace intervalDomainM u₀ u := by
  intro u₀ hu₀
  let D := (conjugateMildSolutionDataM_exists_paperPositive p hu₀).some
  have H := intervalDomainM_classicalSolution_of_mildData p hu₀.admissible.2 D
  exact ⟨D.T, D.hT, D.u,
    ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration p D.u,
    H⟩

/-- The same local construction has a lifespan depending only on a prescribed
positive strip.  This is the form needed by continuation. -/
theorem intervalDomainM_thresholdLocalExistence_positiveStrip_allExponents
    (p : CM2Params) :
    ∀ M c : ℝ, 0 < M → 0 < c → ∃ δ : ℝ, 0 < δ ∧
      ∀ w : intervalDomainPoint → ℝ,
        Continuous w →
        (∀ x, |w x| ≤ M) →
        (∀ x, c ≤ w x) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomainM p δ u v ∧
          InitialTrace intervalDomainM w u := by
  intro M c hM hc
  obtain ⟨δ, hδ, hfactory⟩ :=
    positiveFloorPicardDataM_exists_uniform p M c hc
  refine ⟨δ, hδ, ?_⟩
  intro w hw hbound hfloor
  obtain ⟨P, hPT⟩ := hfactory w hw hbound hfloor
  let D := conjugateMildSolutionDataM_of_picardData hw P
  have H := intervalDomainM_classicalSolution_of_mildData p hw D
  have hDT : D.T = δ := by
    change P.T = δ
    exact hPT
  subst δ
  exact ⟨D.u,
    ShenWork.IntervalCoupledRegularityBootstrap.coupledChemicalConcentration p D.u,
    H⟩

section AxiomAudit

#print axioms ConjugateMildSolutionDataM.lift_datum_bound
#print axioms intervalDomainM_classicalSolution_of_mildData
#print axioms intervalDomainM_localExistence_paperPositive_allExponents
#print axioms intervalDomainM_thresholdLocalExistence_positiveStrip_allExponents

end AxiomAudit

end ShenWork.Paper2
