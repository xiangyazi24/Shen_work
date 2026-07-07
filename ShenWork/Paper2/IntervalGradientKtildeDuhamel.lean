/-
  True integrated gradient-kernel identity for the gradient mild map.

  After the `hgradB` obstruction, the honest identity for the gradient Duhamel
  leg is the open/Ktilde source IBP formula.  This file integrates that
  per-slice identity in time from the regularity-only source bridge stack.
-/
import ShenWork.Paper2.IntervalGradientSourceBridgeRegularityRepresentative
import ShenWork.Paper2.IntervalGradientSourceIBPOpen

open MeasureTheory intervalIntegral Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalMildToLocalExistence

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainClassicalRegularity intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalNeumannFullKernel
  (deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral_open
   intervalFullSemigroupOperator intervalNeumannConjugateKernel)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift)
open ShenWork.Paper2.IntervalGradientSourceBridgeOpen

/-- The true endpoint-safe integrated gradient-kernel identity for a gradient
mild solution with regularity.  The gradient Neumann Duhamel leg is identified
with the `Ktilde` source-derivative integral, not with the B-kernel operator
`intervalConjugateKernelOperator`. -/
theorem gradientDuhamel_deriv_integral_eq_ktilde_source_integral_of_gradientMildRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hreg : intervalDomainClassicalRegularity D.T D.u
      (coupledChemicalConcentration p D.u))
    {t x : ℝ} (ht0 : 0 < t) (htT : t < D.T) :
    (∫ s in (0 : ℝ)..t,
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (D.u s)) z) x)
      =
    ∫ s in (0 : ℝ)..t,
      -(∫ y in (0 : ℝ)..1,
          coupledChemDivSourceLift p D.u s y *
            intervalNeumannConjugateKernel (t - s) x y) := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le ht0.le]
  filter_upwards
    [(MeasureTheory.Ioo_ae_eq_Ioc
      (a := (0 : ℝ)) (b := t) (μ := volume)).symm] with s hs_ae hsIoc
  have hsIoo_t : s ∈ Set.Ioo (0 : ℝ) t := hs_ae.mp hsIoc
  have hsT : s ∈ Set.Ioo (0 : ℝ) D.T :=
    ⟨hsIoo_t.1, lt_trans hsIoo_t.2 htT⟩
  have hr : 0 < t - s := sub_pos.mpr hsIoo_t.2
  have hchem_cont_global :
      Continuous (chemFluxLifted p (D.u s)) :=
    ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_continuous_of_continuous
      p (D.hcont s hsT.1 hsT.2.le) (D.hnonneg s hsT.1 hsT.2.le)
  have hchem_meas :
      AEStronglyMeasurable (chemFluxLifted p (D.u s)) (intervalMeasure 1) :=
    hchem_cont_global.aestronglyMeasurable
  have hchem_cont :
      ContinuousOn (chemFluxLifted p (D.u s)) (Set.Icc (0 : ℝ) 1) :=
    hchem_cont_global.continuousOn
  obtain ⟨Cchem, _hCchem_nonneg, hchem_bound⟩ :=
    ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_bounded_of_continuous
      p (D.hbound s hsT.1 hsT.2.le) D.hM.le
      (D.hcont s hsT.1 hsT.2.le) (D.hnonneg s hsT.1 hsT.2.le)
  have hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (chemFluxLifted p (D.u s))
        (coupledChemDivSourceLift p D.u s y) (Set.Ioi y) y :=
    chemFluxLifted_hasDerivWithinAt_coupledChemDivSourceLift_open_of_mildRegularity
      D hreg hsT
  obtain ⟨Gdiv, hGcont, hGeq⟩ :=
    coupledChemDivSourceLift_continuousRepresentative_of_mildRegularity
      (p := p) D hreg hsT
  have hQ'int :
      IntervalIntegrable (coupledChemDivSourceLift p D.u s) volume (0 : ℝ) 1 :=
    intervalIntegrable_of_Ioo_eq_continuousOn hGcont hGeq
  exact
    deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral_open
      hr hchem_meas hchem_bound hchem_cont hQderiv hQ'int x

#print axioms gradientDuhamel_deriv_integral_eq_ktilde_source_integral_of_gradientMildRegularity

end ShenWork.IntervalMildToLocalExistence
