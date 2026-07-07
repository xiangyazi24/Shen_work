import ShenWork.Paper2.IntervalGradientSourceBridgeIntegrated
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.ChemMildHolderBootstrap

open MeasureTheory intervalIntegral
open scoped Topology

noncomputable section

namespace ShenWork.IntervalMildToLocalExistence

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.Paper2 (IsPaper2ClassicalSolution)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceLift coupledLogisticSourceCoeffs)
open ShenWork.Paper2.IntervalGradientSourceBridgeOpen

/-- Uniform chemotaxis-flux bound constant supplied by a spatial order box. -/
def gradientBridgeChemFluxBound (p : CM2Params) (M : ℝ) : ℝ :=
  M * (Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * M ^ p.γ)))

/-- Uniform logistic-source bound constant supplied by a spatial order box. -/
def gradientBridgeLogisticBound (p : CM2Params) (M : ℝ) : ℝ :=
  M * (p.a + p.b * M ^ p.α)

theorem gradientBridgeChemFluxBound_nonneg
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ gradientBridgeChemFluxBound p M := by
  unfold gradientBridgeChemFluxBound
  exact mul_nonneg hM
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))))

theorem gradientBridgeLogisticBound_nonneg
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ gradientBridgeLogisticBound p M := by
  unfold gradientBridgeLogisticBound
  exact mul_nonneg hM
    (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM _)))

/-- `GradientMildSolutionData` supplies the windowed chemotaxis-flux source
bound needed by the integrated gradient-source bridge. -/
theorem gradientBridge_chemFlux_windowBound_of_gradientMildSolutionData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |chemFluxLifted p (D.u s) y| ≤ gradientBridgeChemFluxBound p D.M := by
  intro s hs hsT y
  exact ShenWork.IntervalConjugateChemFluxIntegrable.chemFluxLifted_sup_bound_of_ball
    p D.hM.le (D.hbound s hs hsT) (D.hnonneg s hs hsT) (D.hcont s hs hsT) y

/-- `GradientMildSolutionData` supplies the windowed logistic source bound
needed by the integrated gradient-source bridge. -/
theorem gradientBridge_logistic_windowBound_of_gradientMildSolutionData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |logisticLifted p (D.u s) y| ≤ gradientBridgeLogisticBound p D.M := by
  intro s hs hsT y
  exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
    p D.hM (D.hbound s hs hsT) y

/-- Source-side certificate version of the integrated classical gradient-source
bridge for a packaged mild solution.

The Duhamel integrability inputs are produced from the actual
`GradientMildSolutionData` measurability, continuity, nonnegativity, and order
box fields; the remaining substantive input is the classical solution
identification used by the per-slice bridge. -/
theorem gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_gradientMildSolutionData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) {t x : ℝ}
    (ht0 : 0 < t) (htT : t < D.T) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hclassical : IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (coupledChemicalConcentration p D.u)) :
    gradientMildChemotaxisDuhamelTerm p D.u t x
      + gradientMildLogisticDuhamelTerm p D.u t x
      =
    ∫ s in (0 : ℝ)..t,
      ((-p.χ₀) *
          unitIntervalSineHeatValue (t - s)
            (sineCoeffs (coupledChemDivSourceLift p D.u s)) x
        + unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p D.u s) x) := by
  have hchem_meas :
      Measurable (Function.uncurry (fun s y => chemFluxLifted p (D.u s) y)) :=
    ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := D.u) D.hmeas
  have hlog_meas :
      Measurable (Function.uncurry (fun s y => logisticLifted p (D.u s) y)) :=
    ShenWork.Paper2.logisticLifted_uncurry_measurable (p := p) (u := D.u) D.hmeas
  exact
    gradientMildDuhamelTerms_eq_integral_mixedSpectralSource_of_windowBounds
      (p := p) (T := D.T) (u := D.u) (t := t) (x := x)
      ht0 htT hx hclassical
      hchem_meas (gradientBridgeChemFluxBound_nonneg p D.hM.le)
      (fun s hs hst y =>
        gradientBridge_chemFlux_windowBound_of_gradientMildSolutionData D
          s hs (le_trans hst htT.le) y)
      hlog_meas (gradientBridgeLogisticBound_nonneg p D.hM.le)
      (fun s hs hst y =>
        gradientBridge_logistic_windowBound_of_gradientMildSolutionData D
          s hs (le_trans hst htT.le) y)

end ShenWork.IntervalMildToLocalExistence
