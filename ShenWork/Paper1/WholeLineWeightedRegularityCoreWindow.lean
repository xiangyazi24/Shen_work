import ShenWork.Paper1.WholeLineWeightedRegularityHalfEnergyWindow
import ShenWork.Paper1.WholeLineWeightedRegularitySecondDerivGenerator

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# The three weighted-energy core inputs from one generator window

Once the actual exact-weight state has its generator-plus-forcing right
derivative throughout a positive-time window, the same datum supplies both
ordinary differentiation of the quadratic half energy and the weighted
second-derivative pairing.  This file exposes exactly the three inputs used
by `paper5WeightedEnergy_deriv_le_common_of_coreIntegrability`.
-/

/-- A local exact-generator trajectory supplies `hhalf`, `W * Wxx`
integrability, and `Wx²` integrability at the target time. -/
theorem paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow
    (p : CMParams) {T eta c L R t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {X A F : ℝ → WholeLineRealL2}
    (hL0 : 0 < L) (hLt : L < t) (htR : t < R) (hRT : R < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hphi_meas : ∀ q, 0 < q → AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U q) volume)
    (hphi_sq : ∀ q, 0 < q → Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume)
    (hZcont : ContinuousOn (fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta (coMovingPath c u) U q))
      (Set.Ioo L R))
    (hXcont : ContinuousOn X (Set.Ioo L R))
    (hFcont : ContinuousOn F (Set.Ioo L R))
    (hu : ∀ q ∈ Set.Ioo L R, ∀ x, 0 ≤ coMovingPath c u q x)
    (hu2 : ∀ q ∈ Set.Ioo L R,
      ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Ioo L R,
      ContDiff ℝ 2 (coMovingPath c v q))
    (hclose : ∀ q ∈ Set.Ioo L R, Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2))
    (hWx2 : ∀ q ∈ Set.Ioo L R, Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hXrep : ∀ q ∈ Set.Ioo L R,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hFrep : ∀ q ∈ Set.Ioo L R,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q))
    (hZright : ∀ q ∈ Set.Ioo L R,
      HasDerivWithinAt (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
        (A q + F q) (Set.Ici q) q)
    (hpoint : ∀ q ∈ Set.Ioo L R, ∀ x,
      HasDerivAt
        (fun s => paper5WeightedPopulation eta (coMovingPath c u) U s x)
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) q x) q) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
        (∫ x : ℝ,
          paper5WeightedPopulation eta (coMovingPath c u) U t x *
            paper5WeightedPopulationT eta
              (paper5CoMovingMaterialTime c u) t x) t ∧
      Integrable (fun x =>
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) ∧
      Integrable (fun x =>
        paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2) := by
  have htmem : t ∈ Set.Ioo L R := ⟨hLt, htR⟩
  have hhalf :=
    paper5WeightedHalfEnergy_hasDerivAt_of_exactGeneratorWindow
      p hL0 hLt htR hRT hsol hTW hU2 hV2 hphi_meas hphi_sq
        hZcont hXcont hFcont hu hu2 hv2 hclose hWx2 hXrep hFrep
        hZright hpoint
  have hdiff :=
    paper5WeightedPopulation_diffusion_data_of_fullGenerator_rightDerivative
      p hsol (hL0.trans hLt) (htR.trans hRT) hTW (hu t htmem)
        (hu2 t htmem) (hv2 t htmem) hU2 hV2 (hclose t htmem)
        (hWx2 t htmem)
        (fun n => hphi_meas _ (add_pos (hL0.trans hLt) (by positivity)))
        (fun n => hphi_sq _ (add_pos (hL0.trans hLt) (by positivity)))
        (hphi_meas t (hL0.trans hLt)) (hphi_sq t (hL0.trans hLt))
        (hZright t htmem) (hpoint t htmem) (hFrep t htmem)
  exact ⟨hhalf, hdiff.2.2.1, hWx2 t htmem⟩

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow
