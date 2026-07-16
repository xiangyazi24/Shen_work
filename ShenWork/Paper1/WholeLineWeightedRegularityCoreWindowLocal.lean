import ShenWork.Paper1.WholeLineWeightedRegularityHalfEnergyFromGenerator
import ShenWork.Paper1.WholeLineWeightedRegularitySecondDerivFromGenerator

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Fully window-local weighted-energy core data

The right generator derivative on one positive-time window now supplies all
three inputs of the weighted-energy core without sampling any slice outside
that window.
-/

/-- Window-local exact-generator data produce the half-energy derivative,
the diffusion pairing, and the weighted gradient square integrability at the
target time. -/
theorem paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local
    (p : CMParams) {T eta c L R t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {X A F : ℝ → WholeLineRealL2}
    (hL0 : 0 < L) (hLt : L < t) (htR : t < R) (hRT : R < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
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
    paper5WeightedHalfEnergy_hasDerivAt_of_exactGeneratorWindow_local
      p hL0 hLt htR hRT hsol hTW hU2 hV2 hZcont hXcont hFcont hu hu2
        hv2 hclose hWx2 hXrep hFrep hZright hpoint
  have hphi_meas : ∀ q ∈ Set.Ioo L R, AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U q) volume := by
    intro q hq
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        ((hu2 q hq).continuous.sub hU2.continuous)).aestronglyMeasurable
  have hphi_sq : ∀ q ∈ Set.Ioo L R, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) volume := by
    intro q hq
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference
      (hclose q hq)
  let r : ℝ := (t + R) / 2
  have htr : t < r := by dsimp only [r]; linarith
  have hrR : r < R := by dsimp only [r]; linarith
  have hArep : (((A t : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
          (c - 2 * eta) *
            paper5WeightedPopulationX eta (coMovingPath c u) U t x +
          (eta ^ 2 - c * eta) *
            paper5WeightedPopulation eta (coMovingPath c u) U t x) := by
    apply
      paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative_window
        p hsol (hL0.trans hLt) (htR.trans hRT) htr hTW (hu t htmem)
          ((hu2 t htmem).of_le (by norm_num)) (hv2 t htmem)
          (hU2.of_le (by norm_num)) hV2
    · intro s hs
      exact hphi_meas s ⟨hLt.trans_le hs.1, hs.2.trans_lt hrR⟩
    · intro s hs
      exact hphi_sq s ⟨hLt.trans_le hs.1, hs.2.trans_lt hrR⟩
    · exact hZright t htmem
    · exact hpoint t htmem
    · exact hFrep t htmem
  have hdiff :=
    paper5WeightedPopulation_mul_second_integrable_of_generator_representation
      (hu2 t htmem) hU2 (hclose t htmem) (hWx2 t htmem) hArep
  exact ⟨hhalf, hdiff, hWx2 t htmem⟩

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local
