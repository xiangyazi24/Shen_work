import ShenWork.Paper1.WholeLineWeightedRegularityEnergyProducerLocal
import ShenWork.Paper1.WholeLineWeightedRegularityCandidateContinuity
import ShenWork.Paper1.WholeLineWeightedRegularityActualRightDerivativeContinuous

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted energy from realized state, gradient, and forcing trajectories

Equality with the full mild candidate supplies state continuity, while a
continuous Holder forcing supplies every right generator derivative.  Thus
the two trajectory hypotheses carried by the local energy producer are
consequences rather than inputs.
-/

/-- The four regularity inputs of the weighted-energy calculation, produced
from realized state, gradient, and forcing trajectories on one window. -/
theorem paper5WeightedEnergy_regularInputs_of_realized_candidate_window
    (p : CMParams) {T eta c a r t theta H K : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {X F : ℝ → WholeLineRealL2}
    (ha0 : 0 < a) (hat : a < t) (htr : t < r) (hrT : r < T)
    (htheta : 0 < theta) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hXcont : ContinuousOn X (Set.Icc a r))
    (hFcont : Continuous F)
    (hFbound : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a r, ∀ q ∈ Set.Icc a r,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hactual : ∀ q ∈ Set.Icc a r,
      wholeLineRealL2Total
          (paper5WeightedPopulation eta (coMovingPath c u) U q) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U a)) F q)
    (hu : ∀ q ∈ Set.Ioo a r, ∀ x, 0 ≤ coMovingPath c u q x)
    (hu2 : ∀ q ∈ Set.Ioo a r,
      ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Ioo a r,
      ContDiff ℝ 2 (coMovingPath c v q))
    (hclose : ∀ q ∈ Set.Ioo a r, Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2))
    (hWx2 : ∀ q ∈ Set.Ioo a r, Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hXrep : ∀ q ∈ Set.Ioo a r,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hFrep : ∀ q ∈ Set.Ioo a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q))
    (hpoint : ∀ q ∈ Set.Ioo a r, ∀ x,
      HasDerivAt
        (fun s => paper5WeightedPopulation eta (coMovingPath c u) U s x)
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) q x) q) :
    ContDiff ℝ 2 (coMovingPath c u t) ∧
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
  let A : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatFullGeneratorValue eta c a q
      (wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U a)) F
  have hZcont : ContinuousOn (fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta (coMovingPath c u) U q))
      (Set.Ioo a r) :=
    (paper5WeightedPopulation_continuousOn_of_candidate_window_continuous_forcing
      (eta := eta) (c := c) (u := coMovingPath c u) (U := U)
      (a := a) (r := r) (hat.le.trans htr.le) hFcont hactual).mono
        Set.Ioo_subset_Icc_self
  have hZright : ∀ q ∈ Set.Ioo a r,
      HasDerivWithinAt (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
        (A q + F q) (Set.Ici q) q := by
    intro q hq
    exact paper5WeightedPopulation_hasDerivWithinAt_right_of_candidate_window_continuous
      (eta := eta) (c := c) (u := coMovingPath c u) (U := U)
      hq.1 hq.2 htheta hH hK hactual
      (fun s hs => hFbound s ⟨hs.1, hs.2.trans hq.2.le⟩)
      (fun s hs z hz => hFholder s
        ⟨hs.1, hs.2.trans hq.2.le⟩ z
        ⟨hz.1, hz.2.trans hq.2.le⟩)
      hFcont
  have hcore :=
    paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local
      p ha0 hat htr hrT hsol hTW hU2 hV2 hZcont
        (hXcont.mono Set.Ioo_subset_Icc_self) hFcont.continuousOn hu hu2
        hv2 hclose hWx2 hXrep hFrep hZright hpoint
  exact ⟨hu2 t ⟨hat, htr⟩, hcore⟩

/-- Realized gradient and forcing trajectories, together with the exact
full-candidate restart, feed the local weighted-energy producer. -/
theorem paper5WeightedEnergy_deriv_le_common_of_realized_candidate_window
    (p : CMParams) {M T eta c a r t theta H K : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {X F : ℝ → WholeLineRealL2}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (ha0 : 0 < a) (hat : a < t) (htr : t < r) (hrT : r < T)
    (htheta : 0 < theta) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hXcont : ContinuousOn X (Set.Icc a r))
    (hFcont : Continuous F)
    (hFbound : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a r, ∀ q ∈ Set.Icc a r,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hactual : ∀ q ∈ Set.Icc a r,
      wholeLineRealL2Total
          (paper5WeightedPopulation eta (coMovingPath c u) U q) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U a)) F q)
    (hu : ∀ q ∈ Set.Ioo a r, ∀ x, 0 ≤ coMovingPath c u q x)
    (hu2 : ∀ q ∈ Set.Ioo a r,
      ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Ioo a r,
      ContDiff ℝ 2 (coMovingPath c v q))
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hclose : ∀ q ∈ Set.Ioo a r, Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2))
    (hWx2 : ∀ q ∈ Set.Ioo a r, Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hXrep : ∀ q ∈ Set.Ioo a r,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hFrep : ∀ q ∈ Set.Ioo a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q))
    (hpoint : ∀ q ∈ Set.Ioo a r, ∀ x,
      HasDerivAt
        (fun s => paper5WeightedPopulation eta (coMovingPath c u) U s x)
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) q x) q)
    (hrem_int : Integrable
      (paper5CorrectedRemainderDensity p eta c
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U t)
        (paper5WeightedPopulationX eta (coMovingPath c u) U t)
        (paper5WeightedSignal eta (coMovingPath c v) V t)
        (paper5WeightedSignalX eta (coMovingPath c v) V t) t)) :
    deriv (paper5WeightedEnergy eta c u U) t ≤
      2 * paper531Quadratic c (paper531CommonA p M)
        (paper531CommonB p M) eta * paper5WeightedEnergy eta c u U t := by
  let A : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatFullGeneratorValue eta c a q
      (wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U a)) F
  have hZcont : ContinuousOn (fun q => wholeLineRealL2Total
      (paper5WeightedPopulation eta (coMovingPath c u) U q))
      (Set.Ioo a r) :=
    (paper5WeightedPopulation_continuousOn_of_candidate_window_continuous_forcing
      (eta := eta) (c := c) (u := coMovingPath c u) (U := U)
      (a := a) (r := r) (hat.le.trans htr.le) hFcont hactual).mono
        Set.Ioo_subset_Icc_self
  have hZright : ∀ q ∈ Set.Ioo a r,
      HasDerivWithinAt (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
        (A q + F q) (Set.Ici q) q := by
    intro q hq
    exact paper5WeightedPopulation_hasDerivWithinAt_right_of_candidate_window_continuous
      (eta := eta) (c := c) (u := coMovingPath c u) (U := U)
      hq.1 hq.2 htheta hH hK hactual
      (fun s hs => hFbound s ⟨hs.1, hs.2.trans hq.2.le⟩)
      (fun s hs z hz => hFholder s
        ⟨hs.1, hs.2.trans hq.2.le⟩ z
        ⟨hz.1, hz.2.trans hq.2.le⟩)
      hFcont
  exact paper5WeightedEnergy_deriv_le_common_of_exactGeneratorWindow_local
    p hchi hc heta hetaCap ha0 hat htr hrT hsol hTW hreg hbound hMChiM
      hU2 hV2 hZcont (hXcont.mono Set.Ioo_subset_Icc_self)
      hFcont.continuousOn hu hu2 hv2 huM hvEq hclose hWx2 hXrep hFrep
      hZright hpoint hrem_int

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedEnergy_regularInputs_of_realized_candidate_window
#print axioms
  ShenWork.Paper1.paper5WeightedEnergy_deriv_le_common_of_realized_candidate_window
