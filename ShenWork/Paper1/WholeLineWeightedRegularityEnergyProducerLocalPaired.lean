import ShenWork.Paper1.WholeLineWeightedRegularityEnergyProducerLocal

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Paired HasDerivAt + inequality from one local window (Q5314 adapter 1)

The existing `paper5WeightedEnergy_deriv_le_common_of_exactGeneratorWindow_local`
exports only the `deriv`-inequality. Since `deriv` is totalized, that inequality
alone is not a differentiability certificate. This wrapper exports BOTH the
`HasDerivAt` and the inequality from the same local window, so the consumer
gets an actual derivative fact.
-/

theorem paper5WeightedEnergy_hasDerivAt_and_deriv_le_of_exactGeneratorWindow_local
    (p : CMParams) {M T eta c L R t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {X A F : ℝ → WholeLineRealL2}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hL0 : 0 < L) (hLt : L < t) (htR : t < R) (hRT : R < T)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
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
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
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
          (paper5CoMovingMaterialTime c u) q x) q)
    (hrem_int : Integrable
      (paper5CorrectedRemainderDensity p eta c
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U t)
        (paper5WeightedPopulationX eta (coMovingPath c u) U t)
        (paper5WeightedSignal eta (coMovingPath c v) V t)
        (paper5WeightedSignalX eta (coMovingPath c v) V t) t)) :
    HasDerivAt (paper5WeightedEnergy eta c u U)
        (deriv (paper5WeightedEnergy eta c u U) t) t ∧
      deriv (paper5WeightedEnergy eta c u U) t ≤
        2 * paper531Quadratic c (paper531CommonA p M)
          (paper531CommonB p M) eta * paper5WeightedEnergy eta c u U t := by
  obtain ⟨hhalf, _hdiff, _hgrad⟩ :=
    paper5WeightedEnergy_coreIntegrability_of_exactGeneratorWindow_local
      p hL0 hLt htR hRT hsol hTW hU2 hV2 hZcont hXcont hFcont hu hu2
        hv2 hclose hWx2 hXrep hFrep hZright hpoint
  have hfull := paper5WeightedEnergy_hasDerivAt_of_half hhalf
  refine ⟨hfull.differentiableAt.hasDerivAt, ?_⟩
  exact paper5WeightedEnergy_deriv_le_common_of_exactGeneratorWindow_local
    p hchi hc heta hetaCap hL0 hLt htR hRT hsol hTW hreg hbound hMChiM
      hU2 hV2 hZcont hXcont hFcont hu hu2 hv2 huM hvEq hclose hWx2 hXrep
      hFrep hZright hpoint hrem_int

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedEnergy_hasDerivAt_and_deriv_le_of_exactGeneratorWindow_local
