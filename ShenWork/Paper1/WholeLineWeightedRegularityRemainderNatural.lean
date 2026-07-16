import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorForcingNatural
import ShenWork.Paper1.WholeLineWeightedRegularityNaturalPointwiseData
import ShenWork.Paper1.WholeLineWeightedRegularityEnergyProducerLocal

open Filter MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural integrability of the corrected weighted remainder

The corrected remainder is the weighted population multiplied by the full
lower-order source.  On a classical positive-time slice, that source is the
physical generator forcing plus the scalar growth already contained in the
conjugated heat generator.  Thus the existing exact-weight `L2` estimates for
the population and the physical forcing give the missing `L1` remainder
directly by Cauchy--Schwarz.
-/

/-- The four corrected lower-order energy densities are exactly the weighted
population multiplied by the named lower-order source. -/
theorem paper5CorrectedRemainderDensity_eq_population_mul_lowerOrderSource
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U W Wx Z Zx : ℝ → ℝ) (t x : ℝ) :
    paper5CorrectedRemainderDensity p eta c u v U W Wx Z Zx t x =
      W x * paper5WeightedLowerOrderSource
        p eta c u v U W Wx Z Zx t x := by
  unfold paper5CorrectedRemainderDensity paper5WeightedLowerOrderSource
  ring

/-- Classical exact-weight `H1` data make the corrected nonlinear remainder
integrable.  No energy inequality, weighted decay, or stability conclusion is
used in this construction. -/
theorem paper5CorrectedRemainderDensity_integrable_of_population_H1_natural
    (p : CMParams) {M T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)) :
    Integrable
      (paper5CorrectedRemainderDensity p eta c
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U t)
        (paper5WeightedPopulationX eta (coMovingPath c u) U t)
        (paper5WeightedSignal eta (coMovingPath c v) V t)
        (paper5WeightedSignalX eta (coMovingPath c v) V t) t) := by
  let W : ℝ → ℝ :=
    paper5WeightedPopulation eta (coMovingPath c u) U t
  let F : ℝ → ℝ :=
    paper5WeightedGeneratorForcing p eta
      (coMovingPath c u) (coMovingPath c v) U V t
  have hW2 : Integrable (fun x => W x ^ 2) := by
    dsimp only [W]
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference hclose
  have hF2 : Integrable (fun x => F x ^ 2) := by
    dsimp only [F]
    exact (paper5WeightedGeneratorForcing_data_of_population_H1_natural
      p hchi hc heta hetaCap hsol ht0 htT hTW hreg hbound hMChiM
        hu2 hv2 hU2 hV2 huM hvEq hclose hWx2).1
  have hWcont : Continuous W := by
    dsimp only [W]
    unfold paper5WeightedPopulation
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        (hu2.continuous.sub hU2.continuous)
  have hFcont : Continuous F := by
    dsimp only [F]
    exact paper5WeightedGeneratorForcing_continuous_of_classical_slices
      p hsol ht0 htT hTW hu2 hv2 hU2 hV2
  have hWF : Integrable (fun x => W x * F x) :=
    integrable_mul_of_sq_integrable_of_continuous
      hWcont hFcont hW2 hF2
  have hgrowth : Integrable (fun x =>
      (eta ^ 2 - c * eta) * W x ^ 2) :=
    hW2.const_mul (eta ^ 2 - c * eta)
  refine (hWF.add hgrowth).congr (Eventually.of_forall fun x => ?_)
  change W x * F x + (eta ^ 2 - c * eta) * W x ^ 2 = _
  have hsource := paper5WeightedLowerOrderSource_sub_growth_eq_generatorForcing
    p (eta := eta) (c := c) hsol ht0 htT hTW
      (huM x).1 (hTW.U_pos x).le
      (hu2.of_le (by norm_num)) hv2 (hU2.of_le (by norm_num)) hV2
  rw [show F x =
      paper5WeightedLowerOrderSource p eta c
          (coMovingPath c u) (coMovingPath c v) U
          (paper5WeightedPopulation eta (coMovingPath c u) U t)
          (paper5WeightedPopulationX eta (coMovingPath c u) U t)
          (paper5WeightedSignal eta (coMovingPath c v) V t)
          (paper5WeightedSignalX eta (coMovingPath c v) V t) t x -
        (eta ^ 2 - c * eta) * W x by
      simpa only [F, W] using hsource.symm]
  rw [paper5CorrectedRemainderDensity_eq_population_mul_lowerOrderSource]
  ring

/-- The reduced fixed-time weighted energy producer with the nonlinear
remainder integrability discharged from the same classical `H1` data. -/
theorem paper5WeightedEnergy_deriv_le_common_of_coreIntegrability_natural
    (p : CMParams) {M T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hchi : p.χ ≠ 0)
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (heta : 0 < eta) (hetaCap : eta < stabilityWeightCap p)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hMChiM : MChi p ≤ M)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hvEq : coMovingPath c v t =
      frozenElliptic p (coMovingPath c u t))
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2))
    (hhalf : HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x, paper5WeightedPopulation eta (coMovingPath c u) U t x *
        paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t x) t)
    (hdiff_int : Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x *
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)) :
    deriv (paper5WeightedEnergy eta c u U) t ≤
      2 * paper531Quadratic c (paper531CommonA p M)
        (paper531CommonB p M) eta * paper5WeightedEnergy eta c u U t := by
  have hrem :=
    paper5CorrectedRemainderDensity_integrable_of_population_H1_natural
      p hchi hc heta hetaCap hsol ht0 htT hTW hreg hbound hMChiM
        hu2 hv2 hU2 hV2 huM hvEq hclose hWx2
  exact paper5WeightedEnergy_deriv_le_common_of_coreIntegrability
    p hchi hc heta hetaCap hsol ht0 htT hTW hreg hbound hMChiM
      hu2 hv2 hU2 hV2 huM hvEq hclose hhalf hdiff_int hWx2 hrem

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5CorrectedRemainderDensity_eq_population_mul_lowerOrderSource
#print axioms
  ShenWork.Paper1.paper5CorrectedRemainderDensity_integrable_of_population_H1_natural
#print axioms
  ShenWork.Paper1.paper5WeightedEnergy_deriv_le_common_of_coreIntegrability_natural
