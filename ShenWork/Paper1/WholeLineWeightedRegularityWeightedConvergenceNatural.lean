import ShenWork.Paper1.WholeLineWeightedRegularityEventualEnergyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyDifferentiableNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalSliceH0Natural
import ShenWork.Paper1.WholeLineWeightedRegularityTailEnergyDecay
import ShenWork.Paper1.WholeLineWeightedRegularityWaveStaticNatural

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural weighted convergence for negative sensitivity

The canonical wave data discharge every static coefficient input of the
positive-time energy identity.  The global limsup ceiling then makes the
corrected quadratic strictly negative on a time tail.  Positive-time
differentiability, exact-weight H0 propagation, and tail-start Gronwall close
the weighted convergence statement without any endpoint regularity at time
zero.
-/

/-- For strictly negative sensitivity, the canonical whole-line Cauchy orbit
converges to the reference wave in the admissible exponentially weighted L2
moving frame. -/
theorem wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_neg_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ < 0)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hregime).A
      (paper531ConcreteStabilityBudget p hregime).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    CoMovingWeightedL2Convergence eta c
      (wholeLineCauchyGlobalU p u₀) U := by
  have hs : Paper5WaveStaticNaturalData p c U V :=
    paper5WaveStaticNaturalData_of_wave p (ne_of_lt hchi) hc hTW hbound hreg
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc).trans hroot
  have heta_one : eta < 1 := by
    have hcap_one : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    exact hetaCap.trans_le hcap_one
  obtain ⟨M, _hM, hquadratic, htail⟩ :=
    wholeLineCauchyGlobal_eventually_weightedEnergy_deriv_le_negative_natural
      (Blog := 1) (D := paper5ConcreteLu p)
      (E := paper5WaveSecondDerivativeBound p c)
      (Kflux := paper5WaveFluxBound p)
      (FD := paper5WaveFluxDerivativeBound p)
      (B := paper5WaveShiftedReactionBound p)
      p hregime hchi u₀ hu₀ hroot hetaCap hs.hBlog heta heta_one
        hc hTW hbound hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd
        hs.hUddcont hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont
        hs.hreact hs.hreact_cont hs.hgrad_int hinitial
  let C : ℝ := 2 * paper531Quadratic c
    (paper531CommonA p M) (paper531CommonB p M) eta
  have hC : C < 0 := by
    dsimp only [C]
    linarith
  have hgrowth : ∀ᶠ t in atTop,
      deriv (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) t ≤
        C * paper5WeightedEnergy eta c
          (wholeLineCauchyGlobalU p u₀) U t := by
    filter_upwards [htail] with t ht
    simpa only [C] using ht.2
  have hdiff : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ
      (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) t := by
    intro t ht
    exact
      wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_natural
        (Blog := 1) (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hchi u₀ hu₀ ht hs.hBlog heta heta_one hetaCap hc hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial
  have hcont : ContinuousOn
      (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    exact (hdiff t ht).continuousAt.continuousWithinAt
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt
      (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U)
      (deriv (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) t) t := by
    intro t ht
    exact (hdiff t ht).hasDerivAt
  have henergy_int : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * eta * z) *
        |wholeLineCauchyGlobalU p u₀ t (z + c * t) - U z| ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simpa only [coMovingPath] using
      (wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_nonpos_of_initialCloseness
        (D := paper5ConcreteLu p)
        (E := paper5WaveSecondDerivativeBound p c)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBound p)
        (B := paper5WaveShiftedReactionBound p)
        p hchi.le u₀ ht heta heta_one hTW hbound hreg hs.hD hs.hFD
          hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
          hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
          hs.hgrad_int hinitial)
  exact CoMovingWeightedL2Convergence.of_paper5WeightedEnergy_eventual_decay
    hC hcont hderiv hgrowth henergy_int

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_neg_natural

end AxiomAudit

end ShenWork.Paper1
