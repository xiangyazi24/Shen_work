import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroCoreAssemblyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalSliceH0Natural
import ShenWork.Paper1.WholeLineWeightedRegularityTailEnergyDecay
import ShenWork.Paper1.WholeLineWeightedRegularityWaveStaticBoundedNatural

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical weighted convergence at zero sensitivity

At `chi = 0` the exact weighted-energy coefficient is
`eta^2 - c*eta + 1`.  The corrected stability budget has `A = B = 0`, so
the existing perturbed-root window makes this coefficient strictly negative.
The wave-static inputs use compactness of `U'` rather than the explicit
nonzero-sensitivity derivative formula.
-/

/-- For zero sensitivity, the canonical whole-line Cauchy orbit converges to
the reference wave in every corrected admissible exponentially weighted
moving frame. -/
theorem wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_zero_natural
    (p : CMParams) (hregime : StableWaveParameterRegime p)
    (hchi : p.χ = 0)
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
  obtain ⟨D, hs⟩ :=
    paper5WaveStaticBoundedData_of_wave p hc hTW hbound hreg
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hregime).rootMinus_pos hc).trans
      hroot
  have heta_one : eta < 1 := by
    simpa [stabilityWeightCap, hchi] using hetaCap
  have hA : paper531ConcreteA p = 0 := by
    simp [paper531ConcreteA, paper531CorrectedAFromBounds,
      paper5ConcreteB1, paper5ConcreteB3, hchi]
  have hB : paper531ConcreteB p = 0 := by
    simp [paper531ConcreteB, paper531CorrectedBFromBounds, hchi]
  have hquadratic : eta ^ 2 - c * eta + 1 < 0 := by
    have hq := (paper531ConcreteStabilityBudget p hregime).quadratic_neg
      hc hroot hetaCap
    simpa [paper531Quadratic, hA, hB] using hq
  let C : ℝ := 2 * (eta ^ 2 - c * eta + 1)
  have hC : C < 0 := by
    dsimp only [C]
    linarith
  have hdiff : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ
      (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) t := by
    intro t ht
    exact
      (wholeLineCauchyGlobal_weightedEnergy_data_chi_zero_natural
        (D := D)
        (E := paper5WaveSecondDerivativeBoundOf p c D)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p D)
        (B := paper5WaveShiftedReactionBound p)
        p hchi u₀ hu₀ ht hs.hBlog heta heta_one hetaCap hc hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial).1
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
  have hgrowth : ∀ᶠ t in atTop,
      deriv (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) t ≤
        C * paper5WeightedEnergy eta c
          (wholeLineCauchyGlobalU p u₀) U t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hdata :=
      wholeLineCauchyGlobal_weightedEnergy_data_chi_zero_natural
        (D := D)
        (E := paper5WaveSecondDerivativeBoundOf p c D)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p D)
        (B := paper5WaveShiftedReactionBound p)
        p hchi u₀ hu₀ ht hs.hBlog heta heta_one hetaCap hc hTW hbound
          hreg hs.hlog hs.hD hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont
          hs.hflux hs.hfluxd hs.hflux_has hs.hfluxd_cont hs.hreact
          hs.hreact_cont hs.hgrad_int hinitial
    simpa only [C] using hdata.2
  have henergy_int : ∀ᶠ t in atTop, Integrable (fun z : ℝ =>
      Real.exp (2 * eta * z) *
        |wholeLineCauchyGlobalU p u₀ t (z + c * t) - U z| ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simpa only [coMovingPath] using
      (wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_nonpos_of_initialCloseness
        (D := D)
        (E := paper5WaveSecondDerivativeBoundOf p c D)
        (Kflux := paper5WaveFluxBound p)
        (FD := paper5WaveFluxDerivativeBoundOf p D)
        (B := paper5WaveShiftedReactionBound p)
        p hchi.le u₀ ht heta heta_one hTW hbound hreg hs.hD hs.hFD
          hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
          hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
          hs.hgrad_int hinitial)
  exact CoMovingWeightedL2Convergence.of_paper5WeightedEnergy_eventual_decay
    hC hcont hderiv hgrowth henergy_int

section AxiomAudit

#print axioms
  wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_zero_natural

end AxiomAudit

end ShenWork.Paper1
