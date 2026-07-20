import ShenWork.Paper1.WholeLineWeightedRegularityFixedBoundEnergyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityEnergyEnvelope
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalStrictPositivityNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalSliceH0Natural
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalSliceH0ChiPosNatural
import ShenWork.Paper1.Theorem12Step4EnergyProducer

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical Section 5 hcore energy package

This file packages the completed natural weighted-energy argument on the
canonical whole-line Cauchy solution.  It supplies every analytic field of the
Section 5 `hcore` interface except the logically independent far-left moving
frame convergence statement.
-/

/-- The canonical solution for paper-faithful nonnegative BUC data supplies
the strict global solution, a smooth scalar envelope with the exact
caller-selected common-bound coefficient, eventual exact-weight
integrability, and the Step 4 spatial modulus.

No left-tail convergence is asserted here. -/
theorem paperNonnegativeInitialDatum_hcore_energy_available_data_natural
    (p : CMParams) (hstable : StableWaveParameterRegime p)
    {c eta : ℝ} {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hstrictWave : HasStrictWaveUpperTailBound p c U)
    (hroot : paper531RootMinus c
      (paper531ConcreteStabilityBudget p hstable).A
      (paper531ConcreteStabilityBudget p hstable).B < eta)
    (hetaCap : eta < stabilityWeightCap p)
    (u₀ : ℝ → ℝ) (hu₀ : PaperNonnegativeInitialDatum u₀)
    (hleft₀ : StrictlyPositiveAtLeft u₀)
    (hinitial : WeightedL2InitialCloseness eta u₀ U)
    (M : ℝ) (hM : MChi p < M) :
    ∃ u v : ℝ → ℝ → ℝ, ∃ E : ℝ → ℝ,
      IsGlobalCauchySolutionFrom p u₀ u v ∧
      (∀ᶠ t in atTop,
        coMovingWeightedL2Energy eta c u U t ≤ E t) ∧
      (∀ T : ℝ, 0 ≤ T → ContinuousOn E (Set.Icc 0 T)) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ t ∈ Set.Ico 0 T,
        HasDerivWithinAt E (deriv E t) (Set.Ici t) t) ∧
      (∀ t : ℝ, 0 ≤ t → deriv E t ≤
        2 * paper531Quadratic c (paper531CommonA p M)
            (paper531CommonB p M) eta * E t) ∧
      EventuallyIntegrableMovingFrameEnergy eta 0
        (coMovingPath c u) U ∧
      EventuallyUniformMovingFrameSpatialModulus 0
        (coMovingPath c u) U := by
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  let u : ℝ → ℝ → ℝ := wholeLineCauchyGlobalU p w
  let v : ℝ → ℝ → ℝ := wholeLineCauchyGlobalV p w
  let F : ℝ → ℝ := paper5WeightedEnergy eta c u U
  let C : ℝ := 2 * paper531Quadratic c (paper531CommonA p M)
    (paper531CommonB p M) eta
  have hw₀ : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  have hleftW : StrictlyPositiveAtLeft w.1 := by
    simpa [w] using hleft₀
  have hinitialW : WeightedL2InitialCloseness eta w.1 U := by
    simpa [w] using hinitial
  have hbound : HasWaveUpperTailBound p c U :=
    hstrictWave.hasWaveUpperTailBound
  have hceiling : WholeLineCauchyCeilingRegime p :=
    hstable.toWholeLineCauchyCeilingRegime
  have heta : 0 < eta :=
    ((paper531ConcreteStabilityBudget p hstable).rootMinus_pos hc).trans
      hroot
  have heta_one : eta < 1 := by
    have hcap_one : stabilityWeightCap p ≤ 1 := by
      unfold stabilityWeightCap
      rw [div_le_one (by positivity)]
      exact le_add_of_nonneg_right
        (Real.rpow_nonneg (abs_nonneg _) _)
    exact hetaCap.trans_le hcap_one
  have hdiff : ∀ t : ℝ, 0 < t → DifferentiableAt ℝ F t := by
    intro t ht
    dsimp only [F, u]
    exact
      wholeLineCauchyGlobal_weightedEnergy_differentiableAt_positive_stable_natural
        p hstable w hw₀ ht heta heta_one hetaCap hc hTW hbound hreg
          hinitialW
  have hcont : ContinuousOn F (Set.Ioi (0 : ℝ)) := by
    intro t ht
    exact (hdiff t ht).continuousAt.continuousWithinAt
  have hderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt F (deriv F t) t := by
    intro t ht
    exact (hdiff t ht).hasDerivAt
  have hfixed :=
    wholeLineCauchyGlobal_eventually_weightedEnergy_deriv_le_fixed_common_natural
      p hstable w hw₀ hM heta heta_one hetaCap hc hTW hbound hreg hinitialW
  have hgrowth : ∀ᶠ t in atTop, deriv F t ≤ C * F t := by
    filter_upwards [hfixed] with t ht
    simpa only [F, C, u] using ht.2
  obtain ⟨E, hcontrolF, hEcont, hEderiv, hEdiss⟩ :=
    scalarEnergy_eventual_exponential_envelope_of_eventual_positive_time_deriv
      hcont hderiv hgrowth
  have hsol : IsGlobalCauchySolutionFrom p u₀ u v := by
    dsimp only [u, v]
    simpa [w] using
      (wholeLineCauchyGlobal_isGlobalCauchySolutionFrom_of_posAtBot
        p hceiling w hw₀ hleftW)
  have hphysicalControl : ∀ᶠ t in atTop,
      coMovingWeightedL2Energy eta c u U t ≤ F t := by
    simpa only [u, F] using
      (wholeLineCauchyGlobal_step4Energy_available_data
        p hceiling w hw₀ eta c U).2.1
  have hcontrol : ∀ᶠ t in atTop,
      coMovingWeightedL2Energy eta c u U t ≤ E t := by
    filter_upwards [hphysicalControl, hcontrolF] with t hphysical henvelope
    exact hphysical.trans henvelope
  obtain ⟨D, hs⟩ :=
    paper5WaveStaticBoundedData_of_wave p hc hTW hbound hreg
  have henergyInt : EventuallyIntegrableMovingFrameEnergy eta 0
      (coMovingPath c u) U := by
    unfold EventuallyIntegrableMovingFrameEnergy
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    by_cases hchi_pos : 0 < p.χ
    · have hslice :=
        wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_pos_of_initialCloseness
          (D := D)
          (E := paper5WaveSecondDerivativeBoundOf p c D)
          (Kflux := paper5WaveFluxBound p)
          (FD := paper5WaveFluxDerivativeBoundOf p D)
          (B := paper5WaveShiftedReactionBound p)
          p hstable hchi_pos w ht heta heta_one hTW hbound hreg hs.hD
            hs.hFD hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
            hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
            hs.hgrad_int hinitialW
      simpa [movingFrameError, u] using hslice
    · have hchi_nonpos : p.χ ≤ 0 := le_of_not_gt hchi_pos
      have hslice :=
        wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_nonpos_of_initialCloseness
          (D := D)
          (E := paper5WaveSecondDerivativeBoundOf p c D)
          (Kflux := paper5WaveFluxBound p)
          (FD := paper5WaveFluxDerivativeBoundOf p D)
          (B := paper5WaveShiftedReactionBound p)
          p hchi_nonpos w ht heta heta_one hTW hbound hreg hs.hD hs.hFD
            hs.hB hs.hUd hs.hUdd hs.hUddcont hs.hflux hs.hfluxd
            hs.hflux_has hs.hfluxd_cont hs.hreact hs.hreact_cont
            hs.hgrad_int hinitialW
      simpa [movingFrameError, u] using hslice
  have hmod : EventuallyUniformMovingFrameSpatialModulus 0
      (coMovingPath c u) U := by
    dsimp only [u]
    exact wholeLineCauchyGlobal_eventuallyUniformMovingFrameSpatialModulus
      p hceiling w hw₀ c hTW hreg
  refine ⟨u, v, E, hsol, hcontrol, hEcont, hEderiv, ?_, henergyInt, hmod⟩
  intro t ht
  simpa only [C] using hEdiss t ht

section AxiomAudit

#print axioms paperNonnegativeInitialDatum_hcore_energy_available_data_natural

end AxiomAudit

end ShenWork.Paper1
