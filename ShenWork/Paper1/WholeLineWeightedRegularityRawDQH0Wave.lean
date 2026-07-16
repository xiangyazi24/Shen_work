import ShenWork.Paper1.WholeLineWeightedRegularityH0ToRawCap
import ShenWork.Paper1.WholeLineWeightedRegularityWaveTrajectory

open Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

set_option maxHeartbeats 2000000

/-!
# Exact-weight H0 inputs around a traveling wave

This file specializes the finite-horizon damped H0 propagation theorem to
the canonical translated traveling-wave fixed point.  The resulting cap
value and raw spatial-difference-quotient bounds are uniform in the cap
radius.  In particular, no weighted spatial derivative is used.
-/

/-- The exact-weight initial distance to a traveling wave supplies all four
fixed-cap inputs consumed by the concrete raw-DQ PDE step.  The raw-DQ radius
is exposed explicitly so that its `|h⁻¹|` loss can be used by the subsequent
Henry-profile closure. -/
theorem exists_uniform_capWeighted_mildFixedPoint_wave_value_rawDQ_inputs_finiteHorizon
    (p : CMParams)
    {M T eta c h B₀ D E Kflux FD B : ℝ}
    (hT : 0 ≤ T) (heta : 0 < eta) (heta_one : eta < 1)
    (hh : h ≠ 0) (hB₀ : 0 ≤ B₀)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hMChi : MChi p ≤ M)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ t, 0 < t → ∀ x, IntervalIntegrable
      (fun q : ℝ => paper5MovingFrameHeatGradOp c q
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 t)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀.1 y - Uw y| ^ 2))
    (hdata_energy : (∫ y : ℝ, Real.exp (2 * eta * y) *
      |u₀.1 y - Uw y| ^ 2) ≤ B₀ ^ 2) :
    ∃ F X : ℝ, 0 ≤ F ∧ 0 ≤ X ∧
      X = eta * F +
        Real.sqrt
          (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F ∧
      ∀ R : ℝ,
        (∀ s ∈ Set.Icc (0 : ℝ) T, Integrable (fun x : ℝ =>
          capWeight eta R x *
            |(wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildFixedPoint p
                  (zero_le_one.trans
                    ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
                  hT u₀ hsmall) s).1 (x + c * s) - Uw x| ^ 2)) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T, Integrable (fun x : ℝ =>
          capWeight eta R x *
            |eta * ((wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildFixedPoint p
                  (zero_le_one.trans
                    ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
                  hT u₀ hsmall) s).1 (x + c * s) - Uw x) +
              spatialDifferenceQuotient h (fun y =>
                (wholeLineBUCTrajectoryExtend hT
                  (wholeLineCauchyBUCMildFixedPoint p
                    (zero_le_one.trans
                      ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
                    hT u₀ hsmall) s).1 (y + c * s) - Uw y) x| ^ 2)) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          (∫ x : ℝ, capWeight eta R x *
            |eta * ((wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildFixedPoint p
                  (zero_le_one.trans
                    ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
                  hT u₀ hsmall) s).1 (x + c * s) - Uw x) +
              spatialDifferenceQuotient h (fun y =>
                (wholeLineBUCTrajectoryExtend hT
                  (wholeLineCauchyBUCMildFixedPoint p
                    (zero_le_one.trans
                      ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
                    hT u₀ hsmall) s).1 (y + c * s) - Uw y) x| ^ 2) ≤
            X ^ 2) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) T,
          (∫ x : ℝ, capWeight eta R x *
            |(wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildFixedPoint p
                  (zero_le_one.trans
                    ((MChi_ge_one_of_travelingWave hTW hbound).trans hMChi))
                  hT u₀ hsmall) s).1 (x + c * s) - Uw x| ^ 2) ≤
            F ^ 2) := by
  have hM1 : 1 ≤ M :=
    (MChi_ge_one_of_travelingWave hTW hbound).trans hMChi
  have hM : 0 ≤ M := zero_le_one.trans hM1
  let hUunif : UniformContinuous Uw :=
    travelingWave_U_uniformContinuous hTW hreg.U_cont
  let hUM : ∀ x, |Uw x| ≤ M := fun x => by
    rw [abs_of_pos (hTW.U_pos x)]
    exact (hbound.le_MChi x).trans hMChi
  let uW : WholeLineBUC :=
    wholeLineTranslatedProfileBUC Uw hUunif M hUM c 0
  let W : WholeLineBUCTrajectory T :=
    wholeLineTranslatedProfileTrajectoryFrom hT Uw hUunif M hUM c 0
  have hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT uW) W := by
    simpa only [hUunif, hUM, uW, W] using
      (IsTravelingWave.translatedProfileTrajectoryFrom_isFixedPt
        p hTW hbound hreg hT hMChi
        hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
        hreact hreact_cont hgrad_int (a := 0))
  have hdata_full' : Integrable (fun y : ℝ =>
      Real.exp (2 * eta * y) * |u₀.1 y - uW.1 y| ^ 2) := by
    simpa only [uW, wholeLineTranslatedProfileBUC_apply, mul_zero, sub_zero]
      using hdata_full
  have hdata_energy' : (∫ y : ℝ,
      Real.exp (2 * eta * y) * |u₀.1 y - uW.1 y| ^ 2) ≤ B₀ ^ 2 := by
    simpa only [uW, wholeLineTranslatedProfileBUC_apply, mul_zero, sub_zero]
      using hdata_energy
  obtain ⟨F, hF, hH₀⟩ :=
    exists_bound_coMoving_mildFixedPoint_difference_fullWeightedL2_finiteHorizon
      p hM hT heta heta_one hB₀ u₀ uW W hfixed hsmall
        hdata_full' hdata_energy'
  let X : ℝ := eta * F +
    Real.sqrt
      (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * F
  have hX : 0 ≤ X := by
    dsimp only [X]
    exact add_nonneg (mul_nonneg heta.le hF)
      (mul_nonneg (Real.sqrt_nonneg _) hF)
  refine ⟨F, X, hF, hX, rfl, ?_⟩
  intro R
  let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  have hinputs : ∀ s ∈ Set.Icc (0 : ℝ) T,
      let w : ℝ → ℝ := fun x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - Uw x
      (Integrable (fun x : ℝ => capWeight eta R x * |w x| ^ 2) ∧
        (∫ x : ℝ, capWeight eta R x * |w x| ^ 2) ≤ F ^ 2) ∧
      (Integrable (fun x : ℝ => capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h w x| ^ 2) ∧
        (∫ x : ℝ, capWeight eta R x *
          |rawSpatialDifferenceQuotient eta h w x| ^ 2) ≤ X ^ 2) := by
    intro s hs
    let z : Set.Icc (0 : ℝ) T := ⟨s, hs⟩
    let w : ℝ → ℝ := fun x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) - Uw x
    have hext : wholeLineBUCTrajectoryExtend hT Traj s = Traj z :=
      wholeLineBUCTrajectoryExtend_eq hT Traj hs
    have hWshift : ∀ x : ℝ, (W z).1 (x + c * s) = Uw x := by
      intro x
      dsimp only [W, wholeLineTranslatedProfileTrajectoryFrom_apply]
      congr 1
      ring
    have hw : Continuous w := by
      exact ((wholeLineBUCTrajectoryExtend hT Traj s).1.continuous.comp
        (continuous_id.add continuous_const)).sub hreg.U_cont
    have hfun : (fun x : ℝ =>
        Real.exp (2 * eta * x) * |w x| ^ 2) =
        fun x : ℝ => Real.exp (2 * eta * x) *
          |(Traj z).1 (x + c * z.1) - (W z).1 (x + c * z.1)| ^ 2 := by
      funext x
      dsimp only [w, z]
      rw [hext, hWshift]
    have hfull : Integrable (fun x : ℝ =>
        Real.exp (2 * eta * x) * |w x| ^ 2) := by
      rw [hfun]
      exact (hH₀ z).1
    have hfull_energy : (∫ x : ℝ,
        Real.exp (2 * eta * x) * |w x| ^ 2) ≤ F ^ 2 := by
      rw [hfun]
      exact (hH₀ z).2
    have hcap := capWeighted_value_rawDQ_inputs_of_fullWeightedL2
      (R := R) heta.le hh hF hw hfull hfull_energy
    refine ⟨hcap.1, hcap.2.1, ?_⟩
    dsimp only [X]
    exact hcap.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hinputs s hs).1.1
  · intro s hs
    simpa only [rawSpatialDifferenceQuotient] using (hinputs s hs).2.1
  · intro s hs
    simpa only [rawSpatialDifferenceQuotient] using (hinputs s hs).2.2
  · intro s hs
    exact (hinputs s hs).1.2

#print axioms
  exists_uniform_capWeighted_mildFixedPoint_wave_value_rawDQ_inputs_finiteHorizon

end ShenWork.Paper1
