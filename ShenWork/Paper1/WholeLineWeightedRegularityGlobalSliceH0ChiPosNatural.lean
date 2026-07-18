import ShenWork.Paper1.WholeLineWeightedRegularityGlobalSliceH0Natural

open Filter Function MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# χ>0 global slice H⁰ integrability via StableWaveParameterRegime

Mirror of `wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_nonpos_of_initialCloseness`
for positive sensitivity χ>0.  Uses StableWaveParameterRegime to get the ceiling
regime and the critical-case MChi ≤ clamp bound.
-/

theorem
    wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_pos_of_initialCloseness
    (p : CMParams) (hstable : StableWaveParameterRegime p) (hchi_pos : 0 < p.χ)
    (u₀ : WholeLineBUC)
    {eta c t D E Kflux FD B : ℝ}
    (ht : 0 < t) (heta : 0 < eta) (heta_one : eta < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
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
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hclose : WeightedL2InitialCloseness eta u₀.1 Uw) :
    Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |coMovingPath c (wholeLineCauchyGlobalU p u₀) t x - Uw x| ^ 2) := by
  let M := wholeLineCauchyGlobalClamp p u₀
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let datum := wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t
  let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 x
  have hregime : WholeLineCauchyCeilingRegime p :=
    hstable.toWholeLineCauchyCeilingRegime
  have hMChi : MChi p ≤ M := by
    have hbranch := hstable.positive_branch_of_chi_nonneg hchi_pos.le
    have hparam : wholeLineCauchyParameterCeiling p = MChi p := by
      unfold wholeLineCauchyParameterCeiling
      rw [if_neg (not_lt.mpr (le_of_eq hbranch.2))]
    have hle : MChi p ≤ wholeLineCauchyStableCeiling p u₀ := by
      rw [← hparam]
      exact le_max_right _ _
    unfold M wholeLineCauchyGlobalClamp
    linarith
  have hH : 0 ≤ H := by
    simpa only [H] using (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
  have hq : q ∈ Set.Icc (0 : ℝ) H := by
    constructor
    · simpa only [q] using (wholeLineCauchyGlobalLocalTime_pos p u₀ ht).le
    · exact (show q < H from by
        simpa only [q, H] using
          wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le).le
  have hdata : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |datum.1 x - Uw x| ^ 2) := by
    simpa only [datum] using
      wholeLineCauchyGlobalPreferredTranslatedDatum_fullWeightedL2_integrable_wave
        p u₀ (t := t) heta heta_one hTW hbound hreg hMChi hD hFD hB
        hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
        hreact_cont hgrad_int
        (by simpa only [WeightedL2InitialCloseness] using hclose)
  let I : ℝ := ∫ x : ℝ, Real.exp (2 * eta * x) *
    |datum.1 x - Uw x| ^ 2
  let B₀ : ℝ := Real.sqrt I
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun x =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hB₀ : 0 ≤ B₀ := Real.sqrt_nonneg _
  have henergy : (∫ x : ℝ, Real.exp (2 * eta * x) *
      |datum.1 x - Uw x| ^ 2) ≤ B₀ ^ 2 := by
    change I ≤ (Real.sqrt I) ^ 2
    rw [Real.sq_sqrt hI]
  obtain ⟨F, hF, hfull⟩ :=
    exists_uniform_fullWeighted_mildFixedPoint_wave_value_inputs_finiteHorizon
      (M := M) (T := H) (eta := eta) (c := c) (B₀ := B₀)
      (D := D) (E := E) (Kflux := Kflux) (FD := FD) (B := B)
      p hH heta heta_one hB₀ datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        hTW hbound hreg hMChi hD hFD hB hUd hUdd hUddcont hflux
        hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
        hdata henergy
  have hlocal : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |coMovingPath c u q x - Uw x| ^ 2) := by
    simpa only [u, Traj, H, q, datum,
      wholeLineCauchyGlobalPreferredTranslatedSegment] using
      (hfull q hq).1
  have hco : coMovingPath c (wholeLineCauchyGlobalU p u₀) t =
      coMovingPath c u q := by
    simpa only [u, Traj, q] using
      wholeLineCauchyGlobal_coMoving_eq_preferredTranslatedSegment
        p u₀ (c := c) ht
  simpa only [hco] using hlocal

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.wholeLineCauchyGlobal_fullWeightedL2_integrable_wave_chi_pos_of_initialCloseness
