import ShenWork.Paper1.WholeLineWeightedRegularityGradientGlobal
import ShenWork.Paper1.WholeLineWeightedRegularityDampedH0

open Filter Function MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Exact-weight H0 propagation through the canonical global restarts

The finite-horizon damped H0 estimate is uniform on each canonical segment.
Spatial covariance lets us normalize the phase accumulated before a restart.
Induction over the half-step restart data then propagates the original
weighted perturbation to every preferred translated datum.
-/

/-- The `n`-th canonical restart datum, translated by the wave phase already
accumulated during the preceding `n` half-steps. -/
def wholeLineCauchyGlobalTranslatedDatumIndex
    (p : CMParams) (u₀ : WholeLineBUC) (c : ℝ) (n : ℕ) : WholeLineBUC :=
  wholeLineBUCTranslate
    (c * ((n : ℝ) * wholeLineCauchyGlobalStep p u₀))
    (wholeLineCauchyGlobalDatum p u₀ n)

@[simp] theorem wholeLineCauchyGlobalTranslatedDatumIndex_zero
    (p : CMParams) (u₀ : WholeLineBUC) (c : ℝ) :
    wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c 0 = u₀ := by
  ext x
  simp [wholeLineCauchyGlobalTranslatedDatumIndex,
    wholeLineCauchyGlobalDatum]

/-- The translated successor datum is the preceding translated canonical
segment at the half-step, observed in the moving coordinate. -/
theorem wholeLineCauchyGlobalTranslatedDatumIndex_succ_apply
    (p : CMParams) (u₀ : WholeLineBUC) (c : ℝ) (n : ℕ) (x : ℝ) :
    (wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c (n + 1)).1 x =
      (wholeLineCauchyBUCMildFixedPoint p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        ⟨wholeLineCauchyGlobalStep p u₀,
          (wholeLineCauchyGlobalStep_pos p u₀).le,
          by
            rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
            linarith [wholeLineCauchyGlobalStep_pos p u₀]⟩).1
        (x + c * wholeLineCauchyGlobalStep p u₀) := by
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let delta := wholeLineCauchyGlobalStep p u₀
  let zdelta : Set.Icc (0 : ℝ) H :=
    ⟨delta, (wholeLineCauchyGlobalStep_pos p u₀).le,
      by
        dsimp only [H, delta]
        rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
        linarith [wholeLineCauchyGlobalStep_pos p u₀]⟩
  simp only [wholeLineCauchyGlobalTranslatedDatumIndex,
    wholeLineCauchyGlobalDatum, wholeLineBUCTranslate_apply,
    Nat.cast_add, Nat.cast_one]
  rw [wholeLineCauchyBUCMildFixedPoint_spatialTranslate]
  simp only [wholeLineBUCTrajectorySpatialTranslate_apply]
  congr 1
  ring

/-- Integrability of the exact-weight initial perturbation is sufficient for
finite-horizon H0 propagation; the scalar initial radius is constructed from
the integral itself. -/
theorem coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_finiteHorizon
    (p : CMParams) {M T eta c : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 < eta)
    (heta_one : eta < 1)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2)) :
    ∀ z : Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |(wholeLineCauchyBUCMildFixedPoint p hM hT u₀₂ hsmall z).1
            (x + c * z.1) -
          (W z).1 (x + c * z.1)| ^ 2) := by
  let I : ℝ := ∫ y : ℝ, Real.exp (2 * eta * y) *
    |u₀₂.1 y - u₀₁.1 y| ^ 2
  let B₀ : ℝ := Real.sqrt I
  have hI : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun y =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hB₀ : 0 ≤ B₀ := Real.sqrt_nonneg _
  have henergy : (∫ y : ℝ, Real.exp (2 * eta * y) *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2 := by
    change I ≤ (Real.sqrt I) ^ 2
    rw [sq_sqrt hI]
  obtain ⟨B, hB, hprop⟩ :=
    exists_bound_coMoving_mildFixedPoint_difference_fullWeightedL2_finiteHorizon
      p hM hT heta heta_one hB₀ u₀₂ u₀₁ W hfixed hsmall
        hdata_full henergy
  exact fun z => (hprop z).1

/-- Exact-weight H0 propagation along every canonical half-step, relative to
any phase-normalized fixed reference trajectory. -/
theorem wholeLineCauchyGlobalTranslatedDatumIndex_fullWeightedL2_integrable
    (p : CMParams) (u₀ : WholeLineBUC) {eta c : ℝ}
    (heta : 0 < eta) (heta_one : eta < 1)
    (uWave : WholeLineBUC)
    (W : WholeLineBUCTrajectory (wholeLineCauchyGlobalSegmentTime p u₀))
    (hfixed : IsFixedPt
      (wholeLineCauchyBUCMildMap p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le uWave) W)
    {Uw : ℝ → ℝ}
    (huWave : ∀ x, uWave.1 x = Uw x)
    (hW : ∀ z x, (W z).1 (x + c * z.1) = Uw x)
    (hinitial : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |u₀.1 x - Uw x| ^ 2)) :
    ∀ n : ℕ, Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |(wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n).1 x -
        Uw x| ^ 2) := by
  intro n
  induction n with
  | zero =>
      simpa only [wholeLineCauchyGlobalTranslatedDatumIndex_zero] using hinitial
  | succ n ih =>
      let H := wholeLineCauchyGlobalSegmentTime p u₀
      let delta := wholeLineCauchyGlobalStep p u₀
      let zdelta : Set.Icc (0 : ℝ) H :=
        ⟨delta, (wholeLineCauchyGlobalStep_pos p u₀).le,
          by
            dsimp only [H, delta]
            rw [wholeLineCauchyGlobalSegmentTime_eq_two_step]
            linarith [wholeLineCauchyGlobalStep_pos p u₀]⟩
      have hdata : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
          |(wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n).1 x -
            uWave.1 x| ^ 2) := by
        refine ih.congr (ae_of_all _ fun x => ?_)
        simp only [huWave x]
      have hnext :=
        coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_finiteHorizon
          p (c := c) (wholeLineCauchyGlobalClamp_pos p u₀).le
          (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
          heta heta_one
          (wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n) uWave W
          hfixed (wholeLineCauchyGlobalSegmentTime_rate p u₀) hdata zdelta
      refine hnext.congr (ae_of_all _ fun x => ?_)
      dsimp only [zdelta, delta, H]
      rw [wholeLineCauchyGlobalTranslatedDatumIndex_succ_apply]
      rw [hW]

/-! The preceding induction is deliberately stated for an abstract fixed
reference trajectory.  The traveling-wave specialization below will supply
that trajectory without adding any weighted regularity premise. -/

/-- Traveling-wave specialization of the canonical restart induction.  All
analytic assumptions below are unweighted stationary-wave facts used only to
realize the reference as a fixed point of the same clamped mild map. -/
theorem wholeLineCauchyGlobalTranslatedDatumIndex_fullWeightedL2_integrable_wave
    (p : CMParams) (u₀ : WholeLineBUC) {eta c D E Kflux FD B : ℝ}
    (heta : 0 < eta) (heta_one : eta < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hMChi : MChi p ≤ wholeLineCauchyGlobalClamp p u₀)
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
    (hinitial : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |u₀.1 x - Uw x| ^ 2)) :
    ∀ n : ℕ, Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |(wholeLineCauchyGlobalTranslatedDatumIndex p u₀ c n).1 x -
        Uw x| ^ 2) := by
  let M := wholeLineCauchyGlobalClamp p u₀
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  have hM1 : 1 ≤ M :=
    (MChi_ge_one_of_travelingWave hTW hbound).trans hMChi
  have hM : 0 ≤ M := zero_le_one.trans hM1
  let hUunif : UniformContinuous Uw :=
    travelingWave_U_uniformContinuous hTW hreg.U_cont
  let hUM : ∀ x, |Uw x| ≤ M := fun x => by
    rw [abs_of_pos (hTW.U_pos x)]
    exact (hbound.le_MChi x).trans hMChi
  let uWave : WholeLineBUC :=
    wholeLineTranslatedProfileBUC Uw hUunif M hUM c 0
  let W : WholeLineBUCTrajectory H :=
    wholeLineTranslatedProfileTrajectoryFrom
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      Uw hUunif M hUM c 0
  have hfixed : IsFixedPt
      (wholeLineCauchyBUCMildMap p hM
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le uWave) W := by
    simpa only [M, H, hUunif, hUM, uWave, W] using
      (IsTravelingWave.translatedProfileTrajectoryFrom_isFixedPt
        p hTW hbound hreg
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le hMChi
        hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
        hreact hreact_cont hgrad_int (a := 0))
  have huWave : ∀ x, uWave.1 x = Uw x := by
    intro x
    simp only [uWave, wholeLineTranslatedProfileBUC_apply, mul_zero, sub_zero]
  have hW : ∀ z x, (W z).1 (x + c * z.1) = Uw x := by
    intro z x
    simp only [W, wholeLineTranslatedProfileTrajectoryFrom_apply,
      zero_add]
    congr 1
    ring
  exact wholeLineCauchyGlobalTranslatedDatumIndex_fullWeightedL2_integrable
    p u₀ heta heta_one uWave W hfixed huWave hW hinitial

/-- The preferred translated datum used by the positive-time global chart is
exactly the indexed phase-normalized datum, so the preceding induction closes
the former global `hWx2` H0 leaf. -/
theorem wholeLineCauchyGlobalPreferredTranslatedDatum_fullWeightedL2_integrable_wave
    (p : CMParams) (u₀ : WholeLineBUC) {eta c t D E Kflux FD B : ℝ}
    (heta : 0 < eta) (heta_one : eta < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hMChi : MChi p ≤ wholeLineCauchyGlobalClamp p u₀)
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
    (hinitial : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |u₀.1 x - Uw x| ^ 2)) :
    Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |(wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t).1 x -
        Uw x| ^ 2) := by
  simpa only [wholeLineCauchyGlobalPreferredTranslatedDatum,
    wholeLineCauchyGlobalPreferredSpatialShift,
    wholeLineCauchyGlobalTranslatedDatumIndex] using
    (wholeLineCauchyGlobalTranslatedDatumIndex_fullWeightedL2_integrable_wave
      p u₀ heta heta_one hTW hbound hreg hMChi hD hFD hB
      hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
      hreact_cont hgrad_int hinitial (wholeLineCauchyGlobalIndex p u₀ t))

/-- Natural χ≤0 global weighted-gradient producer.  The original weighted
initial closeness is propagated internally to the preferred restart datum;
no positive-time weighted H0 hypothesis remains. -/
theorem paper5WeightedPopulationX_sq_integrable_global_chi_nonpos_of_initialCloseness
    (p : CMParams) (hchi : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c t D E Kflux FD B : ℝ}
    (ht : 0 < t) (hBlog : 0 ≤ Blog)
    (heta : 0 < eta) (heta_one : eta < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hlog : ∀ y, |deriv Uw y / Uw y| ≤ Blog)
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
    Integrable (fun x =>
      paper5WeightedPopulationX eta
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) Uw t x ^ 2)
      volume := by
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi
  have hMChi : MChi p ≤ wholeLineCauchyGlobalClamp p u₀ := by
    rw [MChi_eq_one_of_chi_nonpos p hchi]
    have hstable : 1 ≤ wholeLineCauchyStableCeiling p u₀ :=
      wholeLineCauchyStableCeiling_one_le hregime u₀
    unfold wholeLineCauchyGlobalClamp
    linarith
  have hrestart :=
    wholeLineCauchyGlobalPreferredTranslatedDatum_fullWeightedL2_integrable_wave
      p u₀ (t := t) heta heta_one hTW hbound hreg hMChi hD hFD hB hUd hUdd
      hUddcont hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont
      hgrad_int (by simpa only [WeightedL2InitialCloseness] using hclose)
  exact paper5WeightedPopulationX_sq_integrable_global_chi_nonpos
    p hchi u₀ hu₀ ht hBlog heta heta_one hTW hbound hreg hlog
      hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
      hreact hreact_cont hgrad_int hrestart

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.wholeLineCauchyGlobalTranslatedDatumIndex_succ_apply
#print axioms
  ShenWork.Paper1.coMoving_mildFixedPoint_difference_fullWeightedL2_integrable_finiteHorizon
#print axioms
  ShenWork.Paper1.wholeLineCauchyGlobalTranslatedDatumIndex_fullWeightedL2_integrable
#print axioms
  ShenWork.Paper1.wholeLineCauchyGlobalTranslatedDatumIndex_fullWeightedL2_integrable_wave
#print axioms
  ShenWork.Paper1.wholeLineCauchyGlobalPreferredTranslatedDatum_fullWeightedL2_integrable_wave
#print axioms
  ShenWork.Paper1.paper5WeightedPopulationX_sq_integrable_global_chi_nonpos_of_initialCloseness
