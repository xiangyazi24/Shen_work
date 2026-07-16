import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroSharpEnergyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityCompactHolderClosure
import ShenWork.Paper1.WholeLineWeightedRegularityGlobalEnergyNatural

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural exact-weight energy assembly at zero sensitivity

The population `H1` trajectory is independent of the sensitivity sign.  At
`chi = 0`, its value modulus feeds the reaction-only forcing trajectory.  The
physical weighted restart then realizes the exact generator candidate, so the
zero-sensitivity energy inequality follows at every positive target time from
the canonical mild fixed point and the ordinary wave data.
-/

/-- The canonical mild fixed point satisfies the exact-weight differential
energy inequality at every positive interior time when `chi = 0`.  All
positive-window Hilbert trajectories and the physical restart are constructed
internally. -/
theorem
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_data_chi_zero_natural
    (p : CMParams) (hchi : p.χ = 0)
    {M T t Blog eta c D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht0 : 0 < t) (htT : t < T)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta)
    (heta_one : eta < 1) (hetaCap : eta < stabilityWeightCap p)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hMChi : MChi p ≤ M)
    (hlog : ∀ y, |deriv U y / U y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |u₀.1 y - U y| ^ 2)) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    DifferentiableAt ℝ (paper5WeightedEnergy eta c u U) t ∧
      deriv (paper5WeightedEnergy eta c u U) t ≤
        2 * (eta ^ 2 - c * eta + 1) *
          paper5WeightedEnergy eta c u U t := by
  dsimp only
  obtain ⟨L, a, r, R, hL0, hLa, hat, htr, hrR, hRT,
      _hdiamOuter, _hshort⟩ :=
    exists_paper5WeightedGeneratorShortWindow
      (eta := eta) (c := c) ht0 htT
  have ha0 : 0 < a := hL0.trans hLa
  have har : a ≤ r := (hat.trans htr).le
  have hrT : r < T := hrR.trans hRT
  have hdiam : r - a ≤ 1 := by linarith
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
  have htrajectory :=
    exists_wholeLineCauchyBUCMildFixedPoint_weighted_population_H1_trajectory_data
      p hM hT hL0 hLa har hrT hdiam hBlog heta heta_one hetaCap
        u₀ hsmall hstrip hc hTW hbound hreg hMChi hlog hD hFD hB
        hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
        hreact_cont hgrad_int hdata_full
  dsimp only at htrajectory
  obtain ⟨W, X, EW, EWx, HW, HWx, hEW, _hEWx, hHW, _hHWx,
      hWrep, hXrep, hWx2, hWnorm, _hXnorm, hXcont, hWmod, _hXmod⟩ :=
    htrajectory
  obtain ⟨_hsol, huM, _hu2, _hv2, hWjoint, _hWmeas, _hFmeas,
      _hpoint⟩ :=
    wholeLineCauchyBUCMildFixedPoint_positive_window_pointwise_data
      (eta := eta) (c := c) p hM hT ha0 har hrT
        u₀ hsmall hstrip hTW hreg
  have hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M := fun x =>
    ⟨(hTW.U_pos x).le, (hbound.le_MChi x).trans hMChi⟩
  have huC : ∀ q ∈ Set.Icc a r, IsCUnifBdd (coMovingPath c u q) := by
    intro q hq
    have hq0 : 0 ≤ q := ha0.le.trans hq.1
    let zq : Set.Icc (0 : ℝ) T :=
      ⟨q, hq0, hq.2.trans hrT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT Traj q = Traj zq :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zq.2
    have huq : IsCUnifBdd (u q) := by
      simpa only [u, hext] using WholeLineBUC.isCUnifBdd (Traj zq)
    simpa only [coMovingPath] using
      isCUnifBdd_comp_add_const huq (c * q)
  have hUC : IsCUnifBdd U := by
    refine ⟨hreg.U_cont, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (hUM x).1]
    exact (hUM x).2
  have hWsq : ∀ q ∈ Set.Icc a r, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) := by
    intro q hq
    exact integrable_sq_of_wholeLineRealL2_ae_eq (W q) (hWrep q hq)
  have hweight : ∀ q ∈ Set.Icc a r, ∀ x : ℝ,
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2 =
        Real.exp (2 * eta * x) *
          |coMovingPath c u q x - U x| ^ 2 := by
    intro q hq x
    unfold paper5WeightedPopulation
    rw [mul_pow, sq_abs, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hclose : ∀ q ∈ Set.Icc a r, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2) := by
    intro q hq
    exact (hWsq q hq).congr
      (Eventually.of_forall fun x => hweight q hq x)
  have hclose_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2) ≤ EW ^ 2 := by
    intro q hq
    have hnormsq :=
      wholeLineRealL2_norm_sq_eq_integral_sq_of_aeEq (W q) (hWrep q hq)
    calc
      (∫ x : ℝ, Real.exp (2 * eta * x) *
          |coMovingPath c u q x - U x| ^ 2) =
          ∫ x : ℝ,
            paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2 := by
            apply integral_congr_ae
            filter_upwards with x
            exact (hweight q hq x).symm
      _ = ‖W q‖ ^ 2 := hnormsq.symm
      _ ≤ EW ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hEW).2 (hWnorm q hq)
  have hWdiff : ∀ s ∈ Set.Icc a r, ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ =>
        (paper5WeightedPopulation eta (coMovingPath c u) U s x -
          paper5WeightedPopulation eta (coMovingPath c u) U q x) ^ 2) := by
    intro s hs q hq
    apply integrable_sq_of_wholeLineRealL2_ae_eq (W s - W q)
    filter_upwards [Lp.coeFn_sub (W s) (W q), hWrep s hs, hWrep q hq]
      with x hsub hsx hqx
    rw [hsub]
    simp only [Pi.sub_apply, hsx, hqx, u, Traj]
  have hWdiff_le : ∀ s ∈ Set.Icc a r, ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ,
        (paper5WeightedPopulation eta (coMovingPath c u) U s x -
          paper5WeightedPopulation eta (coMovingPath c u) U q x) ^ 2) ≤
        HW ^ 2 *
          (|s - q| ^ paper5ForcingTimeExponent p) ^ 2 := by
    intro s hs q hq
    have hA : 0 ≤ HW * |s - q| ^ paper5ForcingTimeExponent p :=
      mul_nonneg hHW (Real.rpow_nonneg (abs_nonneg _) _)
    have hraw := wholeLineIntegral_sub_sq_le_of_norm_sub_le
      (W s) (W q) (hWrep s hs) (hWrep q hq) hA (hWmod s hs q hq)
    calc
      (∫ x : ℝ,
          (paper5WeightedPopulation eta (coMovingPath c u) U s x -
            paper5WeightedPopulation eta (coMovingPath c u) U q x) ^ 2) ≤
          (HW * |s - q| ^ paper5ForcingTimeExponent p) ^ 2 := hraw
      _ = HW ^ 2 *
          (|s - q| ^ paper5ForcingTimeExponent p) ^ 2 := by ring
  let F : ℝ → WholeLineRealL2 :=
    paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
      p eta c u v U V har
  obtain ⟨H, hH, hFdata, _hFholder, hFcont, hFrep⟩ :=
    exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_chi_zero_data
      p hchi har hM (paper5ForcingTimeExponent_pos p) huC hUC huM hUM
        hclose hclose_le hWdiff hWdiff_le
  let Cf : ℝ := reactionLip p.α M ^ 2 * EW ^ 2
  have hCf : 0 ≤ Cf := by
    dsimp only [Cf]
    positivity
  obtain ⟨_alpha, _Hraw, _Draw, _halpha, _halpha1, _hHraw, _hDraw,
      _hrawCont, _hrawHolder, _hrawBound, _hrawJoint, hfJoint, hfactor⟩ :=
    exists_paper5CanonicalGeneratorForcingRaw_positive_window_natural_data
      p hM hT ha0 har hrT u₀ hsmall hstrip hTW hbound hreg hMChi
        hFD hfluxd
  let f : ℝ → ℝ → ℝ :=
    paper5WeightedGeneratorForcingPositiveWindowClamped
      p eta c hM hT Traj U V har
  have hf_sq : ∀ q ∈ Set.Icc a r,
      Integrable (fun x : ℝ => f q x ^ 2) := by
    intro q hq
    refine (hFdata q hq).1.congr (Eventually.of_forall fun x => ?_)
    simpa only [f, Traj, u, v] using
      congrArg (fun z : ℝ => z ^ 2) (hfactor q hq x).symm
  have hf_le : ∀ q ∈ Set.Icc a r,
      (∫ x : ℝ, f q x ^ 2) ≤ Cf := by
    intro q hq
    rw [show (∫ x : ℝ, f q x ^ 2) =
        ∫ x : ℝ, paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2 by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [f, Traj, u, v] using
        congrArg (fun z : ℝ => z ^ 2) (hfactor q hq x)]
    exact (hFdata q hq).2
  have hFrepClamped : ∀ q ∈ Set.Icc a r,
      (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q) := by
    intro q hq
    filter_upwards [hFrep q hq] with x hx
    rw [hx]
    simpa only [f, Traj, u, v] using (hfactor q hq x).symm
  have hscalarRestart : ∀ q ∈ Set.Ioc a r, ∀ x,
      paper5WeightedPopulation eta (coMovingPath c u) U q x =
        weightedMovingHeatEta eta c (q - a)
            (paper5WeightedPopulation eta (coMovingPath c u) U a) x +
          weightedMovingHeatValueHistory eta c a q f x := by
    intro q hq x
    have hrawRestart :=
      wholeLineCauchyBUCMildFixedPoint_weighted_generator_restart
        (eta := eta) p hM hT ha0 hq.1 (hq.2.trans_lt hrT) u₀ hsmall
          (theta := (1 / 2 : ℝ)) (zeta := (1 / 4 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hstrip hTW hbound hreg hD
          (show 0 ≤ E from le_trans (abs_nonneg (deriv (deriv U) 0))
            (hUdd 0)) hUd hUdd hUddcont x
    change paper5WeightedPopulation eta (coMovingPath c u) U q x = _
    rw [show paper5WeightedPopulation eta (coMovingPath c u) U q x =
        weightedMovingHeatEta eta c (q - a)
            (paper5WeightedPopulation eta (coMovingPath c u) U a) x +
          ∫ s in a..q, weightedMovingHeatEta eta c (q - s)
            (paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) U V s) x by
      simpa only [u, v, Traj] using hrawRestart]
    congr 1
    unfold weightedMovingHeatValueHistory
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume a, Measure.ae_ne volume q]
      with s hsa hsq hs
    rw [Set.uIoc_of_le hq.1.le] at hs
    have hsIcc : s ∈ Set.Icc a r :=
      ⟨hs.1.le, hs.2.trans hq.2⟩
    rw [show f s = paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V s by
      funext y
      simpa only [f, Traj, u, v] using hfactor s hsIcc y]
  have hactual : ∀ q ∈ Set.Icc a r,
      wholeLineRealL2Total
          (paper5WeightedPopulation eta (coMovingPath c u) U q) =
        weightedMovingHeatFullGeneratorCandidate eta c a
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U a)) F q :=
    weightedMovingHeatFullGeneratorCandidate_eq_on_window_of_pointwise_restart_bounded_measurable
      (eta := eta) (c := c) (a := a) (r := r) (Cf := Cf) (F := F)
        hCf hWjoint hfJoint hWsq hf_sq hf_le hFrepClamped
        hFcont.aestronglyMeasurable
        (fun q hq => Eventually.of_forall (hscalarRestart q hq))
  exact
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_data_chi_zero_sharp_of_realized_window
      p hchi hM hT ha0 hat htr hrT (paper5ForcingTimeExponent_pos p)
        u₀ hsmall hstrip hTW hreg hUM hXcont hclose hclose_le hWdiff
        hWdiff_le hactual
        (fun q hq => hWx2 q ⟨hq.1.le, hq.2.le⟩)
        (fun q hq => hXrep q ⟨hq.1.le, hq.2.le⟩)

/-- Preferred-segment transport of the zero-sensitivity energy inequality to
the canonical global Cauchy solution.  The coefficient uses the canonical
global construction clamp; no nonzero-sensitivity coefficient package is
present. -/
theorem wholeLineCauchyGlobal_weightedEnergy_data_chi_zero_natural
    (p : CMParams) (hchi : p.χ = 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c t D E Kflux FD B : ℝ}
    (ht : 0 < t)
    (hBlog : 0 ≤ Blog) (heta : 0 < eta) (heta_one : eta < 1)
    (hetaCap : eta < stabilityWeightCap p)
    {U V : ℝ → ℝ}
    (hc : paper5CorrectedCStarStar p p.χ < c)
    (hTW : IsTravelingWave p c U V)
    (hbound : HasWaveUpperTailBound p c U)
    (hreg : TravelingWaveRegularity p c U V)
    (hlog : ∀ y, |deriv U y / U y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv U y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv U) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv U)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p U V y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p U V) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p U V)
      (deriv (wholeLineTravelingWaveFlux p U V) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p U V)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p U y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p U))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p U V) x) volume 0 q)
    (hinitial : WeightedL2InitialCloseness eta u₀.1 U) :
    DifferentiableAt ℝ (paper5WeightedEnergy eta c
      (wholeLineCauchyGlobalU p u₀) U) t ∧
      deriv (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) t ≤
        2 * (eta ^ 2 - c * eta + 1) *
          paper5WeightedEnergy eta c
            (wholeLineCauchyGlobalU p u₀) U t := by
  let M₀ := wholeLineCauchyGlobalClamp p u₀
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let a := (wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
    wholeLineCauchyGlobalStep p u₀
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let d := wholeLineCauchyGlobalPreferredSpatialShift p u₀ c t
  let Base := wholeLineCauchyGlobalSegment p u₀
    (wholeLineCauchyGlobalIndex p u₀ t)
  let datum := wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t
  let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 x
  have hchi_le : p.χ ≤ 0 := hchi.le
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi_le
  have hM₀ : 0 ≤ M₀ := (wholeLineCauchyGlobalClamp_pos p u₀).le
  have hH : 0 ≤ H := (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
  have hq0 : 0 < q := by
    simpa only [q] using wholeLineCauchyGlobalLocalTime_pos p u₀ ht
  have hqH : q < H := by
    simpa only [q, H] using
      wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le
  have hMChi₀ : MChi p ≤ M₀ := by
    rw [MChi_eq_one_of_chi_nonpos p hchi_le]
    have hstable : 1 ≤ wholeLineCauchyStableCeiling p u₀ :=
      wholeLineCauchyStableCeiling_one_le hregime u₀
    unfold M₀ wholeLineCauchyGlobalClamp
    linarith
  have hstrip : ∀ z : Set.Icc (0 : ℝ) H, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM₀ hH datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) z).1 x ∈
          Set.Icc (0 : ℝ) M₀ := by
    intro z x
    have hbase :=
      (wholeLineCauchyGlobalDatum_segment_bounds p hregime u₀ hu₀
        (wholeLineCauchyGlobalIndex p u₀ t)).2.1 z (x + d)
    change (Traj z).1 x ∈ Set.Icc (0 : ℝ) M₀
    rw [show Traj = wholeLineBUCTrajectorySpatialTranslate hH d Base by
      simpa only [Traj, d, Base, hH] using
        wholeLineCauchyGlobalPreferredTranslatedSegment_eq p u₀ c t]
    simpa only [wholeLineBUCTrajectorySpatialTranslate_apply,
      M₀, H, d, Base] using hbase
  have hdata : Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
      |datum.1 x - U x| ^ 2) := by
    simpa only [datum] using
      wholeLineCauchyGlobalPreferredTranslatedDatum_fullWeightedL2_integrable_wave
        p u₀ (t := t) heta heta_one hTW hbound hreg hMChi₀ hD hFD hB
        hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
        hreact_cont hgrad_int
        (by simpa only [WeightedL2InitialCloseness] using hinitial)
  have hlocal :=
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_data_chi_zero_natural
      p hchi hM₀ hH hq0 hqH hBlog heta heta_one hetaCap datum
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) hstrip hc hTW
        hbound hreg hMChi₀ hlog hD hFD hB hUd hUdd hUddcont hflux
        hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int hdata
  dsimp only at hlocal
  have hderiv :=
    wholeLineCauchyGlobal_weightedEnergy_deriv_eq_preferredTranslated
      p hregime u₀ hu₀ (eta := eta) (c := c) (U := U) ht
  dsimp only at hderiv
  have hshift : DifferentiableAt ℝ
      (fun s => paper5WeightedEnergy eta c u U (s - a)) t := by
    have hcomp := hlocal.1.comp t (differentiableAt_id.sub_const a)
    simpa only [q, wholeLineCauchyGlobalLocalTime, a] using hcomp
  have henergyEv :=
    wholeLineCauchyGlobal_weightedEnergy_eventuallyEq_preferredTranslated
      p hregime u₀ hu₀ (eta := eta) (c := c) (U := U) ht
  dsimp only at henergyEv
  have hglobalDiff : DifferentiableAt ℝ
      (paper5WeightedEnergy eta c
        (wholeLineCauchyGlobalU p u₀) U) t :=
    henergyEv.differentiableAt_iff.mpr hshift
  have henergy := henergyEv.eq_of_nhds
  have henergy' : paper5WeightedEnergy eta c u U q =
      paper5WeightedEnergy eta c (wholeLineCauchyGlobalU p u₀) U t := by
    simpa only [u, Traj, q, wholeLineCauchyGlobalLocalTime] using
      henergy.symm
  refine ⟨hglobalDiff, ?_⟩
  rw [hderiv]
  calc
    deriv (paper5WeightedEnergy eta c u U) q ≤
        2 * (eta ^ 2 - c * eta + 1) *
          paper5WeightedEnergy eta c u U q := by
      simpa only [u, Traj, M₀, H, q, datum] using hlocal.2
    _ = 2 * (eta ^ 2 - c * eta + 1) *
          paper5WeightedEnergy eta c
            (wholeLineCauchyGlobalU p u₀) U t := by
      rw [henergy']

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_weightedEnergy_data_chi_zero_natural
#print axioms
  ShenWork.Paper1.wholeLineCauchyGlobal_weightedEnergy_data_chi_zero_natural
