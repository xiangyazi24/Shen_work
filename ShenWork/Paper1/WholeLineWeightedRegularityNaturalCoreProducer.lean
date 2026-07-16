import ShenWork.Paper1.WholeLineWeightedRegularityEnergyProducerTrajectory
import ShenWork.Paper1.WholeLineWeightedRegularityNaturalPointwiseData
import ShenWork.Paper1.WholeLineWeightedRegularityForcingWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityFullCandidateUniformHolder
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGradientCandidateNatural
import ShenWork.Paper1.WholeLineWeightedRegularityForcingHolderAssemblyNatural
import ShenWork.Paper1.WholeLineWeightedRegularityCoefficientWindowNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorShortWindow
import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroForcingNatural

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural weighted-energy core for the canonical mild fixed point

This file is the terminal wiring layer for the four analytic inputs of the
weighted-energy calculation.  The population and signal are the canonical
BUC mild fixed point and its frozen elliptic resolver.  Classical slice data
and the pointwise material derivative are reconstructed internally.
-/

/-- A uniform time modulus for the unweighted canonical forcing becomes a
local-in-space modulus for its exact-weight representative.  This is the
compact-space input used to construct a strongly measurable Hilbert
trajectory; no stronger exponential weight is introduced. -/
theorem paper5WeightedGeneratorForcingPositiveWindowClamped_local_holder
    (p : CMParams) {M T a b eta c alpha H : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hab : a ≤ b) (hH : 0 ≤ H)
    (Traj : WholeLineBUCTrajectory T) (U V : ℝ → ℝ)
    (hraw : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
      |s - t| ≤ 1 →
        |paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V s x -
            paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V t x| ≤
          H * |s - t| ^ alpha) :
    ∀ n : ℕ, ∃ Hn : ℝ, 0 ≤ Hn ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        |s - t| ≤ 1 → ∀ x ∈ Set.Icc (-(n : ℝ)) (n : ℝ),
          |paper5WeightedGeneratorForcingPositiveWindowClamped
                p eta c hM hT Traj U V hab s x -
              paper5WeightedGeneratorForcingPositiveWindowClamped
                p eta c hM hT Traj U V hab t x| ≤
            Hn * |s - t| ^ alpha := by
  intro n
  let Hn : ℝ := Real.exp (|eta| * (n : ℝ)) * H
  have hHn : 0 ≤ Hn :=
    mul_nonneg (Real.exp_nonneg _) hH
  refine ⟨Hn, hHn, ?_⟩
  intro s hs t ht hst x hx
  have hsproj : (Set.projIcc a b hab s : Set.Icc a b).1 = s := by
    simpa using congrArg Subtype.val (Set.projIcc_of_mem hab hs)
  have htproj : (Set.projIcc a b hab t : Set.Icc a b).1 = t := by
    simpa using congrArg Subtype.val (Set.projIcc_of_mem hab ht)
  have hxabs : |x| ≤ (n : ℝ) := (abs_le).2 ⟨hx.1, hx.2⟩
  have hetaMul : eta * x ≤ |eta| * (n : ℝ) := by
    calc
      eta * x ≤ |eta * x| := le_abs_self _
      _ = |eta| * |x| := abs_mul eta x
      _ ≤ |eta| * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hxabs (abs_nonneg eta)
  have hexp : Real.exp (eta * x) ≤ Real.exp (|eta| * (n : ℝ)) :=
    Real.exp_le_exp.mpr hetaMul
  have hraw' := hraw s hs t ht x hst
  simp only [paper5WeightedGeneratorForcingPositiveWindowClamped,
    paper5CanonicalGeneratorForcingRawPositiveWindowClamped,
    hsproj, htproj]
  rw [show
      Real.exp (eta * x) *
            paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V s x -
          Real.exp (eta * x) *
            paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V t x =
        Real.exp (eta * x) *
          (paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V s x -
            paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V t x) by
      ring,
    abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (eta * x) *
        |paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V s x -
          paper5CanonicalGeneratorForcingRaw p c hM hT Traj U V t x| ≤
      Real.exp (eta * x) * (H * |s - t| ^ alpha) :=
        mul_le_mul_of_nonneg_left hraw' (Real.exp_nonneg _)
    _ ≤ Real.exp (|eta| * (n : ℝ)) * (H * |s - t| ^ alpha) :=
      mul_le_mul_of_nonneg_right hexp
        (mul_nonneg hH (Real.rpow_nonneg (abs_nonneg _) _))
    _ = Hn * |s - t| ^ alpha := by
      dsimp only [Hn]
      ring

/-- The canonical fixed point and a traveling wave produce the exact-weight
population and spatial-gradient Hilbert trajectories on a closed positive
window.  All time moduli are quantitative conclusions.  The auxiliary
forcing used to realize the state and gradient is the measurable clamped
physical source and is not exported. -/
theorem
    exists_wholeLineCauchyBUCMildFixedPoint_weighted_population_H1_trajectory_data
    (p : CMParams)
    {M T L a b Blog eta c D E Kflux FD B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hL0 : 0 < L) (hLa : L < a) (hab : a ≤ b) (hbT : b < T)
    (hdiam : b - a ≤ 1)
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
    ∃ W X : ℝ → WholeLineRealL2, ∃ EW EWx HW HWx : ℝ,
      0 ≤ EW ∧ 0 ≤ EWx ∧ 0 ≤ HW ∧ 0 ≤ HWx ∧
      (∀ q ∈ Set.Icc a b,
        (((W q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedPopulation eta (coMovingPath c u) U q)) ∧
      (∀ q ∈ Set.Icc a b,
        (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedPopulationX eta (coMovingPath c u) U q)) ∧
      (∀ q ∈ Set.Icc a b, Integrable (fun x : ℝ =>
        paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2)) ∧
      (∀ q ∈ Set.Icc a b, ‖W q‖ ≤ EW) ∧
      (∀ q ∈ Set.Icc a b, ‖X q‖ ≤ EWx) ∧
      ContinuousOn X (Set.Icc a b) ∧
      (∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖W s - W t‖ ≤ HW *
          |s - t| ^ paper5ForcingTimeExponent p) ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖X s - X t‖ ≤ HWx *
          |s - t| ^ paper5ForcingTimeExponent p := by
  dsimp only
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
  have hLb : L ≤ b := hLa.le.trans hab
  obtain ⟨hsol, huM, hu2, hv2, hWjoint, hWmeas, hFmeas, _hpoint⟩ :=
    wholeLineCauchyBUCMildFixedPoint_positive_window_pointwise_data
      (eta := eta) (c := c) p hM hT hL0 hLb hbT
        u₀ hsmall hstrip hTW hreg
  let E₀ : ℝ := ∫ y : ℝ,
    Real.exp (2 * eta * y) * |u₀.1 y - U y| ^ 2
  let B₀ : ℝ := Real.sqrt E₀
  have hE₀ : 0 ≤ E₀ := by
    dsimp only [E₀]
    exact integral_nonneg fun y =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hB₀ : 0 ≤ B₀ := Real.sqrt_nonneg _
  have hdata_energy :
      (∫ y : ℝ, Real.exp (2 * eta * y) * |u₀.1 y - U y| ^ 2) ≤
        B₀ ^ 2 := by
    dsimp only [B₀, E₀]
    rw [Real.sq_sqrt hE₀]
  obtain ⟨EW, hEW, hfullRaw⟩ :=
    exists_uniform_fullWeighted_mildFixedPoint_wave_value_inputs_finiteHorizon
      p hT heta heta_one hB₀ u₀ hsmall hTW hbound hreg hMChi
        hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has
        hfluxd_cont hreact hreact_cont hgrad_int hdata_full hdata_energy
  have hfull : ∀ q ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : ℝ => Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2) ∧
      (∫ x : ℝ, Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2) ≤ EW ^ 2 := by
    intro q hq
    simpa only [u, Traj, coMovingPath] using hfullRaw q hq
  have hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M := fun x =>
    ⟨(hTW.U_pos x).le, (hbound.le_MChi x).trans hMChi⟩
  have huC : ∀ q ∈ Set.Icc L b, IsCUnifBdd (coMovingPath c u q) := by
    intro q hq
    refine ⟨(hu2 q hq).continuous, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (huM q hq x).1]
    exact (huM q hq x).2
  have hUC : IsCUnifBdd U := by
    refine ⟨hreg.U_cont, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (hUM x).1]
    exact (hUM x).2
  have hforcing_exists : ∃ Cf : ℝ, 0 ≤ Cf ∧
      ∀ q ∈ Set.Icc L b,
        Integrable (fun x : ℝ =>
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) ∧
        (∫ x : ℝ, paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) ≤ Cf := by
    by_cases hchi0 : p.χ = 0
    · let Cf : ℝ := reactionLip p.α M ^ 2 * EW ^ 2
      have hCf : 0 ≤ Cf := by
        dsimp only [Cf]
        positivity
      refine ⟨Cf, hCf, ?_⟩
      intro q hq
      have hqfull : q ∈ Set.Icc (0 : ℝ) T :=
        ⟨hL0.le.trans hq.1, hq.2.trans hbT.le⟩
      have hraw := paper5WeightedGeneratorForcing_chi_zero_l2_data
        p hchi0 (u := coMovingPath c u) (v := coMovingPath c v)
          (U := U) (V := V) hM (huC q hq) hUC (huM q hq) hUM
          (hfull q hqfull).1
      exact ⟨hraw.1, hraw.2.trans (by
        dsimp only [Cf]
        gcongr
        exact (hfull q hqfull).2)⟩
    · exact
        exists_uniform_weightedGeneratorForcing_square_bound_mildFixedPoint_wave
          p hM hT hL0 hLb hbT (show 0 ≤ Blog from hBlog) heta
            heta_one hetaCap u₀ hsmall hstrip hchi0 hc hTW hbound hreg
            hMChi hlog hD hFD hB hUd hUdd hUddcont hflux hfluxd
            hflux_has hfluxd_cont hreact hreact_cont hgrad_int hdata_full
  obtain ⟨Cf, hCf, hforcing⟩ := hforcing_exists
  obtain ⟨alpha, Hraw, Draw, halpha, _halpha1, hHraw, hDraw,
      hrawCont, hrawHolder, hrawBound, hrawJoint, hfJoint, hfactor⟩ :=
    exists_paper5CanonicalGeneratorForcingRaw_positive_window_natural_data
      p hM hT hL0 hLb hbT u₀ hsmall hstrip hTW hbound hreg hMChi
        hFD hfluxd
  let raw : ℝ → ℝ → ℝ :=
    paper5CanonicalGeneratorForcingRawPositiveWindowClamped
      p c hM hT Traj U V hLb
  let f : ℝ → ℝ → ℝ :=
    paper5WeightedGeneratorForcingPositiveWindowClamped
      p eta c hM hT Traj U V hLb
  have hf_meas : ∀ q ∈ Set.Icc L b,
      AEStronglyMeasurable (f q) volume := by
    intro q hq
    exact hfJoint.of_uncurry_left.aestronglyMeasurable
  have hf_sq : ∀ q ∈ Set.Icc L b,
      Integrable (fun x : ℝ => f q x ^ 2) volume := by
    intro q hq
    refine (hforcing q hq).1.congr (Eventually.of_forall fun x => ?_)
    have heq := hfactor q hq x
    simpa only [f, Traj] using congrArg (fun z : ℝ => z ^ 2) heq.symm
  have hf_le : ∀ q ∈ Set.Icc L b,
      (∫ x : ℝ, f q x ^ 2) ≤ Cf := by
    intro q hq
    have hqf := (hforcing q hq).2
    rw [show (∫ x : ℝ, f q x ^ 2) =
        ∫ x : ℝ, paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2 by
      apply integral_congr_ae
      filter_upwards with x
      have heq := hfactor q hq x
      simpa only [f, u, v, Traj] using congrArg (fun z : ℝ => z ^ 2) heq]
    exact hqf
  have hf_local : ∀ n : ℕ, ∃ Hn : ℝ, 0 ≤ Hn ∧
      ∀ s ∈ Set.Icc L b, ∀ t ∈ Set.Icc L b,
        |s - t| ≤ 1 → ∀ x ∈ Set.Icc (-(n : ℝ)) (n : ℝ),
          |f s x - f t x| ≤ Hn * |s - t| ^ alpha := by
    simpa only [f, Traj] using
      (paper5WeightedGeneratorForcingPositiveWindowClamped_local_holder
        p hM hT hLb hHraw Traj U V hrawHolder)
  obtain ⟨Faux, hFauxTime, hFauxData⟩ :=
    exists_wholeLineRealL2_clamped_trajectory_of_local_holder
      hLb halpha hf_meas hf_sq hf_le hf_local
  have hFauxRep : ∀ q ∈ Set.Icc L b,
      (((Faux q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] f q) :=
    fun q hq => (hFauxData q hq).1
  let KF : ℝ := Real.sqrt Cf
  have hKF : 0 ≤ KF := Real.sqrt_nonneg _
  have hFauxNorm : ∀ q ∈ Set.Icc L b, ‖Faux q‖ ≤ KF := by
    intro q hq
    have hsq := (hFauxData q hq).2
    have hsqCf : ‖Faux q‖ ^ 2 ≤ KF ^ 2 := by
      rw [show KF ^ 2 = Cf by exact Real.sq_sqrt hCf]
      exact hsq
    exact (sq_le_sq₀ (norm_nonneg _) hKF).mp hsqCf
  have hWsq : ∀ q ∈ Set.Icc L b, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) := by
    intro q hq
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference
      (hfull q ⟨hL0.le.trans hq.1, hq.2.trans hbT.le⟩).1
  have hscalarRestart : ∀ q ∈ Set.Ioc L b, ∀ x,
      paper5WeightedPopulation eta (coMovingPath c u) U q x =
        weightedMovingHeatEta eta c (q - L)
            (paper5WeightedPopulation eta (coMovingPath c u) U L) x +
          weightedMovingHeatValueHistory eta c L q f x := by
    intro q hq x
    have hLq : L < q := hq.1
    have hrawRestart :=
      wholeLineCauchyBUCMildFixedPoint_weighted_generator_restart
        (eta := eta) p hM hT hL0 hLq (hq.2.trans_lt hbT) u₀ hsmall
          (theta := (1 / 2 : ℝ)) (zeta := (1 / 4 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) hstrip hTW hbound hreg hD (show 0 ≤ E from by
            exact le_trans (abs_nonneg (deriv (deriv U) 0)) (hUdd 0))
          hUd hUdd hUddcont x
    change paper5WeightedPopulation eta (coMovingPath c u) U q x = _
    rw [show paper5WeightedPopulation eta (coMovingPath c u) U q x =
        weightedMovingHeatEta eta c (q - L)
            (paper5WeightedPopulation eta (coMovingPath c u) U L) x +
          ∫ s in L..q, weightedMovingHeatEta eta c (q - s)
            (paper5WeightedGeneratorForcing p eta
              (coMovingPath c u) (coMovingPath c v) U V s) x by
      simpa only [u, v, Traj] using hrawRestart]
    congr 1
    unfold weightedMovingHeatValueHistory
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume L, Measure.ae_ne volume q]
      with s hsL hsq hs
    rw [Set.uIoc_of_le hLq.le] at hs
    have hsIcc : s ∈ Set.Icc L b :=
      ⟨hs.1.le, hs.2.trans hq.2⟩
    rw [show f s = paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V s by
      funext y
      simpa only [f, u, v, Traj] using hfactor s hsIcc y]
  have hactualAux : ∀ q ∈ Set.Icc a b,
      wholeLineRealL2Total
          (paper5WeightedPopulation eta (coMovingPath c u) U q) =
        weightedMovingHeatFullGeneratorCandidate eta c L
          (wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U L))
          Faux q := by
    have hall :=
      weightedMovingHeatFullGeneratorCandidate_eq_on_window_of_pointwise_restart_bounded_measurable
        (eta := eta) (c := c) (a := L) (r := b) (Cf := Cf) (F := Faux)
        hCf hWjoint hfJoint hWsq hf_sq hf_le hFauxRep hFauxTime
        (fun q hq => Eventually.of_forall (hscalarRestart q hq))
    exact fun q hq => hall q ⟨hLa.le.trans hq.1, hq.2⟩
  let W : ℝ → WholeLineRealL2 := fun q => wholeLineRealL2Total
    (paper5WeightedPopulation eta (coMovingPath c u) U q)
  have hWrep : ∀ q ∈ Set.Icc a b,
      (((W q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulation eta (coMovingPath c u) U q) := by
    intro q hq
    exact wholeLineRealL2Total_coe_ae _
      (hWmeas q ⟨hLa.le.trans hq.1, hq.2⟩)
      (hWsq q ⟨hLa.le.trans hq.1, hq.2⟩)
  have hWnorm : ∀ q ∈ Set.Icc a b, ‖W q‖ ≤ EW := by
    intro q hq
    have hraw := wholeLineRealL2Total_norm_le_sqrt_of_integral_sq_le
      (C := EW ^ 2) (sq_nonneg EW)
      (hWmeas q ⟨hLa.le.trans hq.1, hq.2⟩)
      (hWsq q ⟨hLa.le.trans hq.1, hq.2⟩)
      (by
        have hqfull := (hfull q
          ⟨hL0.le.trans (hLa.le.trans hq.1), hq.2.trans hbT.le⟩).2
        convert hqfull using 1
        apply integral_congr_ae
        filter_upwards with x
        unfold paper5WeightedPopulation coMovingPath
        rw [mul_pow, sq_abs]
        congr 1
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring)
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hEW] using hraw
  have hhist : ∀ q : ℝ, AEStronglyMeasurable
      (fun s => weightedMovingHeatL2Semigroup eta c (q - s) (Faux s))
      (volume.restrict (Set.Icc L b)) := by
    intro q
    exact weightedMovingHeatL2Semigroup_terminal_history_aestronglyMeasurable_of_aestronglyMeasurable
      (eta := eta) (c := c) (tau := q) (a := L) (r := b) hFauxTime
  obtain ⟨HW, hHW, hWsqrt⟩ :=
    exists_weightedMovingHeatFullGeneratorCandidate_uniform_sqrt_holder
      hLa hab hKF hEW
      (wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U L))
      (fun q hq => hFauxNorm q hq) hhist
      (fun q hq => by
        rw [← hactualAux q hq]
        exact hWnorm q hq)
  have hWsqrtActual : ∀ s ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b,
      ‖W s - W q‖ ≤ HW * Real.sqrt |s - q| := by
    intro s hs q hq
    dsimp only [W]
    rw [hactualAux s hs, hactualAux q hq]
    exact hWsqrt s hs q hq
  have hWmod : ∀ s ∈ Set.Icc a b, ∀ q ∈ Set.Icc a b,
      ‖W s - W q‖ ≤ HW * |s - q| ^ paper5ForcingTimeExponent p := by
    exact uniform_forcingExponent_holder_of_sqrt_holder
      p hdiam hHW hWsqrtActual
  have hWderiv : ∀ q ∈ Set.Icc a b, ∀ x,
      HasDerivAt
        (paper5WeightedPopulation eta (coMovingPath c u) U q)
        (paper5WeightedPopulationX eta (coMovingPath c u) U q x) x := by
    intro q hq x
    exact paper5WeightedPopulation_space_hasDerivAt
      ((hu2 q ⟨hLa.le.trans hq.1, hq.2⟩).differentiable (by norm_num) x)
      ((hreg.U_contDiff_two hTW).differentiable (by norm_num) x)
  have hraw_meas : ∀ q ∈ Set.Ioc L b,
      AEStronglyMeasurable (raw q) volume := by
    intro q hq
    exact hrawJoint.of_uncurry_left.aestronglyMeasurable
  have hraw_bound : ∀ q ∈ Set.Ioc L b, ∀ y, |raw q y| ≤ Draw := by
    intro q hq y
    simpa only [raw, Traj,
      paper5CanonicalGeneratorForcingRawPositiveWindowClamped,
      Set.projIcc_of_mem hLb ⟨hq.1.le, hq.2⟩] using
        hrawBound q ⟨hq.1.le, hq.2⟩ y
  have hfactor' : ∀ q ∈ Set.Ioc L b, ∀ y,
      f q y = Real.exp (eta * y) * raw q y := by
    intro q hq y
    rfl
  obtain ⟨X, EWx, HWx, hEWx, hHWx, hXcont, hXrep, hWx2,
      hXnorm, _hXsqrt, hXmod, _hXintegralMod⟩ :=
    exists_weightedMovingHeatFullGradientCandidate_natural_closed_window
      p hLa hab hdiam halpha hCf hDraw
      (hWmeas L ⟨le_rfl, hLb⟩) (hWsq L ⟨le_rfl, hLb⟩)
      (fun q hq => hscalarRestart q ⟨hLa.trans_le hq.1, hq.2⟩)
      hWderiv hf_meas hf_sq hf_le hf_local hfJoint
      hraw_meas hraw_bound hfactor'
  exact ⟨W, X, EW, EWx, HW, HWx, hEW, hEWx, hHW, hHWx,
    hWrep, hXrep, hWx2, hWnorm, hXnorm, hXcont, hWmod, hXmod⟩

/-- Once the exact state restart and the natural `H¹`/forcing Hilbert
trajectories have been realized on a positive window, the canonical BUC mild
fixed point supplies all four regularity inputs used by the weighted energy
identity.  In particular, spatial `C²` regularity and the pointwise material
time derivative are conclusions of the canonical positive-time theory. -/
theorem wholeLineCauchyBUCMildFixedPoint_weightedEnergy_regularInputs_of_realized_window
    (p : CMParams) {M T eta c a r t theta H K : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hat : a < t) (htr : t < r) (hrT : r < T)
    (htheta : 0 < theta) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    {X F : ℝ → WholeLineRealL2}
    (hXcont : ContinuousOn X (Set.Icc a r))
    (hFcont : Continuous F)
    (hFbound : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K)
    (hFholder : ∀ s ∈ Set.Icc a r, ∀ q ∈ Set.Icc a r,
      ‖F s - F q‖ ≤ H * |s - q| ^ theta)
    (hactual :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ q ∈ Set.Icc a r,
        wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U q) =
          weightedMovingHeatFullGeneratorCandidate eta c a
            (wholeLineRealL2Total
              (paper5WeightedPopulation eta (coMovingPath c u) U a)) F q)
    (hclose :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ q ∈ Set.Ioo a r, Integrable (fun x =>
        Real.exp (2 * eta * x) *
          |coMovingPath c u q x - U x| ^ 2))
    (hWx2 :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ q ∈ Set.Ioo a r, Integrable (fun x =>
        paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hXrep :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ q ∈ Set.Ioo a r,
        (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hFrep :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
      ∀ q ∈ Set.Ioo a r,
        (((F q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V q)) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
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
  dsimp only at hactual hclose hWx2 hXrep hFrep ⊢
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  obtain ⟨hsol, hu, hu2, hv2, _hWjoint, _hWmeas, _hFmeas, hpoint⟩ :=
    wholeLineCauchyBUCMildFixedPoint_positive_window_pointwise_data
      p hM hT ha (show a ≤ r from (hat.trans htr).le) hrT
        u₀ hsmall hstrip hTW hreg
  exact paper5WeightedEnergy_regularInputs_of_realized_candidate_window
    p ha hat htr hrT htheta hH hK hsol hTW
      (hreg.U_contDiff_two hTW) (hreg.V_contDiff_two hTW)
      hXcont hFcont hFbound hFholder hactual
      (fun q hq x => (hu q ⟨hq.1.le, hq.2.le⟩ x).1)
      (fun q hq => hu2 q ⟨hq.1.le, hq.2.le⟩)
      (fun q hq => hv2 q ⟨hq.1.le, hq.2.le⟩)
      hclose hWx2 hXrep hFrep
      (fun q hq x => hpoint q ⟨hq.1.le, hq.2.le⟩ x)

/-- The canonical mild fixed point supplies the four regularity inputs of
the exact weighted-energy identity at every positive interior time.  All
Hilbert trajectories, their moduli, and the physical generator restart are
constructed on an automatically selected compact window around the target
time. -/
theorem wholeLineCauchyBUCMildFixedPoint_weightedEnergy_regularInputs_natural
    (p : CMParams)
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
    (hchi : p.χ ≠ 0)
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
  dsimp only
  obtain ⟨L, a, r, R, hL0, hLa, hat, htr, hrR, hRT, hdiamOuter, _hshort⟩ :=
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
  obtain ⟨W, X, EW, EWx, HW, HWx, hEW, hEWx, hHW, hHWx,
      hWrep, hXrep, hWx2, hWnorm, hXnorm, hXcont, hWmod, hXmod⟩ :=
    htrajectory
  obtain ⟨hsol, huM, hu2, hv2, hWjoint, hWmeas, _hFmeas, _hpoint⟩ :=
    wholeLineCauchyBUCMildFixedPoint_positive_window_pointwise_data
      (eta := eta) (c := c) p hM hT ha0 har hrT
        u₀ hsmall hstrip hTW hreg
  have hMone : 1 ≤ M :=
    (MChi_ge_one_of_travelingWave hTW hbound).trans hMChi
  have hU2 : ContDiff ℝ 2 U := hreg.U_contDiff_two hTW
  have hV2 : ContDiff ℝ 2 V := hreg.V_contDiff_two hTW
  have hvEq : ∀ q ∈ Set.Icc a r,
      coMovingPath c v q = frozenElliptic p (coMovingPath c u q) := by
    intro q hq
    have hq0 : 0 ≤ q := ha0.le.trans hq.1
    let zq : Set.Icc (0 : ℝ) T :=
      ⟨q, hq0, hq.2.trans hrT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT Traj q = Traj zq :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zq.2
    have huC : IsCUnifBdd (u q) := by
      simpa only [u, hext] using WholeLineBUC.isCUnifBdd (Traj zq)
    have hu0 : ∀ x, 0 ≤ u q x := by
      intro x
      simpa only [u, hext, Traj] using (hstrip zq x).1
    change (fun x => frozenElliptic p (u q) (x + c * q)) =
      frozenElliptic p (fun x => u q (x + c * q))
    exact (frozenElliptic_comp_add_const_fun p huC hu0 (c * q)).symm
  obtain ⟨Hu, hHu, huHolderRaw⟩ :=
    exists_wholeLineCauchyBUCMildFixedPoint_coMoving_time_sqrt_holder_positive_window
      p c hM hT ha0 har hrT.le u₀ hsmall
        (theta := (1 / 2 : ℝ)) (zeta := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hstrip
  have huHolder : ∀ s ∈ Set.Icc a r, ∀ q ∈ Set.Icc a r, ∀ x,
      |coMovingPath c u s x - coMovingPath c u q x| ≤
        Hu * |s - q| ^ (1 / 2 : ℝ) := by
    intro s hs q hq x
    have hdist : |q - s| ≤ 1 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hs.1, hs.2, hq.1, hq.2, hdiam]
    simpa only [u, Traj, coMovingPath, abs_sub_comm] using
      huHolderRaw s hs q hq x hdist
  obtain ⟨Cf, hCf, hforcing⟩ :=
    exists_uniform_weightedGeneratorForcing_square_bound_mildFixedPoint_wave
      p hM hT ha0 har hrT hBlog heta heta_one hetaCap
        u₀ hsmall hstrip hchi hc hTW hbound hreg hMChi hlog hD hFD hB
        hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont hreact
        hreact_cont hgrad_int hdata_full
  let F : ℝ → WholeLineRealL2 :=
    paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
      p eta c u v U V har
  obtain ⟨H, hH, hFholder, hFcont, hFrep⟩ :=
    exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_data_of_population_H1_trajectories_and_classical_wave
      p har hdiam ha0 hrT hMone heta heta_one hsol hchi hc hTW hreg
        hbound hMChi hu2 hv2 hU2 hV2 huM hvEq hHu huHolder hBlog hlog
        (fun q hq => (hforcing q hq).1) hEW hEWx hHW hHWx hWrep hXrep
        hWnorm hXnorm hWmod hXmod
  let K : ℝ := Real.sqrt Cf
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hFbound : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K := by
    intro q hq
    have hnormsq :=
      wholeLineRealL2_norm_sq_eq_integral_sq_of_aeEq (F q) (hFrep q hq)
    have hsquare : ‖F q‖ ^ 2 ≤ K ^ 2 := by
      rw [hnormsq, show K ^ 2 = Cf by exact Real.sq_sqrt hCf]
      exact (hforcing q hq).2
    exact (sq_le_sq₀ (norm_nonneg _) hK).mp hsquare
  have hWsq : ∀ q ∈ Set.Icc a r, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U q x ^ 2) := by
    intro q hq
    exact integrable_sq_of_wholeLineRealL2_ae_eq (W q) (hWrep q hq)
  have hclose : ∀ q ∈ Set.Ioo a r, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u q x - U x| ^ 2) := by
    intro q hq
    refine (hWsq q ⟨hq.1.le, hq.2.le⟩).congr
      (Eventually.of_forall fun x => ?_)
    unfold paper5WeightedPopulation
    change (Real.exp (eta * x) * (coMovingPath c u q x - U x)) ^ 2 =
      Real.exp (2 * eta * x) * |coMovingPath c u q x - U x| ^ 2
    rw [mul_pow, sq_abs, pow_two, ← Real.exp_add]
    congr 1
    ring
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
    refine (hforcing q hq).1.congr (Eventually.of_forall fun x => ?_)
    simpa only [f, Traj, u, v] using
      congrArg (fun z : ℝ => z ^ 2) (hfactor q hq x).symm
  have hf_le : ∀ q ∈ Set.Icc a r, (∫ x : ℝ, f q x ^ 2) ≤ Cf := by
    intro q hq
    rw [show (∫ x : ℝ, f q x ^ 2) =
        ∫ x : ℝ, paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q x ^ 2 by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [f, Traj, u, v] using
        congrArg (fun z : ℝ => z ^ 2) (hfactor q hq x)]
    exact (hforcing q hq).2
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
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_regularInputs_of_realized_window
      p hM hT ha0 hat htr hrT (paper5ForcingTimeExponent_pos p) hH hK
        u₀ hsmall hstrip hTW hreg hXcont hFcont hFbound hFholder
        hactual hclose
        (fun q hq => hWx2 q ⟨hq.1.le, hq.2.le⟩)
        (fun q hq => hXrep q ⟨hq.1.le, hq.2.le⟩)
        (fun q hq => hFrep q ⟨hq.1.le, hq.2.le⟩)

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exists_wholeLineCauchyBUCMildFixedPoint_weighted_population_H1_trajectory_data
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_weightedEnergy_regularInputs_of_realized_window
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_weightedEnergy_regularInputs_natural
