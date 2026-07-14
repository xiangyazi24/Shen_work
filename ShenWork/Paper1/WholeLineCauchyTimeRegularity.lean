import ShenWork.Paper1.WholeLineCauchyPositivePDE

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time regularity of the whole-line Cauchy fixed point

The forward mild equation first gives the parabolic equation as a right
derivative.  This file proves the missing two-sided time regularity.  The
first step records positive-lag continuity of the spatial generator kernels
through the already established BUC heat cocycle, rather than by repeating
Gaussian dominated-convergence calculations.
-/

/-- Two successive positive-time BUC gradient heat operators are the spatial
Hessian of the heat flow at the sum of the two times. -/
theorem wholeLineCauchyHeatGradientBUCTotal_comp_apply_eq_hess
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineCauchyHeatGradientBUCTotal t
      (wholeLineCauchyHeatGradientBUCTotal s u)).1 x =
        wholeLineCauchyHeatHessOp (t + s) u.1 x := by
  let us : WholeLineBUC := wholeLineCauchyHeatBUCTotal s u
  let gs : WholeLineBUC := wholeLineCauchyHeatGradientBUCTotal s u
  have hus_apply : ∀ y, us.1 y = wholeLineCauchyHeatOp s u.1 y := by
    intro y
    simp [us, wholeLineCauchyHeatBUCTotal, hs,
      wholeLineCauchyHeatBUC_apply]
  have hgs_apply : ∀ y, gs.1 y = wholeLineCauchyHeatGradOp s u.1 y := by
    intro y
    simp [gs, wholeLineCauchyHeatGradientBUCTotal, hs,
      wholeLineCauchyHeatGradientBUC_apply]
  have hus_deriv : ∀ y, HasDerivAt us.1 (gs.1 y) y := by
    intro y
    have h := wholeLineCauchyHeatOp_hasDerivAt hs
      u.1.continuous.aestronglyMeasurable
      (fun z => by simpa [Real.norm_eq_abs] using u.1.norm_coe_le_norm z)
      (x := y)
    rw [show us.1 = fun z => wholeLineCauchyHeatOp s u.1 z by
      funext z; exact hus_apply z]
    simpa only [hgs_apply y] using h
  have hus_deriv_eq : deriv us.1 = gs.1 := by
    funext y
    exact (hus_deriv y).deriv
  have hgs_cont : Continuous gs.1 := gs.1.continuous
  have hgs_bound : ∀ y, |gs.1 y| ≤ ‖gs‖ := fun y =>
    WholeLineBUC.abs_apply_le_norm gs y
  have hheat_grad : ∀ y,
      wholeLineCauchyHeatGradOp t us.1 y =
        wholeLineCauchyHeatOp t gs.1 y := by
    intro y
    have h := wholeLineCauchyHeatGradOp_eq_heatOp_deriv ht
      (fun z => by simpa [Real.norm_eq_abs] using us.1.norm_coe_le_norm z)
      (fun z => by rw [hus_deriv_eq]; exact hgs_bound z)
      (fun z => (hus_deriv z).congr_deriv (hus_deriv z).deriv.symm)
      (by simpa [hus_deriv_eq] using hgs_cont) (x := y)
    simpa [hus_deriv_eq] using h
  have hsemigroup_fun :
      (fun y => wholeLineCauchyHeatOp t us.1 y) =
        fun y => wholeLineCauchyHeatOp (t + s) u.1 y := by
    funext y
    rw [show us.1 = fun z => wholeLineCauchyHeatOp s u.1 z by
      funext z; exact hus_apply z]
    exact wholeLineCauchyHeatOp_add_time ht hs u.1.continuous
      (fun z => by simpa [Real.norm_eq_abs] using u.1.norm_coe_le_norm z)
  have hleft : HasDerivAt
      (fun y => wholeLineCauchyHeatOp t gs.1 y)
      (wholeLineCauchyHeatGradOp t gs.1 x) x :=
    wholeLineCauchyHeatOp_hasDerivAt ht gs.1.continuous.aestronglyMeasurable
      hgs_bound
  have hright : HasDerivAt
      (fun y => wholeLineCauchyHeatGradOp (t + s) u.1 y)
      (wholeLineCauchyHeatHessOp (t + s) u.1 x) x :=
    wholeLineCauchyHeatGradOp_hasDerivAt (add_pos ht hs)
      u.1.continuous.aestronglyMeasurable
      (fun z => by simpa [Real.norm_eq_abs] using u.1.norm_coe_le_norm z)
  have hfun :
      (fun y => wholeLineCauchyHeatOp t gs.1 y) =
        fun y => wholeLineCauchyHeatGradOp (t + s) u.1 y := by
    funext y
    rw [← hheat_grad y]
    have hleftGrad := wholeLineCauchyHeatOp_hasDerivAt ht
      us.1.continuous.aestronglyMeasurable
      (fun z => by simpa [Real.norm_eq_abs] using us.1.norm_coe_le_norm z)
      (x := y)
    have hrightGrad := wholeLineCauchyHeatOp_hasDerivAt (add_pos ht hs)
      u.1.continuous.aestronglyMeasurable
      (fun z => by simpa [Real.norm_eq_abs] using u.1.norm_coe_le_norm z)
      (x := y)
    rw [hsemigroup_fun] at hleftGrad
    exact hleftGrad.unique hrightGrad
  have hleft' : HasDerivAt
      (fun y => wholeLineCauchyHeatGradOp (t + s) u.1 y)
      (wholeLineCauchyHeatGradOp t gs.1 x) x := by
    rw [← hfun]
    exact hleft
  have heq := hleft'.unique hright
  simpa [gs, wholeLineCauchyHeatGradientBUCTotal, ht, hs,
    wholeLineCauchyHeatGradientBUC_apply] using heq

/-- The Hessian heat operator is continuous in every strictly positive time.
The proof factors it into two positive-time BUC gradient operators. -/
theorem wholeLineCauchyHeatHessOp_time_continuousAt
    {t : ℝ} (ht : 0 < t) (u : WholeLineBUC) (x : ℝ) :
    ContinuousAt (fun q : ℝ => wholeLineCauchyHeatHessOp q u.1 x) t := by
  let inner : ℝ → WholeLineBUC := fun q =>
    wholeLineCauchyHeatGradientBUCTotal (q / 2) u
  have ht2 : 0 < t / 2 := by positivity
  have hhalf : ContinuousAt (fun q : ℝ => q / 2) t :=
    continuousAt_id.div_const (2 : ℝ)
  have hinner : ContinuousAt inner t := by
    exact (wholeLineCauchyHeatGradientBUCTotal_continuousAt_of_pos ht2 u).comp
      (f := fun q : ℝ => q / 2) hhalf
  have hpair : ContinuousAt (fun q : ℝ => (q / 2, inner q)) t :=
    hhalf.prodMk hinner
  have houter : ContinuousAt
      (fun q : ℝ => wholeLineCauchyHeatGradientBUCTotal (q / 2) (inner q)) t :=
    by
      have h :=
        (wholeLineCauchyHeatGradientBUCTotal_jointContinuousAt_of_pos
          ht2 (inner t)).comp
            (f := fun q : ℝ => (q / 2, inner q)) hpair
      simpa only [Function.comp_apply] using h
  have hevalMap : Continuous (fun w : WholeLineBUC => w.1 x) := by
    fun_prop
  have heval : ContinuousAt
      (fun q : ℝ =>
        (wholeLineCauchyHeatGradientBUCTotal (q / 2) (inner q)).1 x) t :=
    hevalMap.continuousAt.comp houter
  apply heval.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with q hq
  have hq2 : 0 < q / 2 := half_pos hq
  symm
  simpa [inner] using
    wholeLineCauchyHeatGradientBUCTotal_comp_apply_eq_hess
      hq2 hq2 u x

/-- A short Hessian Duhamel window is controlled by the integrable
`tau^(-1+theta/2)` cancellation bound. -/
theorem wholeLineCauchyHeatHess_recent_abs_le
    {F : ℝ → WholeLineBUC} {c q theta C H x : ℝ}
    (hcq : c < q) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hH : 0 ≤ H)
    (hFnorm : ∀ s y, |(F s).1 y| ≤ C)
    (hFholder : ∀ s ∈ Set.Icc c q, ∀ y z,
      |(F s).1 y - (F s).1 z| ≤ H * |y - z| ^ theta) :
    |∫ s in c..q,
        wholeLineCauchyHeatHessOp (q - s) (F s).1 x| ≤
      ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta *
        ((q - c) ^ (theta / 2 : ℝ) / (theta / 2)) * H := by
  let W : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let bound : ℝ → ℝ := fun s =>
    W * (q - s) ^ (-1 + theta / 2 : ℝ) * H
  have hW : 0 ≤ W := by
    dsimp [W]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hboundInt : IntervalIntegrable bound volume c q := by
    have hbase :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := q - c) htheta0
    have hshift : IntervalIntegrable
        (fun s : ℝ => (q - s) ^ (-1 + theta / 2 : ℝ))
        volume c q := by
      have h := hbase.comp_sub_right c
      convert h using 1 <;> ring_nf
    exact (hshift.const_mul W).mul_const H
  have hpoint : ∀ᵐ s ∂volume, s ∈ Set.Ioc c q →
      ‖wholeLineCauchyHeatHessOp (q - s) (F s).1 x‖ ≤ bound s := by
    filter_upwards [Measure.ae_ne volume q] with s hsq hs
    have hsqLt : s < q := lt_of_le_of_ne hs.2 hsq
    have hlag : 0 < q - s := sub_pos.mpr hsqLt
    have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
      hlag htheta0 htheta1 hH
      (F s).1.continuous.aestronglyMeasurable
      (hFnorm s) (hFholder s ⟨hs.1.le, hs.2⟩) (x := x)
    simpa [bound, W, Real.norm_eq_abs] using hcancel
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ s in c..q,
        wholeLineCauchyHeatHessOp (q - s) (F s).1 x‖ ≤
        ∫ s in c..q, bound s :=
      intervalIntegral.norm_integral_le_of_norm_le hcq.le hpoint hboundInt
    _ = W * ((q - c) ^ (theta / 2 : ℝ) / (theta / 2)) * H := by
      change (∫ s in c..q,
        W * (q - s) ^ (-1 + theta / 2 : ℝ) * H) = _
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_comp_sub_left
        (fun r : ℝ => r ^ (-1 + theta / 2 : ℝ)) q]
      simp only [sub_self]
      rw [integral_rpow (Or.inl (by linarith :
        (-1 : ℝ) < -1 + theta / 2))]
      have hne : (theta / 2 : ℝ) ≠ 0 := by linarith
      rw [show (-1 + theta / 2 : ℝ) + 1 = theta / 2 by ring,
        Real.zero_rpow hne, sub_zero]
    _ = ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta *
        ((q - c) ^ (theta / 2 : ℝ) / (theta / 2)) * H := rfl

/-- The reaction Hessian history depends continuously on every strictly
interior positive terminal time. -/
theorem wholeLineCauchyReactionHessianHistory_time_continuousAt_positive
    (p : CMParams) {M T theta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (x : ℝ) :
    ContinuousAt
      (fun q : ℝ => ∫ s in (0 : ℝ)..q,
        wholeLineCauchyHeatHessOp (q - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) t := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hbT : b ≤ T := by dsimp [b]; linarith
  have hRcont : Continuous R := by
    simpa [R] using wholeLineCauchyReactionSourceTrajectory_continuous
      p hM hT U
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  rcases exists_wholeLineCauchyReactionSourceTrajectory_window_Ctheta
      p hM hT ha hbT u₀ hsmall htheta0 htheta1 with
    ⟨HR, hHR, hRholder⟩
  let W : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let A : ℝ := W * (1 / (theta / 2)) * HR
  have hW : 0 ≤ W := by
    dsimp [W]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rw [Metric.continuousAt_iff]
  intro eps heps
  let dtail : ℝ := (eps / (12 * (A + 1))) ^ (2 / theta : ℝ)
  have hbase : 0 < eps / (12 * (A + 1)) := by positivity
  have hdtail : 0 < dtail := by dsimp [dtail]; positivity
  have hdtailpow : dtail ^ (theta / 2 : ℝ) =
      eps / (12 * (A + 1)) := by
    dsimp [dtail]
    rw [← Real.rpow_mul hbase.le]
    have hmul : (2 / theta : ℝ) * (theta / 2) = 1 := by
      field_simp [ne_of_gt htheta0]
    rw [hmul, Real.rpow_one]
  let d : ℝ := min ((t - a) / 2) (min ((b - t) / 2) (dtail / 2))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (lt_min (by linarith) (half_pos hdtail))
  let c : ℝ := t - d
  have hac : a < c := by
    dsimp [c]
    have hdle : d ≤ (t - a) / 2 := by dsimp [d]; exact min_le_left _ _
    linarith
  have hct : c < t := by dsimp [c]; linarith
  have hOld : ContinuousAt
      (fun q : ℝ => ∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatHessOp (q - s) (R s).1 x) t := by
    let Bold : ℝ :=
      (5 * Real.sqrt 2 / 2) * (d / 2) ^ (-(1 : ℝ)) * MR
    apply intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ : ℝ => Bold)
    · filter_upwards with q
      exact (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable
        hRcont q x).restrict
    · filter_upwards [Ioi_mem_nhds (show t - d / 2 < t by linarith)]
        with q hq
      filter_upwards [Measure.ae_ne volume c] with s hsc hs
      rw [Set.uIoc_of_le (ha.le.trans hac.le)] at hs
      change t - d / 2 < q at hq
      have hscLt : s < c := lt_of_le_of_ne hs.2 hsc
      have hlagLower : d / 2 ≤ q - s := by
        dsimp [c] at hscLt
        linarith
      have hlag : 0 < q - s := lt_of_lt_of_le (half_pos hd) hlagLower
      have hpow : (q - s) ^ (-(1 : ℝ)) ≤ (d / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (half_pos hd) hlagLower (by norm_num)
      have hraw := wholeLineCauchyHeatHessOp_abs_le
        hlag hMR (R s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (R s) y).trans (hRnorm s))
        (x := x)
      rw [Real.norm_eq_abs]
      exact hraw.trans (by dsimp [Bold]; gcongr)
    · exact intervalIntegrable_const
    · filter_upwards with s hs
      rw [Set.uIoc_of_le (ha.le.trans hac.le)] at hs
      have hlag : 0 < t - s := sub_pos.mpr (hs.2.trans_lt hct)
      exact (wholeLineCauchyHeatHessOp_time_continuousAt
        hlag (R s) x).comp (f := fun q : ℝ => q - s) (by fun_prop)
  rw [Metric.continuousAt_iff] at hOld
  obtain ⟨dold, hdold, hOldClose⟩ := hOld (eps / 2) (by linarith)
  refine ⟨min d dold, lt_min hd hdold, ?_⟩
  intro q hq
  rw [Real.dist_eq] at hq ⊢
  have hqd : |q - t| < d := hq.trans_le (min_le_left _ _)
  have hqold : |q - t| < dold := hq.trans_le (min_le_right _ _)
  have hqa : a < q := by
    have hdle : d ≤ (t - a) / 2 := by dsimp [d]; exact min_le_left _ _
    have hneg := neg_abs_le (q - t)
    linarith
  have hqb : q < b := by
    have hdle : d ≤ (b - t) / 2 := by
      dsimp [d]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hpos := le_abs_self (q - t)
    linarith
  have hcq : c < q := by
    dsimp [c]
    have hneg := neg_abs_le (q - t)
    linarith
  have hlen : q - c < dtail := by
    have hdle : d ≤ dtail / 2 := by
      dsimp [d]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hpos := le_abs_self (q - t)
    dsimp [c]
    linarith
  have hqT : q < T := hqb.trans_le hbT
  have hIntq := wholeLineCauchyReactionHessianHistory_intervalIntegrable_positive
    p hM hT u₀ hsmall (ha.trans hqa) hqT htheta0 htheta1 x
  have hIntt := wholeLineCauchyReactionHessianHistory_intervalIntegrable_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1 x
  have hTailBound : ∀ {r : ℝ}, c < r → r < b → r - c < dtail →
      |∫ s in c..r, wholeLineCauchyHeatHessOp (r - s) (R s).1 x| <
        eps / 12 := by
    intro r hcr hrb hrlen
    have hrpos : 0 < r := ha.trans (hac.trans hcr)
    have hrT : r < T := hrb.trans_le hbT
    have hrecent := wholeLineCauchyHeatHess_recent_abs_le
      (F := R) (x := x) hcr htheta0 htheta1 hHR
      (fun s y => (WholeLineBUC.abs_apply_le_norm (R s) y).trans (hRnorm s))
      (fun s hs y z => hRholder s
        ⟨hac.le.trans hs.1, hs.2.trans hrb.le⟩ y z)
    have hrpow : (r - c) ^ (theta / 2 : ℝ) <
        eps / (12 * (A + 1)) := by
      calc
        (r - c) ^ (theta / 2 : ℝ) <
            dtail ^ (theta / 2 : ℝ) :=
          Real.rpow_lt_rpow (sub_nonneg.mpr hcr.le) hrlen (by positivity)
        _ = eps / (12 * (A + 1)) := hdtailpow
    have hAstep : A * (r - c) ^ (theta / 2 : ℝ) < eps / 12 := by
      have hle : A * (r - c) ^ (theta / 2 : ℝ) ≤
          A * (eps / (12 * (A + 1))) :=
        mul_le_mul_of_nonneg_left hrpow.le hA
      have hstrict : A * (eps / (12 * (A + 1))) < eps / 12 := by
        have hfrac : A / (A + 1) < 1 := by
          rw [div_lt_one (by positivity : 0 < A + 1)]
          linarith
        calc
          A * (eps / (12 * (A + 1))) =
              (A / (A + 1)) * (eps / 12) := by field_simp
          _ < 1 * (eps / 12) :=
            mul_lt_mul_of_pos_right hfrac (by positivity)
          _ = eps / 12 := one_mul _
      exact hle.trans_lt hstrict
    exact hrecent.trans_lt (by
      simpa [A, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hAstep)
  have htailq := hTailBound hcq hqb hlen
  have htailt : |∫ s in c..t,
      wholeLineCauchyHeatHessOp (t - s) (R s).1 x| < eps / 12 := by
    apply hTailBound hct htb
    dsimp [c]
    have hdle : d ≤ dtail / 2 := by
      dsimp [d]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have holdClose : abs (
      (∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatHessOp (q - s) (R s).1 x) -
      (∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatHessOp (t - s) (R s).1 x)) < eps / 2 := by
    simpa [Real.dist_eq] using hOldClose hqold
  have hsplitq :
      (∫ s in (0 : ℝ)..q,
        wholeLineCauchyHeatHessOp (q - s) (R s).1 x) =
      (∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatHessOp (q - s) (R s).1 x) +
      (∫ s in c..q,
        wholeLineCauchyHeatHessOp (q - s) (R s).1 x) := by
    have hc0 : 0 ≤ c := ha.le.trans hac.le
    have hq0 : 0 ≤ q := (ha.trans hqa).le
    have h0c : IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatHessOp (q - s) (R s).1 x)
        volume 0 c := by
      apply hIntq.mono_set
      rw [Set.uIcc_of_le hc0, Set.uIcc_of_le hq0]
      exact Set.Icc_subset_Icc_right hcq.le
    have hcqi : IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatHessOp (q - s) (R s).1 x)
        volume c q := by
      apply hIntq.mono_set
      rw [Set.uIcc_of_le hcq.le, Set.uIcc_of_le hq0]
      exact Set.Icc_subset_Icc_left hc0
    exact (intervalIntegral.integral_add_adjacent_intervals h0c hcqi).symm
  have hsplitt :
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (R s).1 x) =
      (∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatHessOp (t - s) (R s).1 x) +
      (∫ s in c..t,
        wholeLineCauchyHeatHessOp (t - s) (R s).1 x) := by
    have hc0 : 0 ≤ c := ha.le.trans hac.le
    have h0c : IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (R s).1 x)
        volume 0 c := by
      apply hIntt.mono_set
      rw [Set.uIcc_of_le hc0, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc_right hct.le
    have hcti : IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (R s).1 x)
        volume c t := by
      apply hIntt.mono_set
      rw [Set.uIcc_of_le hct.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc_left hc0
    exact (intervalIntegral.integral_add_adjacent_intervals h0c hcti).symm
  rw [hsplitq, hsplitt]
  calc
    |((∫ s in (0 : ℝ)..c,
          wholeLineCauchyHeatHessOp (q - s) (R s).1 x) +
        ∫ s in c..q, wholeLineCauchyHeatHessOp (q - s) (R s).1 x) -
      ((∫ s in (0 : ℝ)..c,
          wholeLineCauchyHeatHessOp (t - s) (R s).1 x) +
        ∫ s in c..t, wholeLineCauchyHeatHessOp (t - s) (R s).1 x)| ≤
        |(∫ s in (0 : ℝ)..c,
            wholeLineCauchyHeatHessOp (q - s) (R s).1 x) -
          (∫ s in (0 : ℝ)..c,
            wholeLineCauchyHeatHessOp (t - s) (R s).1 x)| +
        |∫ s in c..q,
          wholeLineCauchyHeatHessOp (q - s) (R s).1 x| +
        |∫ s in c..t,
          wholeLineCauchyHeatHessOp (t - s) (R s).1 x| := by
      calc
        |_ - _| = |((∫ s in (0 : ℝ)..c,
              wholeLineCauchyHeatHessOp (q - s) (R s).1 x) -
            (∫ s in (0 : ℝ)..c,
              wholeLineCauchyHeatHessOp (t - s) (R s).1 x)) +
            ((∫ s in c..q,
              wholeLineCauchyHeatHessOp (q - s) (R s).1 x) -
            (∫ s in c..t,
              wholeLineCauchyHeatHessOp (t - s) (R s).1 x))| := by ring_nf
        _ ≤ _ := by
          have hadd := abs_add_le
            ((∫ s in (0 : ℝ)..c,
                wholeLineCauchyHeatHessOp (q - s) (R s).1 x) -
              (∫ s in (0 : ℝ)..c,
                wholeLineCauchyHeatHessOp (t - s) (R s).1 x))
            ((∫ s in c..q,
                wholeLineCauchyHeatHessOp (q - s) (R s).1 x) -
              (∫ s in c..t,
                wholeLineCauchyHeatHessOp (t - s) (R s).1 x))
          have hsub := abs_sub
            (∫ s in c..q,
              wholeLineCauchyHeatHessOp (q - s) (R s).1 x)
            (∫ s in c..t,
              wholeLineCauchyHeatHessOp (t - s) (R s).1 x)
          linarith
    _ < eps / 2 + eps / 12 + eps / 12 := by linarith
    _ < eps := by linarith

/-- The short chemotaxis generator window has the same integrable Hessian
singularity after spatial integration by parts onto the physical flux. -/
theorem wholeLineCauchyFluxThird_recent_abs_le_positive
    (p : CMParams) {M T c q rho HFd x : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hc : 0 < c) (hcq : c < q) (hqT : q < T)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (hHFd : 0 ≤ HFd)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (hFdHolder : ∀ s ∈ Set.Icc c q, ∀ y z,
      |deriv
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 y -
        deriv
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 z| ≤
        HFd * |y - z| ^ rho) :
    |∫ s in c..q,
      wholeLineCauchyHeatThirdOp (q - s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| ≤
      ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst rho *
        ((q - c) ^ (rho / 2 : ℝ) / (rho / 2)) * HFd := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  let DF : ℝ := HFd + 2 * MF
  let W : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst rho
  let bound : ℝ → ℝ := fun s =>
    W * (q - s) ^ (-1 + rho / 2 : ℝ) * HFd
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hDF : 0 ≤ DF := by dsimp [DF]; positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg rho
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hboundInt : IntervalIntegrable bound volume c q := by
    have hbase :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := q - c) hrho0
    have hshift : IntervalIntegrable
        (fun s : ℝ => (q - s) ^ (-1 + rho / 2 : ℝ)) volume c q := by
      have h := hbase.comp_sub_right c
      convert h using 1 <;> ring_nf
    exact (hshift.const_mul W).mul_const HFd
  have hpoint : ∀ᵐ s ∂volume, s ∈ Set.Ioc c q →
      ‖wholeLineCauchyHeatThirdOp (q - s) (F s).1 x‖ ≤ bound s := by
    filter_upwards [Measure.ae_ne volume q] with s hsq hs
    have hsqLt : s < q := lt_of_le_of_ne hs.2 hsq
    have hspos : 0 < s := hc.trans hs.1
    have hlag : 0 < q - s := sub_pos.mpr hsqLt
    let zs : Set.Icc (0 : ℝ) T :=
      ⟨s, hspos.le, hsqLt.le.trans hqT.le⟩
    have hFdDeriv : ∀ y, HasDerivAt (F s).1 (deriv (F s).1 y) y := by
      intro y
      have h := wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
        p hM hT u₀ hsmall zs hspos (hstrip zs) y
      simpa [F, U] using h.differentiableAt.hasDerivAt
    have hFdHold : ∀ y z,
        |deriv (F s).1 y - deriv (F s).1 z| ≤
          HFd * |y - z| ^ rho := by
      intro y z
      simpa [F, U] using hFdHolder s ⟨hs.1.le, hs.2⟩ y z
    have hFdCont : Continuous (deriv (F s).1) :=
      wholeLineContinuous_of_holder hrho0 hHFd hFdHold
    have hFbound : ∀ y, |(F s).1 y| ≤ MF := fun y =>
      (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
    have hFdBound : ∀ y, |deriv (F s).1 y| ≤ DF := by
      intro y
      exact deriv_abs_le_of_bounded_of_deriv_holder
        hHFd hrho0 hFbound
        (fun z => (hFdDeriv z).differentiableAt) hFdHold y
    have hthirdEq := wholeLineCauchyHeatThirdOp_eq_hessOp_deriv
      (f := (F s).1) (x := x) hlag hFbound hFdBound hFdDeriv hFdCont
    have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
      hlag hrho0 hrho1 hHFd hFdCont.aestronglyMeasurable
      hFdBound hFdHold (x := x)
    rw [Real.norm_eq_abs, hthirdEq]
    simpa [bound, W] using hcancel
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ s in c..q, wholeLineCauchyHeatThirdOp (q - s) (F s).1 x‖ ≤
        ∫ s in c..q, bound s :=
      intervalIntegral.norm_integral_le_of_norm_le hcq.le hpoint hboundInt
    _ = W * ((q - c) ^ (rho / 2 : ℝ) / (rho / 2)) * HFd := by
      change (∫ s in c..q,
        W * (q - s) ^ (-1 + rho / 2 : ℝ) * HFd) = _
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_comp_sub_left
        (fun r : ℝ => r ^ (-1 + rho / 2 : ℝ)) q]
      simp only [sub_self]
      rw [integral_rpow (Or.inl (by linarith :
        (-1 : ℝ) < -1 + rho / 2))]
      have hne : (rho / 2 : ℝ) ≠ 0 := by linarith
      rw [show (-1 + rho / 2 : ℝ) + 1 = rho / 2 by ring,
        Real.zero_rpow hne, sub_zero]
    _ = ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst rho *
        ((q - c) ^ (rho / 2 : ℝ) / (rho / 2)) * HFd := rfl

-- The old/recent dominated-convergence decomposition below elaborates a
-- large dependent expression before the kernel cancellations become visible.
set_option maxHeartbeats 800000 in
/-- The chemotaxis third-kernel history depends continuously on every
strictly interior positive terminal time. -/
theorem wholeLineCauchyFluxThirdHistory_time_continuousAt_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    ContinuousAt
      (fun q : ℝ => ∫ s in (0 : ℝ)..q,
        wholeLineCauchyHeatThirdOp (q - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) t := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hab : a ≤ b := hat.le.trans htb.le
  have hbT : b ≤ T := by dsimp [b]; linarith
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hstripWindow : ∀ s ∈ Set.Icc a b, ∀ y,
      (wholeLineBUCTrajectoryExtend hT U s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨ha.le.trans hs.1, hs.2.trans hbT⟩
    rw [wholeLineBUCTrajectoryExtend_eq hT U hsT]
    exact hstrip ⟨s, hsT⟩ y
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel hstripWindow with
    ⟨rho, HFd, hrho0, hrho1, hHFd, hFdHolder⟩
  let W : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst rho
  let A : ℝ := W * (1 / (rho / 2)) * HFd
  have hW : 0 ≤ W := by
    dsimp [W]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg rho
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rw [Metric.continuousAt_iff]
  intro eps heps
  let dtail : ℝ := (eps / (12 * (A + 1))) ^ (2 / rho : ℝ)
  have hbase : 0 < eps / (12 * (A + 1)) := by positivity
  have hdtail : 0 < dtail := by dsimp [dtail]; positivity
  have hdtailpow : dtail ^ (rho / 2 : ℝ) =
      eps / (12 * (A + 1)) := by
    dsimp [dtail]
    rw [← Real.rpow_mul hbase.le]
    have hmul : (2 / rho : ℝ) * (rho / 2) = 1 := by
      field_simp [ne_of_gt hrho0]
    rw [hmul, Real.rpow_one]
  let d : ℝ := min ((t - a) / 2) (min ((b - t) / 2) (dtail / 2))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (lt_min (by linarith) (half_pos hdtail))
  let c : ℝ := t - d
  have hac : a < c := by
    dsimp [c]
    have hdle : d ≤ (t - a) / 2 := by dsimp [d]; exact min_le_left _ _
    linarith
  have hct : c < t := by dsimp [c]; linarith
  have hc0 : 0 < c := ha.trans hac
  have hOld : ContinuousAt
      (fun q : ℝ => ∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) t := by
    let C3 : ℝ := heatThirdTailConstant
    let Bold : ℝ := C3 * (d / 2) ^ (-(3 / 2 : ℝ)) * MF
    have hC3 : 0 ≤ C3 := by
      dsimp [C3]
      exact heatThirdTailConstant_nonneg
    apply intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun _ : ℝ => Bold)
    · filter_upwards with q
      exact (wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable
        hFcont q x).restrict
    · filter_upwards [Ioi_mem_nhds (show t - d / 2 < t by linarith)]
        with q hq
      filter_upwards [Measure.ae_ne volume c] with s hsc hs
      rw [Set.uIoc_of_le hc0.le] at hs
      change t - d / 2 < q at hq
      have hscLt : s < c := lt_of_le_of_ne hs.2 hsc
      have hlagLower : d / 2 ≤ q - s := by
        dsimp [c] at hscLt
        linarith
      have hlag : 0 < q - s := lt_of_lt_of_le (half_pos hd) hlagLower
      have hpow : (q - s) ^ (-(3 / 2 : ℝ)) ≤
          (d / 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (half_pos hd) hlagLower (by norm_num)
      have hraw := wholeLineCauchyHeatThirdOp_abs_le
        hlag hMF (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s))
        (x := x)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| ≤
            (C3 / ((q - s) * Real.sqrt (q - s))) * MF := by
          simpa [C3] using hraw
        _ = C3 * (q - s) ^ (-(3 / 2 : ℝ)) * MF := by
          rw [div_eq_mul_inv, ← one_div,
            one_div_mul_sqrt_eq_rpow_neg_three_half hlag]
        _ ≤ Bold := by dsimp [Bold]; gcongr
    · exact intervalIntegrable_const
    · filter_upwards with s hs
      rw [Set.uIoc_of_le hc0.le] at hs
      have hspos : 0 < s := hs.1
      have hsT : s < T := hs.2.trans_lt (hct.trans htT)
      let zs : Set.Icc (0 : ℝ) T := ⟨s, hspos.le, hsT.le⟩
      let Ds : WholeLineBUC :=
        wholeLineCauchyFluxDerivativeBUCPositive p hM hT u₀ hsmall zs hspos
          htheta0 htheta1 heta0 heta1 hrel (hstrip zs)
      rcases wholeLineCauchyFluxSourceTrajectory_restartC1Data_positive
          p hM hT u₀ hsmall zs hspos htheta0 htheta1
            heta0 heta1 hrel (hstrip zs) with
        ⟨hhas, hcont, D, hDbound⟩
      have hFbound : ∀ y, |(F s).1 y| ≤ MF := fun y =>
        (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
      have hDsApply : ∀ y, Ds.1 y = deriv (F s).1 y := by
        intro y
        simp [Ds, F, U, zs]
      have htime := (wholeLineCauchyHeatHessOp_time_continuousAt
        (sub_pos.mpr (hs.2.trans_lt hct)) Ds x).comp
          (f := fun q : ℝ => q - s) (by fun_prop)
      apply htime.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds (hs.2.trans_lt hct)] with q hsq
      have hlag : 0 < q - s := sub_pos.mpr hsq
      have hthirdEq := wholeLineCauchyHeatThirdOp_eq_hessOp_deriv
        (f := (F s).1) (x := x) hlag hFbound hDbound hhas hcont
      rw [hthirdEq]
      congr 2
  rw [Metric.continuousAt_iff] at hOld
  obtain ⟨dold, hdold, hOldClose⟩ := hOld (eps / 2) (by linarith)
  refine ⟨min d dold, lt_min hd hdold, ?_⟩
  intro q hq
  rw [Real.dist_eq] at hq ⊢
  have hqd : |q - t| < d := hq.trans_le (min_le_left _ _)
  have hqold : |q - t| < dold := hq.trans_le (min_le_right _ _)
  have hqa : a < q := by
    have hdle : d ≤ (t - a) / 2 := by dsimp [d]; exact min_le_left _ _
    have hneg := neg_abs_le (q - t)
    linarith
  have hqb : q < b := by
    have hdle : d ≤ (b - t) / 2 := by
      dsimp [d]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hpos := le_abs_self (q - t)
    linarith
  have hcq : c < q := by
    dsimp [c]
    have hneg := neg_abs_le (q - t)
    linarith
  have hlen : q - c < dtail := by
    have hdle : d ≤ dtail / 2 := by
      dsimp [d]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hpos := le_abs_self (q - t)
    dsimp [c]
    linarith
  have hqT : q < T := hqb.trans_le hbT
  have hIntq := wholeLineCauchyFluxThirdHistory_intervalIntegrable_positive
    p hM hT u₀ hsmall (ha.trans hqa) hqT htheta0 htheta1
      heta0 heta1 hrel hstrip x
  have hIntt := wholeLineCauchyFluxThirdHistory_intervalIntegrable_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1
      heta0 heta1 hrel hstrip x
  have hTailBound : ∀ {r : ℝ}, c < r → r < b → r - c < dtail →
      |∫ s in c..r, wholeLineCauchyHeatThirdOp (r - s) (F s).1 x| <
        eps / 12 := by
    intro r hcr hrb hrlen
    have hrecent := wholeLineCauchyFluxThird_recent_abs_le_positive
      p hM hT u₀ hsmall hc0 hcr (hrb.trans_le hbT)
        hrho0 hrho1 hHFd hstrip
        (fun s hs y z => by
          simpa [F, U] using hFdHolder s
            ⟨hac.le.trans hs.1, hs.2.trans hrb.le⟩ y z)
        (x := x)
    have hrpow : (r - c) ^ (rho / 2 : ℝ) <
        eps / (12 * (A + 1)) := by
      calc
        (r - c) ^ (rho / 2 : ℝ) < dtail ^ (rho / 2 : ℝ) :=
          Real.rpow_lt_rpow (sub_nonneg.mpr hcr.le) hrlen (by positivity)
        _ = eps / (12 * (A + 1)) := hdtailpow
    have hAstep : A * (r - c) ^ (rho / 2 : ℝ) < eps / 12 := by
      have hle : A * (r - c) ^ (rho / 2 : ℝ) ≤
          A * (eps / (12 * (A + 1))) :=
        mul_le_mul_of_nonneg_left hrpow.le hA
      have hstrict : A * (eps / (12 * (A + 1))) < eps / 12 := by
        have hfrac : A / (A + 1) < 1 := by
          rw [div_lt_one (by positivity : 0 < A + 1)]
          linarith
        calc
          A * (eps / (12 * (A + 1))) =
              (A / (A + 1)) * (eps / 12) := by field_simp
          _ < 1 * (eps / 12) :=
            mul_lt_mul_of_pos_right hfrac (by positivity)
          _ = eps / 12 := one_mul _
      exact hle.trans_lt hstrict
    exact hrecent.trans_lt (by
      simpa [A, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hAstep)
  have htailq := hTailBound hcq hqb hlen
  have htailt : |∫ s in c..t,
      wholeLineCauchyHeatThirdOp (t - s) (F s).1 x| < eps / 12 := by
    apply hTailBound hct htb
    dsimp [c]
    have hdle : d ≤ dtail / 2 := by
      dsimp [d]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have holdClose : abs (
      (∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) -
      (∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)) < eps / 2 := by
    simpa [Real.dist_eq] using hOldClose hqold
  have hsplitq :
      (∫ s in (0 : ℝ)..q,
        wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) =
      (∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) +
      (∫ s in c..q,
        wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) := by
    have h0c : IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatThirdOp (q - s) (F s).1 x)
        volume 0 c := by
      apply hIntq.mono_set
      rw [Set.uIcc_of_le hc0.le, Set.uIcc_of_le (ha.trans hqa).le]
      exact Set.Icc_subset_Icc_right hcq.le
    have hcqi : IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatThirdOp (q - s) (F s).1 x)
        volume c q := by
      apply hIntq.mono_set
      rw [Set.uIcc_of_le hcq.le, Set.uIcc_of_le (ha.trans hqa).le]
      exact Set.Icc_subset_Icc_left hc0.le
    exact (intervalIntegral.integral_add_adjacent_intervals h0c hcqi).symm
  have hsplitt :
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) =
      (∫ s in (0 : ℝ)..c,
        wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) +
      (∫ s in c..t,
        wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) := by
    have h0c : IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)
        volume 0 c := by
      apply hIntt.mono_set
      rw [Set.uIcc_of_le hc0.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc_right hct.le
    have hcti : IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)
        volume c t := by
      apply hIntt.mono_set
      rw [Set.uIcc_of_le hct.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc_left hc0.le
    exact (intervalIntegral.integral_add_adjacent_intervals h0c hcti).symm
  rw [hsplitq, hsplitt]
  calc
    |((∫ s in (0 : ℝ)..c,
          wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) +
        ∫ s in c..q, wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) -
      ((∫ s in (0 : ℝ)..c,
          wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) +
        ∫ s in c..t, wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)| ≤
        |(∫ s in (0 : ℝ)..c,
            wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) -
          (∫ s in (0 : ℝ)..c,
            wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)| +
        |∫ s in c..q,
          wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| +
        |∫ s in c..t,
          wholeLineCauchyHeatThirdOp (t - s) (F s).1 x| := by
      have hadd := abs_add_le
        ((∫ s in (0 : ℝ)..c,
            wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) -
          (∫ s in (0 : ℝ)..c,
            wholeLineCauchyHeatThirdOp (t - s) (F s).1 x))
        ((∫ s in c..q,
            wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) -
          (∫ s in c..t,
            wholeLineCauchyHeatThirdOp (t - s) (F s).1 x))
      have hsub := abs_sub
        (∫ s in c..q, wholeLineCauchyHeatThirdOp (q - s) (F s).1 x)
        (∫ s in c..t, wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)
      convert hadd.trans (add_le_add le_rfl hsub) using 1 <;> ring_nf
    _ < eps / 2 + eps / 12 + eps / 12 := by linarith
    _ < eps := by linarith

/-- The second spatial derivative of the canonical fixed point is continuous
in time at every strictly interior positive point. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_second_time_continuousAt_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    ContinuousAt
      (fun q : ℝ => deriv
        (fun xi : ℝ => deriv
          (fun w : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 w) xi) x) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT U
  let formula : ℝ → ℝ := fun q =>
    wholeLineCauchyHeatHessOp q u₀.1 x +
      (-p.χ) * (∫ s in (0 : ℝ)..q,
        wholeLineCauchyHeatThirdOp (q - s) (F s).1 x) +
      (∫ s in (0 : ℝ)..q,
        wholeLineCauchyHeatHessOp (q - s) (R s).1 x)
  have hformula : ContinuousAt formula t := by
    have hheat := wholeLineCauchyHeatHessOp_time_continuousAt ht u₀ x
    have hflux := wholeLineCauchyFluxThirdHistory_time_continuousAt_positive
      p hM hT u₀ hsmall ht htT htheta0 htheta1
        heta0 heta1 hrel hstrip x
    have hreac :=
      wholeLineCauchyReactionHessianHistory_time_continuousAt_positive
        p hM hT u₀ hsmall ht htT htheta0 htheta1 x
    simpa [formula, F, R, U] using (hheat.add (hflux.const_mul (-p.χ))).add hreac
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with q hq
  let zq : Set.Icc (0 : ℝ) T := ⟨q, hq.1.le, hq.2.le⟩
  have hext : wholeLineBUCTrajectoryExtend hT U q = U zq :=
    wholeLineBUCTrajectoryExtend_eq hT U zq.2
  have hstripWindow : ∀ s ∈ Set.Icc (q / 2) q, ∀ y,
      (wholeLineBUCTrajectoryExtend hT U s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    have hs0 : 0 ≤ s := (half_pos hq.1).le.trans hs.1
    have hsT : s ≤ T := hs.2.trans hq.2.le
    have hexts := wholeLineBUCTrajectoryExtend_eq hT U
      (show s ∈ Set.Icc (0 : ℝ) T from ⟨hs0, hsT⟩)
    rw [hexts]
    exact hstrip ⟨s, hs0, hsT⟩ y
  have hspace :=
    (wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
      p hM hT u₀ hsmall zq hq.1 htheta0 htheta1
        heta0 heta1 hrel hstripWindow x).deriv
  rw [hext]
  simpa [formula, U, F, R, zq] using hspace

/-- A continuous function with a continuous right derivative on an open
interval has the ordinary derivative there.  The proof compares it with the
integral primitive by the right-derivative fencing theorem. -/
theorem hasDerivAt_of_continuous_right_derivative_on_Icc
    {f D : ℝ → ℝ} {a b t : ℝ} {o : Set ℝ}
    (hat : a < t) (htb : t < b)
    (hfcont : ContinuousOn f (Set.Icc a b))
    (ho : IsOpen o) (hsub : Set.Icc a b ⊆ o)
    (hDcont : ∀ q ∈ o, ContinuousAt D q)
    (hright : ∀ q ∈ Set.Ico a b,
      HasDerivWithinAt f (D q) (Set.Ici q) q) :
    HasDerivAt f (D t) t := by
  have hab : a < b := hat.trans htb
  have hDcontOn : ContinuousOn D (Set.Icc a b) := fun q hq =>
    (hDcont q (hsub hq)).continuousWithinAt
  have hDint : IntegrableOn D (Set.Icc a b) volume :=
    hDcontOn.integrableOn_Icc
  let g : ℝ → ℝ := fun q => f a + ∫ r in a..q, D r
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    have hprim := intervalIntegral.continuousOn_primitive hDint
    have hprim' : ContinuousOn (fun q => ∫ r in a..q, D r)
        (Set.Icc a b) := by
      apply hprim.congr
      intro q hq
      change (∫ r in a..q, D r) = ∫ r in Set.Ioc a q, D r
      exact intervalIntegral.integral_of_le hq.1
    exact continuousOn_const.add hprim'
  have hgderiv : ∀ q ∈ Set.Ico a b, HasDerivAt g (D q) q := by
    intro q hq
    have hqIcc : q ∈ Set.Icc a b := ⟨hq.1, hq.2.le⟩
    have hDintaq : IntervalIntegrable D volume a q := by
      apply (hDcontOn.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hq.1]
      exact Set.Icc_subset_Icc_right hq.2.le
    have hstrong : StronglyMeasurableAtFilter D (nhds q) volume :=
      ContinuousAt.stronglyMeasurableAtFilter ho hDcont q (hsub hqIcc)
    have hprim := intervalIntegral.integral_hasDerivAt_right
      hDintaq hstrong (hDcont q (hsub hqIcc))
    simpa [g] using hprim.const_add (f a)
  have hfg : ∀ q ∈ Set.Icc a b, f q = g q := by
    apply eq_of_has_deriv_right_eq hright
      (fun q hq => (hgderiv q hq).hasDerivWithinAt)
      hfcont hgcont
    simp [g]
  have hgt := hgderiv t ⟨hat.le, htb⟩
  apply hgt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hat htb] with q hq
  exact hfg q ⟨hq.1.le, hq.2.le⟩

/-- The spatial derivative of the physical flux is continuous in time at
every strictly interior positive point. -/
theorem wholeLineCauchyFluxSourceTrajectory_deriv_time_continuousAt_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    ContinuousAt
      (fun q : ℝ => deriv
        (wholeLineCauchyFluxSourceTrajectory p hM hT U q).1 x) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
  have huniform :=
    wholeLineCauchyFluxSourceTrajectory_deriv_uniformContinuousAt_positive
      p hM hT u₀ hsmall zt ht htT htheta0 htheta1
        heta0 heta1 hrel hstrip
  rw [Metric.continuousAt_iff]
  intro eps heps
  rcases huniform eps heps with ⟨delta, hdelta, hclose⟩
  refine ⟨delta, hdelta, ?_⟩
  intro q hq
  rw [Real.dist_eq] at hq ⊢
  simpa [U, zt] using hclose q hq x

/-- The generator expression appearing in the forward mild equation is
continuous at every strictly interior positive time. -/
theorem wholeLineCauchyBUCMildFixedPoint_generator_time_continuousAt_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
    let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
    ContinuousAt
      (fun q : ℝ =>
        deriv (fun xi : ℝ => deriv
          (fun w : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 w) xi) x -
        (wholeLineBUCTrajectoryExtend hT U q).1 x +
        (-p.χ) * deriv (F q).1 x + (R q).1 x) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT U
  have hspace :=
    wholeLineCauchyBUCMildFixedPoint_spatial_second_time_continuousAt_positive
      p hM hT u₀ hsmall ht htT htheta0 htheta1
        heta0 heta1 hrel hstrip x
  have hevalMap : Continuous (fun w : WholeLineBUC => w.1 x) := by fun_prop
  have hu : ContinuousAt
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x) t :=
    hevalMap.continuousAt.comp
      (f := wholeLineBUCTrajectoryExtend hT U)
      (wholeLineBUCTrajectoryExtend_continuous hT U).continuousAt
  have hflux :=
    wholeLineCauchyFluxSourceTrajectory_deriv_time_continuousAt_positive
      p hM hT u₀ hsmall ht htT htheta0 htheta1
        heta0 heta1 hrel hstrip x
  have hreac : ContinuousAt (fun q : ℝ => (R q).1 x) t :=
    hevalMap.continuousAt.comp (f := R)
      (by simpa [R] using
        (wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U).continuousAt)
  simpa [U, F, R] using
    ((hspace.sub hu).add (hflux.const_mul (-p.χ))).add hreac

/-- The canonical fixed point has an ordinary time derivative at every
strictly interior positive point, equal to the mild generator expression. -/
theorem wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let F := wholeLineCauchyFluxSourceTrajectory p hM hT U
    let R := wholeLineCauchyReactionSourceTrajectory p hM hT U
    HasDerivAt
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x)
      (deriv (fun xi : ℝ => deriv
          (fun w : ℝ => (wholeLineBUCTrajectoryExtend hT U t).1 w) xi) x -
        (wholeLineBUCTrajectoryExtend hT U t).1 x +
        (-p.χ) * deriv (F t).1 x + (R t).1 x) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT U
  let f : ℝ → ℝ := fun q =>
    (wholeLineBUCTrajectoryExtend hT U q).1 x
  let D : ℝ → ℝ := fun q =>
    deriv (fun xi : ℝ => deriv
      (fun w : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 w) xi) x -
      (wholeLineBUCTrajectoryExtend hT U q).1 x +
      (-p.χ) * deriv (F q).1 x + (R q).1 x
  let a : ℝ := t / 2
  let b : ℝ := (t + T) / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hat : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hbT : b < T := by dsimp [b]; linarith
  have hfcont : Continuous f := by
    have hevalMap : Continuous (fun w : WholeLineBUC => w.1 x) := by fun_prop
    exact hevalMap.comp (wholeLineBUCTrajectoryExtend_continuous hT U)
  have hDcont : ∀ q ∈ Set.Ioo (0 : ℝ) T, ContinuousAt D q := by
    intro q hq
    simpa [D, U, F, R] using
      (wholeLineCauchyBUCMildFixedPoint_generator_time_continuousAt_positive
        p hM hT u₀ hsmall hq.1 hq.2 htheta0 htheta1
          heta0 heta1 hrel hstrip x)
  have hright : ∀ q ∈ Set.Ico a b,
      HasDerivWithinAt f (D q) (Set.Ici q) q := by
    intro q hq
    have hq0 : 0 < q := ha.trans_le hq.1
    have hqT : q < T := hq.2.trans hbT
    let zq : Set.Icc (0 : ℝ) T := ⟨q, hq0.le, hqT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT U q = U zq :=
      wholeLineBUCTrajectoryExtend_eq hT U zq.2
    have hpde := wholeLineCauchyBUCMildFixedPoint_right_generator_pde
      p hM hT u₀ hsmall hq0 hqT htheta0 htheta1
        heta0 heta1 hrel hstrip x
    have hpde' : HasDerivWithinAt f (D q)
        (Set.Icc q (min (q + 1) T)) q := by
      simpa [f, D, U, F, R, zq, hext] using hpde
    have hupper : q < min (q + 1) T := lt_min (by linarith) hqT
    exact hpde'.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hupper)
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T := by
    intro q hq
    exact ⟨ha.trans_le hq.1, hq.2.trans_lt hbT⟩
  simpa [f, D, U, F, R] using
    (hasDerivAt_of_continuous_right_derivative_on_Icc
      hat htb hfcont.continuousOn isOpen_Ioo hsub hDcont hright)

/-- On the physical strip, the canonical fixed point satisfies the original
parabolic equation with an ordinary two-sided time derivative. -/
theorem wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
    (p : CMParams) {M T theta eta t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (htT : t < T)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M)
    (x : ℝ) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
    HasDerivAt
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x)
      (deriv (fun xi : ℝ => deriv (fun w : ℝ => (U zt).1 w) xi) x -
        p.χ * deriv (wholeLineChemotaxisFlux p (U zt).1) x +
        wholeLineLogisticSource p (U zt).1 x) t := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT U
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
  have htime := wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
    p hM hT u₀ hsmall ht htT htheta0 htheta1
      heta0 heta1 hrel hstrip x
  change HasDerivAt
    (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x)
    (deriv (fun xi : ℝ => deriv
        (fun w : ℝ => (wholeLineBUCTrajectoryExtend hT U t).1 w) xi) x -
      (wholeLineBUCTrajectoryExtend hT U t).1 x +
      (-p.χ) * deriv (F t).1 x + (R t).1 x) t at htime
  have hext : wholeLineBUCTrajectoryExtend hT U t = U zt :=
    wholeLineBUCTrajectoryExtend_eq hT U zt.2
  have hfluxEq : (F t).1 = wholeLineChemotaxisFlux p (U zt).1 := by
    funext y
    simpa [F, wholeLineCauchyFluxSourceTrajectory, hext] using congrFun
      (wholeLineCauchyTruncatedFlux_eq_of_mem_Icc p hM (hstrip zt)) y
  have hreactionEq : (R t).1 = wholeLineCauchyShiftedReaction p (U zt).1 := by
    funext y
    simpa [R, wholeLineCauchyReactionSourceTrajectory, hext] using congrFun
      (wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hM (hstrip zt)) y
  rw [hext, hfluxEq, hreactionEq] at htime
  convert htime using 1
  simp only [wholeLineCauchyShiftedReaction]
  ring

section WholeLineCauchyTimeRegularityAxiomAudit

#print axioms wholeLineCauchyHeatGradientBUCTotal_comp_apply_eq_hess
#print axioms wholeLineCauchyHeatHessOp_time_continuousAt
#print axioms wholeLineCauchyHeatHess_recent_abs_le
#print axioms
  wholeLineCauchyReactionHessianHistory_time_continuousAt_positive
#print axioms wholeLineCauchyFluxThird_recent_abs_le_positive
#print axioms wholeLineCauchyFluxThirdHistory_time_continuousAt_positive
#print axioms
  wholeLineCauchyBUCMildFixedPoint_spatial_second_time_continuousAt_positive
#print axioms hasDerivAt_of_continuous_right_derivative_on_Icc
#print axioms
  wholeLineCauchyFluxSourceTrajectory_deriv_time_continuousAt_positive
#print axioms
  wholeLineCauchyBUCMildFixedPoint_generator_time_continuousAt_positive
#print axioms wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
#print axioms wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt

end WholeLineCauchyTimeRegularityAxiomAudit

end ShenWork.Paper1
