import ShenWork.Paper1.WholeLineCauchyC2Bootstrap
import ShenWork.Paper1.WholeLineCauchyGlobalGluing
import ShenWork.Paper1.Theorem12CoordinateAudit

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time `C²` slices for the whole-line weighted-energy argument

The pointwise positive-time bootstrap already differentiates a canonical mild
slice twice.  This file supplies the missing continuity of the second spatial
derivative, packages the result as `ContDiff ℝ 2`, and transports it through
the canonical global gluing and the co-moving spatial translation.
-/

/-- For a bounded continuous source, the third Gaussian convolution is a
continuous function of the spatial observation point. -/
theorem wholeLineCauchyHeatThirdOp_continuous
    {t : ℝ} (ht : 0 < t) (f : WholeLineBUC) :
    Continuous (wholeLineCauchyHeatThirdOp t f.1) := by
  let K : ℝ → ℝ := fun z =>
    deriv
      (fun q : ℝ => deriv
        (fun r : ℝ => deriv (fun w : ℝ => heatKernel t w) r) q) z
  have hKcont : Continuous K := by
    simpa [K] using continuous_thirdDeriv_heatKernel ht
  have hKint : Integrable K volume := by
    exact (integrable_norm_iff hKcont.aestronglyMeasurable).1 (by
      simpa [K, Real.norm_eq_abs] using
        thirdDeriv_heatKernel_abs_integrable ht)
  have hconv : Continuous (kernelConvVal K f) :=
    kernelConvVal_continuous hKcont hKint f
  have heq : wholeLineCauchyHeatThirdOp t f.1 =
      fun x => Real.exp (-t) * kernelConvVal K f x := by
    funext x
    simp only [wholeLineCauchyHeatThirdOp, kernelConvVal, K]
  rw [heq]
  exact continuous_const.mul hconv

/-- A local-in-space dominated-convergence wrapper for a fixed time interval.
The analytic estimates below naturally give their majorant on one unit ball
around each observation point, which is exactly what continuity requires. -/
theorem intervalIntegral_continuous_of_local_spatial_dominated
    {F : ℝ → ℝ → ℝ} {t : ℝ} (ht : 0 < t)
    (hF_meas : ∀ x,
      AEStronglyMeasurable (F x) (volume.restrict <| Set.uIoc 0 t))
    (hF_cont : ∀ s, 0 < s → s < t → Continuous (fun x => F x s))
    (hlocal : ∀ x, ∃ bound : ℝ → ℝ,
      IntervalIntegrable bound volume 0 t ∧
      ∀ s, 0 ≤ s → s < t → ∀ q ∈ Metric.ball x 1,
        ‖F q s‖ ≤ bound s) :
    Continuous (fun x => ∫ s in (0 : ℝ)..t, F x s) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨bound, hboundInt, hbound⟩ := hlocal x
  apply intervalIntegral.continuousAt_of_dominated_interval
      (bound := bound)
  · filter_upwards with q
    simpa [Set.uIoc_of_le ht.le] using hF_meas q
  · filter_upwards [Metric.ball_mem_nhds x one_pos] with q hqx
    filter_upwards [Measure.ae_ne volume t] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    exact hbound s hs.1.le (lt_of_le_of_ne hs.2 hst) q hqx
  · exact hboundInt
  · filter_upwards [Measure.ae_ne volume t] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    exact (hF_cont s hs.1 (lt_of_le_of_ne hs.2 hst)).continuousAt

/-- Continuity of the Hessian Duhamel coefficient under the same recent-time
spatial Hölder hypothesis used by the pointwise second-derivative theorem. -/
theorem wholeLineCauchyValueHistory_secondCoeff_continuous_of_window_Ctheta
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t C theta H : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hFnorm : ∀ s, ‖F s‖ ≤ C) (hH : 0 ≤ H)
    (hholder : ∀ s ∈ Set.Icc (t / 2) t, ∀ y w : ℝ,
      |(F s).1 y - (F s).1 w| ≤ H * |y - w| ^ theta) :
    Continuous (fun x => ∫ s in (0 : ℝ)..t,
      wholeLineCauchyHeatHessOp (t - s) (F s).1 x) := by
  apply intervalIntegral_continuous_of_local_spatial_dominated ht
  · intro x
    exact (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable
      hF t x).restrict
  · intro s _hs hst
    have hlag : 0 < t - s := sub_pos.mpr hst
    rw [continuous_iff_continuousAt]
    intro x
    exact (wholeLineCauchyHeatHessOp_hasDerivAt hlag
      (F s).1.continuous.aestronglyMeasurable
      (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
        (hFnorm s))).continuousAt
  · intro x
    have hhalf : 0 < t / 2 := by positivity
    let Cearly : ℝ :=
      (5 * Real.sqrt 2 / 2) * (t / 2) ^ (-(1 : ℝ)) * C
    let Wtheta : ℝ :=
      ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
    let bound : ℝ → ℝ := fun s =>
      Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * H
    have hCearly : 0 ≤ Cearly := by dsimp [Cearly]; positivity
    have hWtheta : 0 ≤ Wtheta := by
      dsimp [Wtheta]
      exact
        ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
    have hboundInt : IntervalIntegrable bound volume 0 t := by
      have hk :=
        ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
          (t := t) htheta0
      have hscaled := (hk.const_mul Wtheta).mul_const H
      have hconst : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
        intervalIntegrable_const
      simpa [bound, mul_assoc] using hconst.add hscaled
    refine ⟨bound, hboundInt, ?_⟩
    intro s hs0 hst q _hq
    have hlag : 0 < t - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ t / 2
    · have hlagHalf : t / 2 ≤ t - s := by linarith
      have hpow : (t - s) ^ (-(1 : ℝ)) ≤
          (t / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hglobal := wholeLineCauchyHeatHessOp_abs_le
        hlag hC (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
          (hFnorm s)) (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (t - s) (F s).1 q| ≤
            ((5 * Real.sqrt 2 / 2) * (t - s) ^ (-(1 : ℝ))) * C :=
          hglobal
        _ ≤ Cearly := by
          dsimp [Cearly]
          gcongr
        _ ≤ bound s := by
          dsimp [bound]
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hWtheta
              (Real.rpow_nonneg hlag.le _)) hH)
    · have hsWindow : s ∈ Set.Icc (t / 2) t :=
        ⟨le_of_not_ge hsHalf, hst.le⟩
      have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
        hlag htheta0 htheta1 hH
        (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
          (hFnorm s))
        (hholder s hsWindow) (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (t - s) (F s).1 q| ≤
            Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * H := by
          simpa [Wtheta] using hcancel
        _ ≤ bound s := by
          dsimp [bound]
          linarith

/-- The third-kernel chemotaxis history is spatially continuous at every
positive target time.  The early half-window uses the global third-Gaussian
bound; on the recent half-window one derivative is transferred to the common
Hölder-continuous flux derivative. -/
theorem wholeLineCauchyFluxThirdHistory_continuous_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ s ∈ Set.Icc (z.1 / 2) z.1, ∀ x,
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x ∈
          Set.Icc (0 : ℝ) M) :
    Continuous (fun x => ∫ s in (0 : ℝ)..z.1,
      wholeLineCauchyHeatThirdOp (z.1 - s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hhalf : 0 < z.1 / 2 := by positivity
  have hhalfLe : z.1 / 2 ≤ z.1 := by linarith
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT hhalf hhalfLe z.2.2 u₀ hsmall
        htheta0 htheta1 heta0 heta1 hrel hstrip with
    ⟨rho, HFd, hrho0, hrho1, hHFd, hFdHolder⟩
  let DF : ℝ := HFd + 2 * MF
  have hDF : 0 ≤ DF := by dsimp [DF]; positivity
  let C3 : ℝ := heatThirdTailConstant
  let Cearly : ℝ := C3 * (z.1 / 2) ^ (-(3 / 2 : ℝ)) * MF
  let Wrho : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst rho
  let bound : ℝ → ℝ := fun s =>
    Cearly + Wrho * (z.1 - s) ^ (-1 + rho / 2 : ℝ) * HFd
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    exact heatThirdTailConstant_nonneg
  have hCearly : 0 ≤ Cearly := by dsimp [Cearly]; positivity
  have hWrho : 0 ≤ Wrho := by
    dsimp [Wrho]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg rho
  have hboundInt : IntervalIntegrable bound volume 0 z.1 := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := z.1) hrho0
    have hscaled := (hk.const_mul Wrho).mul_const HFd
    have hconst : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 z.1 :=
      intervalIntegrable_const
    simpa [bound, mul_assoc] using hconst.add hscaled
  apply intervalIntegral_continuous_of_local_spatial_dominated hz
  · intro x
    exact (wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable
      hFcont z.1 x).restrict
  · intro s _hs hst
    exact wholeLineCauchyHeatThirdOp_continuous (sub_pos.mpr hst) (F s)
  · intro x
    refine ⟨bound, hboundInt, ?_⟩
    intro s hs0 hst q _hq
    have hlag : 0 < z.1 - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ z.1 / 2
    · have hlagHalf : z.1 / 2 ≤ z.1 - s := by linarith
      have hpow : (z.1 - s) ^ (-(3 / 2 : ℝ)) ≤
          (z.1 / 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hraw := wholeLineCauchyHeatThirdOp_abs_le
        hlag hMF (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
          (hFnorm s)) (x := q)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatThirdOp (z.1 - s) (F s).1 q| ≤
            (C3 / ((z.1 - s) * Real.sqrt (z.1 - s))) * MF := by
          simpa [C3] using hraw
        _ = C3 * (z.1 - s) ^ (-(3 / 2 : ℝ)) * MF := by
          rw [div_eq_mul_inv, ← one_div,
            one_div_mul_sqrt_eq_rpow_neg_three_half hlag]
        _ ≤ Cearly := by
          dsimp [Cearly]
          gcongr
        _ ≤ bound s := by
          dsimp [bound]
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg hWrho
              (Real.rpow_nonneg hlag.le _)) hHFd)
    · have hsWindow : s ∈ Set.Icc (z.1 / 2) z.1 :=
        ⟨le_of_not_ge hsHalf, hst.le⟩
      have hspos : 0 < s := hhalf.trans_le hsWindow.1
      let zs : Set.Icc (0 : ℝ) T :=
        ⟨s, hspos.le, hst.le.trans z.2.2⟩
      have hext : wholeLineBUCTrajectoryExtend hT U s = U zs :=
        wholeLineBUCTrajectoryExtend_eq hT U zs.2
      have hsStrip : ∀ y, (U zs).1 y ∈ Set.Icc (0 : ℝ) M := by
        intro y
        rw [← hext]
        exact hstrip s hsWindow y
      have hFdDeriv : ∀ y,
          HasDerivAt (F s).1 (deriv (F s).1 y) y := by
        intro y
        have h := wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
          p hM hT u₀ hsmall zs hspos hsStrip y
        simpa [F, U] using h.differentiableAt.hasDerivAt
      have hFdHold : ∀ y w,
          |deriv (F s).1 y - deriv (F s).1 w| ≤
            HFd * |y - w| ^ rho := by
        intro y w
        simpa [F, U] using hFdHolder s hsWindow y w
      have hFdCont : Continuous (deriv (F s).1) :=
        wholeLineContinuous_of_holder hrho0 hHFd hFdHold
      have hFbound : ∀ y, |(F s).1 y| ≤ MF := by
        intro y
        exact (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
      have hFdBound : ∀ y, |deriv (F s).1 y| ≤ DF := by
        intro y
        exact deriv_abs_le_of_bounded_of_deriv_holder
          hHFd hrho0 hFbound
          (fun w => (hFdDeriv w).differentiableAt) hFdHold y
      have hthirdEq := wholeLineCauchyHeatThirdOp_eq_hessOp_deriv
        (f := (F s).1) (x := q) hlag hFbound hFdBound hFdDeriv hFdCont
      have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
        hlag hrho0 hrho1 hHFd hFdCont.aestronglyMeasurable
        hFdBound hFdHold (x := q)
      rw [Real.norm_eq_abs, hthirdEq]
      calc
        |wholeLineCauchyHeatHessOp (z.1 - s) (deriv (F s).1) q| ≤
            Wrho * (z.1 - s) ^ (-1 + rho / 2 : ℝ) * HFd := by
          simpa [Wrho] using hcancel
        _ ≤ bound s := by
          dsimp [bound]
          linarith

/-- The reaction Hessian history is spatially continuous at every positive
target time. -/
theorem wholeLineCauchyReactionHessianHistory_continuous_positive
    (p : CMParams) {M T theta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    Continuous (fun x => ∫ s in (0 : ℝ)..z.1,
      wholeLineCauchyHeatHessOp (z.1 - s)
        (wholeLineCauchyReactionSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hRcont : Continuous R := by
    simpa [R] using wholeLineCauchyReactionSourceTrajectory_continuous
      p hM hT U
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hhalf : 0 < z.1 / 2 := by positivity
  rcases exists_wholeLineCauchyReactionSourceTrajectory_window_Ctheta
      p hM hT hhalf z.2.2 u₀ hsmall htheta0 htheta1 with
    ⟨HR, hHR, hRholder⟩
  change Continuous (fun x => ∫ s in (0 : ℝ)..z.1,
    wholeLineCauchyHeatHessOp (z.1 - s) (R s).1 x)
  exact wholeLineCauchyValueHistory_secondCoeff_continuous_of_window_Ctheta
    hRcont hz hMR htheta0 htheta1 hRnorm hHR hRholder

/-- The second spatial derivative of a positive canonical mild slice is a
continuous function of space. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_second_continuous_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ s ∈ Set.Icc (z.1 / 2) z.1, ∀ x,
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x ∈
          Set.Icc (0 : ℝ) M) :
    Continuous (fun x => deriv (fun y => deriv
      (fun w =>
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w) y) x) := by
  let fluxCoeff : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..z.1,
    wholeLineCauchyHeatThirdOp (z.1 - s)
      (wholeLineCauchyFluxSourceTrajectory p hM hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x
  let reactionCoeff : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..z.1,
    wholeLineCauchyHeatHessOp (z.1 - s)
      (wholeLineCauchyReactionSourceTrajectory p hM hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x
  have hheat : Continuous (wholeLineCauchyHeatHessOp z.1 u₀.1) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (wholeLineCauchyHeatHessOp_hasDerivAt hz
      u₀.1.continuous.aestronglyMeasurable
      (fun y => WholeLineBUC.abs_apply_le_norm u₀ y)).continuousAt
  have hflux : Continuous fluxCoeff := by
    simpa [fluxCoeff] using
      wholeLineCauchyFluxThirdHistory_continuous_positive
        p hM hT u₀ hsmall z hz htheta0 htheta1
          heta0 heta1 hrel hstrip
  have hreaction : Continuous reactionCoeff := by
    simpa [reactionCoeff] using
      wholeLineCauchyReactionHessianHistory_continuous_positive
        p hM hT u₀ hsmall z hz htheta0 htheta1
  have hcoeff : Continuous (fun x =>
      wholeLineCauchyHeatHessOp z.1 u₀.1 x +
        (-p.χ) * fluxCoeff x + reactionCoeff x) :=
    (hheat.add (continuous_const.mul hflux)).add hreaction
  have heq :
      (fun x => deriv (fun y => deriv
        (fun w =>
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w) y) x) =
      fun x => wholeLineCauchyHeatHessOp z.1 u₀.1 x +
        (-p.χ) * fluxCoeff x + reactionCoeff x := by
    funext x
    simpa [fluxCoeff, reactionCoeff] using
      (wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
        p hM hT u₀ hsmall z hz htheta0 htheta1
          heta0 heta1 hrel hstrip x).deriv
  rw [heq]
  exact hcoeff

/-- Every positive canonical mild slice is `C²` in the spatial variable. -/
theorem wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ s ∈ Set.Icc (z.1 / 2) z.1, ∀ x,
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x ∈
          Set.Icc (0 : ℝ) M) :
    ContDiff ℝ 2
      (fun x =>
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x) := by
  let f : ℝ → ℝ := fun x =>
    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x
  have hf : Differentiable ℝ f := by
    intro x
    exact (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
      p hM hT u₀ hsmall z hz x).differentiableAt
  have hdf : Differentiable ℝ (deriv f) := by
    intro x
    exact (wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
      p hM hT u₀ hsmall z hz htheta0 htheta1
        heta0 heta1 hrel hstrip x).differentiableAt
  have hdd : Continuous (deriv (deriv f)) := by
    simpa [f] using
      wholeLineCauchyBUCMildFixedPoint_spatial_second_continuous_positive
        p hM hT u₀ hsmall z hz htheta0 htheta1
          heta0 heta1 hrel hstrip
  change ContDiff ℝ 2 f
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiff_succ_iff_deriv]
  exact ⟨hf, by simp, contDiff_one_iff_deriv.2 ⟨hdf, hdd⟩⟩

/-- Every positive slice of the canonically glued whole-line Cauchy solution
is `C²` in space. -/
theorem wholeLineCauchyGlobalU_slice_contDiff_two_positive
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 2 (wholeLineCauchyGlobalU p u₀ t) := by
  let n : ℕ := wholeLineCauchyGlobalIndex p u₀ t
  let H : ℝ := wholeLineCauchyGlobalSegmentTime p u₀
  let q : ℝ := wholeLineCauchyGlobalLocalTime p u₀ t
  have hq0 : 0 < q := by
    simpa [q] using wholeLineCauchyGlobalLocalTime_pos p u₀ ht
  have hqH : q < H := by
    simpa [q, H] using
      wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le
  let z : Set.Icc (0 : ℝ) H := ⟨q, hq0.le, hqH.le⟩
  have hsegmentStrip : ∀ w : Set.Icc (0 : ℝ) H, ∀ x,
      (wholeLineCauchyGlobalSegment p u₀ n w).1 x ∈
        Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀) := by
    simpa [n, H] using
      (wholeLineCauchyGlobalDatum_segment_bounds
        p hregime u₀ hu₀ n).2.1
  have hwindow : ∀ s ∈ Set.Icc (z.1 / 2) z.1, ∀ x,
      (wholeLineBUCTrajectoryExtend
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalSegment p u₀ n) s).1 x ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀) := by
    intro s hs x
    have hsH : s ∈ Set.Icc (0 : ℝ) H := by
      constructor
      · have : 0 < z.1 / 2 := by simpa [z, q] using half_pos hq0
        exact this.le.trans hs.1
      · exact hs.2.trans z.2.2
    have hext := wholeLineBUCTrajectoryExtend_eq
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalSegment p u₀ n) hsH
    rw [hext]
    exact hsegmentStrip ⟨s, hsH⟩ x
  have hlocal : ContDiff ℝ 2
      (fun x => (wholeLineCauchyGlobalSegment p u₀ n z).1 x) := by
    simpa [wholeLineCauchyGlobalSegment, H, z, q, n] using
      (wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
        (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ)) p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalDatum p u₀ n)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        z hq0
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hwindow)
  have hslice : wholeLineCauchyGlobalU p u₀ t =
      fun x => (wholeLineCauchyGlobalSegment p u₀ n z).1 x := by
    funext x
    have hEq := congrArg (fun w : WholeLineBUC => w.1 x)
      (wholeLineCauchyGlobalBUC_eq_segment p u₀ ht.le)
    simpa [wholeLineCauchyGlobalU, n, H, q, z] using hEq
  rw [hslice]
  exact hlocal

/-- The positive-time canonical global solution is spatially `C²` in every
co-moving frame.  This is the `hu2` producer consumed by the weighted-energy
identity. -/
theorem wholeLineCauchyGlobalU_coMoving_contDiff_two_positive
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {c t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 2 (coMovingPath c (wholeLineCauchyGlobalU p u₀) t) := by
  have hslice := wholeLineCauchyGlobalU_slice_contDiff_two_positive
    p hregime u₀ hu₀ ht
  simpa [coMovingPath] using ContDiff.two_shift hslice (c * t)

#print axioms wholeLineCauchyHeatThirdOp_continuous
#print axioms intervalIntegral_continuous_of_local_spatial_dominated
#print axioms
  wholeLineCauchyValueHistory_secondCoeff_continuous_of_window_Ctheta
#print axioms wholeLineCauchyFluxThirdHistory_continuous_positive
#print axioms
  wholeLineCauchyReactionHessianHistory_continuous_positive
#print axioms
  wholeLineCauchyBUCMildFixedPoint_spatial_second_continuous_positive
#print axioms
  wholeLineCauchyBUCMildFixedPoint_slice_contDiff_two_positive
#print axioms wholeLineCauchyGlobalU_slice_contDiff_two_positive
#print axioms wholeLineCauchyGlobalU_coMoving_contDiff_two_positive

end ShenWork.Paper1
