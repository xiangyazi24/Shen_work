import ShenWork.Paper1.WholeLineWeightedRegularitySlice
import ShenWork.Paper1.WholeLineCauchyTimeRegularity

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Uniform spatial bounds for positive-time canonical second derivatives

The positive-time `C²` bootstrap identifies the second derivative pointwise.
This file records the complementary uniform-in-space estimates furnished by
the very same early/recent Gaussian majorants.  These estimates are unweighted
and do not use any weighted `H¹` conclusion.
-/

/-- The Hessian Duhamel coefficient is uniformly bounded in space under the
recent-window Hölder hypothesis used by the positive-time `C²` bootstrap. -/
theorem wholeLineCauchyValueHistory_secondCoeff_bounded_of_window_Ctheta
    {F : ℝ → WholeLineBUC}
    {t C theta H : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hFnorm : ∀ s, ‖F s‖ ≤ C) (hH : 0 ≤ H)
    (hholder : ∀ s ∈ Set.Icc (t / 2) t, ∀ y w : ℝ,
      |(F s).1 y - (F s).1 w| ≤ H * |y - w| ^ theta) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (F s).1 x| ≤ B := by
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
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hboundInt : IntervalIntegrable bound volume 0 t := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0
    have hscaled := (hk.const_mul Wtheta).mul_const H
    have hconst : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    simpa [bound, mul_assoc] using hconst.add hscaled
  let B : ℝ := ∫ s in (0 : ℝ)..t, bound s
  have hbound_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ bound s := by
    intro s hs
    dsimp [bound]
    exact add_nonneg hCearly
      (mul_nonneg (mul_nonneg hWtheta
        (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)) hH)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact intervalIntegral.integral_nonneg ht.le hbound_nonneg
  refine ⟨B, hB, ?_⟩
  intro x
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le ht.le _ hboundInt
  filter_upwards with s
  intro hs
  rcases lt_or_eq_of_le hs.2 with hst | rfl
  · have hlag : 0 < t - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ t / 2
    · have hlagHalf : t / 2 ≤ t - s := by linarith
      have hpow : (t - s) ^ (-(1 : ℝ)) ≤
          (t / 2) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hglobal := wholeLineCauchyHeatHessOp_abs_le
        hlag hC (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
          (hFnorm s)) (x := x)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (t - s) (F s).1 x| ≤
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
        (hholder s hsWindow) (x := x)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatHessOp (t - s) (F s).1 x| ≤
            Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * H := by
          simpa [Wtheta] using hcancel
        _ ≤ bound s := by
          dsimp [bound]
          linarith
  · simp only [sub_self,
        wholeLineCauchyHeatHessOp_eq_zero_of_nonpos le_rfl, norm_zero]
    exact hbound_nonneg _ ⟨ht.le, le_rfl⟩

/-- At a fixed positive canonical time, the chemotaxis third-kernel history
has a bound independent of the spatial observation point. -/
theorem wholeLineCauchyFluxThirdHistory_bounded_positive
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
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |∫ s in (0 : ℝ)..z.1,
        wholeLineCauchyHeatThirdOp (z.1 - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| ≤ B := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
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
  have hbound_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) z.1, 0 ≤ bound s := by
    intro s hs
    dsimp [bound]
    exact add_nonneg hCearly
      (mul_nonneg (mul_nonneg hWrho
        (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)) hHFd)
  let B : ℝ := ∫ s in (0 : ℝ)..z.1, bound s
  have hB : 0 ≤ B := by
    dsimp [B]
    exact intervalIntegral.integral_nonneg hz.le hbound_nonneg
  refine ⟨B, hB, ?_⟩
  intro x
  change |∫ s in (0 : ℝ)..z.1,
    wholeLineCauchyHeatThirdOp (z.1 - s) (F s).1 x| ≤ B
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le hz.le _ hboundInt
  filter_upwards with s
  intro hs
  rcases lt_or_eq_of_le hs.2 with hst | rfl
  · have hlag : 0 < z.1 - s := sub_pos.mpr hst
    by_cases hsHalf : s ≤ z.1 / 2
    · have hlagHalf : z.1 / 2 ≤ z.1 - s := by linarith
      have hpow : (z.1 - s) ^ (-(3 / 2 : ℝ)) ≤
          (z.1 / 2) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hhalf hlagHalf (by norm_num)
      have hraw := wholeLineCauchyHeatThirdOp_abs_le
        hlag hMF (F s).1.continuous.aestronglyMeasurable
        (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
          (hFnorm s)) (x := x)
      rw [Real.norm_eq_abs]
      calc
        |wholeLineCauchyHeatThirdOp (z.1 - s) (F s).1 x| ≤
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
        (f := (F s).1) (x := x) hlag hFbound hFdBound hFdDeriv hFdCont
      have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
        hlag hrho0 hrho1 hHFd hFdCont.aestronglyMeasurable
        hFdBound hFdHold (x := x)
      rw [Real.norm_eq_abs, hthirdEq]
      calc
        |wholeLineCauchyHeatHessOp (z.1 - s) (deriv (F s).1) x| ≤
            Wrho * (z.1 - s) ^ (-1 + rho / 2 : ℝ) * HFd := by
          simpa [Wrho] using hcancel
        _ ≤ bound s := by
          dsimp [bound]
          linarith
  · simp only [sub_self,
        wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos le_rfl, norm_zero]
    exact hbound_nonneg _ ⟨hz.le, le_rfl⟩

/-- At a fixed positive canonical time, the reaction Hessian history has a
bound independent of the spatial observation point. -/
theorem wholeLineCauchyReactionHessianHistory_bounded_positive
    (p : CMParams) {M T theta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |∫ s in (0 : ℝ)..z.1,
        wholeLineCauchyHeatHessOp (z.1 - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| ≤ B := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have hhalf : 0 < z.1 / 2 := by positivity
  rcases exists_wholeLineCauchyReactionSourceTrajectory_window_Ctheta
      p hM hT hhalf z.2.2 u₀ hsmall htheta0 htheta1 with
    ⟨HR, hHR, hRholder⟩
  change ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
    |∫ s in (0 : ℝ)..z.1,
      wholeLineCauchyHeatHessOp (z.1 - s) (R s).1 x| ≤ B
  exact wholeLineCauchyValueHistory_secondCoeff_bounded_of_window_Ctheta
    hz hMR htheta0 htheta1 hRnorm hHR hRholder

/-- A positive-time heat Hessian of bounded BUC data is uniformly bounded in
the observation point. -/
theorem wholeLineCauchyHeatHessOp_bounded_positive
    {t : ℝ} (ht : 0 < t) (f : WholeLineBUC) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |wholeLineCauchyHeatHessOp t f.1 x| ≤ B := by
  let B : ℝ := (5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ)) * ‖f‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro x
  exact wholeLineCauchyHeatHessOp_abs_le ht (norm_nonneg f)
    f.1.continuous.aestronglyMeasurable
    (fun y => WholeLineBUC.abs_apply_le_norm f y) (x := x)

/-- Every fixed positive canonical mild slice has a spatial second derivative
with one global-in-space bound.  The proof consumes only the population strip
and the unweighted Gaussian/Hölder estimates from the `C²` bootstrap. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_second_bounded_positive
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
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |deriv (fun y : ℝ => deriv
        (fun w : ℝ =>
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 w) y) x| ≤ B := by
  rcases wholeLineCauchyHeatHessOp_bounded_positive hz u₀ with
    ⟨Bheat, hBheat, hheat⟩
  rcases wholeLineCauchyFluxThirdHistory_bounded_positive
      p hM hT u₀ hsmall z hz htheta0 htheta1
        heta0 heta1 hrel hstrip with
    ⟨Bflux, hBflux, hflux⟩
  rcases wholeLineCauchyReactionHessianHistory_bounded_positive
      p hM hT u₀ hsmall z hz htheta0 htheta1 with
    ⟨Breac, hBreac, hreac⟩
  let B : ℝ := Bheat + |p.χ| * Bflux + Breac
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro x
  rw [(wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
    p hM hT u₀ hsmall z hz htheta0 htheta1
      heta0 heta1 hrel hstrip x).deriv]
  calc
    |wholeLineCauchyHeatHessOp z.1 u₀.1 x +
        (-p.χ) * (∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatThirdOp (z.1 - s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) +
        (∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatHessOp (z.1 - s)
            (wholeLineCauchyReactionSourceTrajectory p hM hT
              (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x)| ≤
        |wholeLineCauchyHeatHessOp z.1 u₀.1 x| +
          |p.χ| * |∫ s in (0 : ℝ)..z.1,
            wholeLineCauchyHeatThirdOp (z.1 - s)
              (wholeLineCauchyFluxSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| +
          |∫ s in (0 : ℝ)..z.1,
            wholeLineCauchyHeatHessOp (z.1 - s)
              (wholeLineCauchyReactionSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| := by
      calc
        |wholeLineCauchyHeatHessOp z.1 u₀.1 x +
            (-p.χ) * (∫ s in (0 : ℝ)..z.1,
              wholeLineCauchyHeatThirdOp (z.1 - s)
                (wholeLineCauchyFluxSourceTrajectory p hM hT
                  (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x) +
            (∫ s in (0 : ℝ)..z.1,
              wholeLineCauchyHeatHessOp (z.1 - s)
                (wholeLineCauchyReactionSourceTrajectory p hM hT
                  (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x)| ≤
            |wholeLineCauchyHeatHessOp z.1 u₀.1 x| +
              |(-p.χ) * (∫ s in (0 : ℝ)..z.1,
                wholeLineCauchyHeatThirdOp (z.1 - s)
                  (wholeLineCauchyFluxSourceTrajectory p hM hT
                    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x)| +
              |∫ s in (0 : ℝ)..z.1,
                wholeLineCauchyHeatHessOp (z.1 - s)
                  (wholeLineCauchyReactionSourceTrajectory p hM hT
                    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| := by
          exact (abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)
        _ = _ := by rw [abs_mul, abs_neg]
    _ ≤ Bheat + |p.χ| * Bflux + Breac := by
      exact add_le_add (add_le_add (hheat x)
        (mul_le_mul_of_nonneg_left (hflux x) (abs_nonneg p.χ))) (hreac x)
    _ = B := rfl

/-- Uniform-in-target-time version of the Hessian Duhamel bound on a compact
positive window.  The source Hölder modulus is only needed on the enlarged
recent-source window `[a/2,b]`. -/
theorem wholeLineCauchyValueHistory_secondCoeff_bounded_positive_window
    {F : ℝ → WholeLineBUC} {a b C theta H : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hC : 0 ≤ C)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hFnorm : ∀ s, ‖F s‖ ≤ C) (hH : 0 ≤ H)
    (hholder : ∀ s ∈ Set.Icc (a / 2) b, ∀ y w : ℝ,
      |(F s).1 y - (F s).1 w| ≤ H * |y - w| ^ theta) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc a b, ∀ x,
      |∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (F s).1 x| ≤ B := by
  have haHalf : 0 < a / 2 := by positivity
  have hb0 : 0 ≤ b := ha.le.trans hab
  let Cearly : ℝ :=
    (5 * Real.sqrt 2 / 2) * (a / 2) ^ (-(1 : ℝ)) * C
  let Wtheta : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst theta
  let B : ℝ := Cearly * b +
    Wtheta * (b ^ (theta / 2 : ℝ) / (theta / 2)) * H
  have hCearly : 0 ≤ Cearly := by dsimp [Cearly]; positivity
  have hWtheta : 0 ≤ Wtheta := by
    dsimp [Wtheta]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta
  have hthetaHalf : 0 < theta / 2 := by positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg hCearly hb0)
      (mul_nonneg
        (mul_nonneg hWtheta
          (div_nonneg (Real.rpow_nonneg hb0 _) hthetaHalf.le)) hH)
  refine ⟨B, hB, ?_⟩
  intro t ht x
  have ht0 : 0 < t := ha.trans_le ht.1
  have htHalf : 0 < t / 2 := by positivity
  let bound : ℝ → ℝ := fun s =>
    Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * H
  have hboundInt : IntervalIntegrable bound volume 0 t := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0
    have hscaled := (hk.const_mul Wtheta).mul_const H
    have hconst : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    simpa [bound, mul_assoc] using hconst.add hscaled
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (F s).1 x‖ ≤
        ∫ s in (0 : ℝ)..t, bound s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht0.le _ hboundInt
      filter_upwards with s
      intro hs
      rcases lt_or_eq_of_le hs.2 with hst | rfl
      · have hlag : 0 < t - s := sub_pos.mpr hst
        by_cases hsHalf : s ≤ t / 2
        · have hlagHalf : a / 2 ≤ t - s := by
            have : t / 2 ≤ t - s := by linarith
            exact (div_le_div_of_nonneg_right ht.1 zero_le_two).trans this
          have hpow : (t - s) ^ (-(1 : ℝ)) ≤
              (a / 2) ^ (-(1 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos haHalf hlagHalf (by norm_num)
          have hglobal := wholeLineCauchyHeatHessOp_abs_le
            hlag hC (F s).1.continuous.aestronglyMeasurable
            (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
              (hFnorm s)) (x := x)
          rw [Real.norm_eq_abs]
          calc
            |wholeLineCauchyHeatHessOp (t - s) (F s).1 x| ≤
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
        · have hsWindow : s ∈ Set.Icc (a / 2) b := by
            constructor
            · exact (div_le_div_of_nonneg_right ht.1 zero_le_two).trans
                (le_of_not_ge hsHalf)
            · exact hst.le.trans ht.2
          have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
            hlag htheta0 htheta1 hH
            (F s).1.continuous.aestronglyMeasurable
            (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
              (hFnorm s))
            (hholder s hsWindow) (x := x)
          rw [Real.norm_eq_abs]
          calc
            |wholeLineCauchyHeatHessOp (t - s) (F s).1 x| ≤
                Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * H := by
              simpa [Wtheta] using hcancel
            _ ≤ bound s := by
              dsimp [bound]
              linarith
      · simp only [sub_self,
            wholeLineCauchyHeatHessOp_eq_zero_of_nonpos le_rfl, norm_zero]
        dsimp [bound]
        exact add_nonneg hCearly
          (mul_nonneg (mul_nonneg hWtheta
            (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)) hH)
    _ = Cearly * t +
        Wtheta * (t ^ (theta / 2 : ℝ) / (theta / 2)) * H := by
      change (∫ s in (0 : ℝ)..t,
        Cearly + Wtheta * (t - s) ^ (-1 + theta / 2 : ℝ) * H) = _
      have hsing :=
        ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
          (t := t) htheta0
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((hsing.const_mul Wtheta).mul_const H)]
      rw [intervalIntegral.integral_const, smul_eq_mul,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul,
        ShenWork.IntervalNeumannFullKernel.integral_sub_rpow_hessian ht0.le htheta0]
      ring
    _ ≤ Cearly * b +
        Wtheta * (b ^ (theta / 2 : ℝ) / (theta / 2)) * H := by
      have hrpow : t ^ (theta / 2 : ℝ) ≤ b ^ (theta / 2 : ℝ) :=
        Real.rpow_le_rpow ht0.le ht.2 hthetaHalf.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left ht.2 hCearly)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hrpow hthetaHalf.le) hWtheta) hH)
    _ = B := rfl

/-- The canonical reaction Hessian histories share one spatial bound on a
compact positive target-time window. -/
theorem wholeLineCauchyReactionHessianHistory_bounded_positive_window
    (p : CMParams) {M T a b theta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc a b, ∀ x,
      |∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| ≤ B := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let R : ℝ → WholeLineBUC :=
    wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have haHalf : 0 < a / 2 := by positivity
  rcases exists_wholeLineCauchyReactionSourceTrajectory_window_Ctheta
      p hM hT haHalf hbT u₀ hsmall htheta0 htheta1 with
    ⟨HR, hHR, hRholder⟩
  change ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc a b, ∀ x,
    |∫ s in (0 : ℝ)..t,
      wholeLineCauchyHeatHessOp (t - s) (R s).1 x| ≤ B
  exact wholeLineCauchyValueHistory_secondCoeff_bounded_positive_window
    ha hab hMR htheta0 htheta1 hRnorm hHR hRholder

/-- The homogeneous heat Hessians share one spatial bound on a compact
positive target-time window. -/
theorem wholeLineCauchyHeatHessOp_bounded_positive_window
    {a b : ℝ} (ha : 0 < a) (f : WholeLineBUC) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc a b, ∀ x,
      |wholeLineCauchyHeatHessOp t f.1 x| ≤ B := by
  let B : ℝ := (5 * Real.sqrt 2 / 2) * a ^ (-(1 : ℝ)) * ‖f‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro t ht x
  have ht0 : 0 < t := ha.trans_le ht.1
  have hpow : t ^ (-(1 : ℝ)) ≤ a ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha ht.1 (by norm_num)
  exact (wholeLineCauchyHeatHessOp_abs_le ht0 (norm_nonneg f)
    f.1.continuous.aestronglyMeasurable
    (fun y => WholeLineBUC.abs_apply_le_norm f y) (x := x)).trans (by
      dsimp [B]
      gcongr)

/-- The canonical chemotaxis third-kernel histories share one spatial bound
on a compact positive target-time window. -/
theorem wholeLineCauchyFluxThirdHistory_bounded_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ s ∈ Set.Icc (a / 2) b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x ∈
          Set.Icc (0 : ℝ) M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc a b, ∀ x,
      |∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatThirdOp (t - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x| ≤ B := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  have haHalf : 0 < a / 2 := by positivity
  have haHalfLeB : a / 2 ≤ b :=
    (div_le_self ha.le (by norm_num)).trans hab
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT haHalf haHalfLeB hbT u₀ hsmall
        htheta0 htheta1 heta0 heta1 hrel hstrip with
    ⟨rho, HFd, hrho0, hrho1, hHFd, hFdHolder⟩
  let DF : ℝ := HFd + 2 * MF
  have hDF : 0 ≤ DF := by dsimp [DF]; positivity
  let C3 : ℝ := heatThirdTailConstant
  let Cearly : ℝ := C3 * (a / 2) ^ (-(3 / 2 : ℝ)) * MF
  let Wrho : ℝ :=
    ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst rho
  let B : ℝ := Cearly * b +
    Wrho * (b ^ (rho / 2 : ℝ) / (rho / 2)) * HFd
  have hC3 : 0 ≤ C3 := by
    dsimp [C3]
    exact heatThirdTailConstant_nonneg
  have hCearly : 0 ≤ Cearly := by dsimp [Cearly]; positivity
  have hWrho : 0 ≤ Wrho := by
    dsimp [Wrho]
    exact ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg rho
  have hrhoHalf : 0 < rho / 2 := by positivity
  have hb0 : 0 ≤ b := ha.le.trans hab
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg (mul_nonneg hCearly hb0)
      (mul_nonneg
        (mul_nonneg hWrho
          (div_nonneg (Real.rpow_nonneg hb0 _) hrhoHalf.le)) hHFd)
  refine ⟨B, hB, ?_⟩
  intro t ht x
  have ht0 : 0 < t := ha.trans_le ht.1
  have htHalf : 0 < t / 2 := by positivity
  let bound : ℝ → ℝ := fun s =>
    Cearly + Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd
  have hboundInt : IntervalIntegrable bound volume 0 t := by
    have hk :=
      ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) hrho0
    have hscaled := (hk.const_mul Wrho).mul_const HFd
    have hconst : IntervalIntegrable (fun _ : ℝ => Cearly) volume 0 t :=
      intervalIntegrable_const
    simpa [bound, mul_assoc] using hconst.add hscaled
  change |∫ s in (0 : ℝ)..t,
    wholeLineCauchyHeatThirdOp (t - s) (F s).1 x| ≤ B
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatThirdOp (t - s) (F s).1 x‖ ≤
        ∫ s in (0 : ℝ)..t, bound s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht0.le _ hboundInt
      filter_upwards with s
      intro hs
      rcases lt_or_eq_of_le hs.2 with hst | rfl
      · have hlag : 0 < t - s := sub_pos.mpr hst
        by_cases hsHalf : s ≤ t / 2
        · have hlagHalf : a / 2 ≤ t - s := by
            have : t / 2 ≤ t - s := by linarith
            exact (div_le_div_of_nonneg_right ht.1 zero_le_two).trans this
          have hpow : (t - s) ^ (-(3 / 2 : ℝ)) ≤
              (a / 2) ^ (-(3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos haHalf hlagHalf (by norm_num)
          have hraw := wholeLineCauchyHeatThirdOp_abs_le
            hlag hMF (F s).1.continuous.aestronglyMeasurable
            (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans
              (hFnorm s)) (x := x)
          rw [Real.norm_eq_abs]
          calc
            |wholeLineCauchyHeatThirdOp (t - s) (F s).1 x| ≤
                (C3 / ((t - s) * Real.sqrt (t - s))) * MF := by
              simpa [C3] using hraw
            _ = C3 * (t - s) ^ (-(3 / 2 : ℝ)) * MF := by
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
        · have hsWindow : s ∈ Set.Icc (a / 2) b := by
            constructor
            · exact (div_le_div_of_nonneg_right ht.1 zero_le_two).trans
                (le_of_not_ge hsHalf)
            · exact hst.le.trans ht.2
          have hspos : 0 < s := haHalf.trans_le hsWindow.1
          let zs : Set.Icc (0 : ℝ) T :=
            ⟨s, hspos.le, hsWindow.2.trans hbT⟩
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
            (f := (F s).1) (x := x) hlag hFbound hFdBound hFdDeriv hFdCont
          have hcancel := wholeLineCauchyHeatHessOp_Ctheta_abs_le
            hlag hrho0 hrho1 hHFd hFdCont.aestronglyMeasurable
            hFdBound hFdHold (x := x)
          rw [Real.norm_eq_abs, hthirdEq]
          calc
            |wholeLineCauchyHeatHessOp (t - s) (deriv (F s).1) x| ≤
                Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd := by
              simpa [Wrho] using hcancel
            _ ≤ bound s := by
              dsimp [bound]
              linarith
      · simp only [sub_self,
            wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos le_rfl, norm_zero]
        dsimp [bound]
        exact add_nonneg hCearly
          (mul_nonneg (mul_nonneg hWrho
            (Real.rpow_nonneg (sub_nonneg.mpr le_rfl) _)) hHFd)
    _ = Cearly * t +
        Wrho * (t ^ (rho / 2 : ℝ) / (rho / 2)) * HFd := by
      change (∫ s in (0 : ℝ)..t,
        Cearly + Wrho * (t - s) ^ (-1 + rho / 2 : ℝ) * HFd) = _
      have hsing :=
        ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
          (t := t) hrho0
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((hsing.const_mul Wrho).mul_const HFd)]
      rw [intervalIntegral.integral_const, smul_eq_mul,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const_mul,
        ShenWork.IntervalNeumannFullKernel.integral_sub_rpow_hessian ht0.le hrho0]
      ring
    _ ≤ Cearly * b +
        Wrho * (b ^ (rho / 2 : ℝ) / (rho / 2)) * HFd := by
      have hrpow : t ^ (rho / 2 : ℝ) ≤ b ^ (rho / 2 : ℝ) :=
        Real.rpow_le_rpow ht0.le ht.2 hrhoHalf.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left ht.2 hCearly)
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hrpow hrhoHalf.le) hWrho) hHFd)
    _ = B := rfl

/-- On a compact positive-time window, the canonical mild fixed point has one
common global-in-space bound for its second spatial derivative. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatial_second_bounded_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ s ∈ Set.Icc (a / 2) b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x ∈
          Set.Icc (0 : ℝ) M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc a b, ∀ x,
      |deriv (fun y : ℝ => deriv
        (fun w : ℝ =>
          (wholeLineBUCTrajectoryExtend hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1 w) y) x| ≤ B := by
  rcases wholeLineCauchyHeatHessOp_bounded_positive_window ha u₀ with
    ⟨Bheat, hBheat, hheat⟩
  rcases wholeLineCauchyFluxThirdHistory_bounded_positive_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel hstrip with
    ⟨Bflux, hBflux, hflux⟩
  rcases wholeLineCauchyReactionHessianHistory_bounded_positive_window
      p hM hT ha hab hbT u₀ hsmall htheta0 htheta1 with
    ⟨Breac, hBreac, hreac⟩
  let B : ℝ := Bheat + |p.χ| * Bflux + Breac
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro t ht x
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  have ht0 : 0 < t := ha.trans_le ht.1
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht0.le, ht.2.trans hbT⟩
  have hext : wholeLineBUCTrajectoryExtend hT U t = U zt :=
    wholeLineBUCTrajectoryExtend_eq hT U zt.2
  have hstripTarget : ∀ s ∈ Set.Icc (t / 2) t, ∀ y,
      (wholeLineBUCTrajectoryExtend hT U s).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro s hs y
    apply hstrip s ?_ y
    constructor
    · exact (div_le_div_of_nonneg_right ht.1 zero_le_two).trans hs.1
    · exact hs.2.trans ht.2
  have hsecond :=
    (wholeLineCauchyBUCMildFixedPoint_spatial_second_hasDerivAt_positive
      p hM hT u₀ hsmall zt ht0 htheta0 htheta1
        heta0 heta1 hrel hstripTarget x).deriv
  let A : ℝ := wholeLineCauchyHeatHessOp t u₀.1 x
  let X : ℝ := ∫ s in (0 : ℝ)..t,
    wholeLineCauchyHeatThirdOp (t - s)
      (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 x
  let R : ℝ := ∫ s in (0 : ℝ)..t,
    wholeLineCauchyHeatHessOp (t - s)
      (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 x
  rw [hext]
  rw [hsecond]
  change |A + (-p.χ) * X + R| ≤ B
  calc
    |A + (-p.χ) * X + R| ≤ |A| + |(-p.χ) * X| + |R| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |A| + |p.χ| * |X| + |R| := by rw [abs_mul, abs_neg]
    _ ≤ Bheat + |p.χ| * Bflux + Breac := by
      exact add_le_add (add_le_add (by simpa [A] using hheat t ht x)
        (mul_le_mul_of_nonneg_left (by simpa [X, U] using hflux t ht x)
          (abs_nonneg p.χ)))
        (by simpa [R, U] using hreac t ht x)
    _ = B := rfl

/-- The differentiated physical flux has one global-in-space bound on every
compact positive canonical window. -/
theorem wholeLineCauchyFluxSourceTrajectory_deriv_bounded_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ s ∈ Set.Icc a b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x ∈
          Set.Icc (0 : ℝ) M) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Set.Icc a b, ∀ x,
      |deriv
        (wholeLineCauchyFluxSourceTrajectory p hM hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) t).1 x| ≤ D := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by dsimp [MF]; positivity
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_holder_positive_window
      p hM hT ha hab hbT u₀ hsmall
        htheta0 htheta1 heta0 heta1 hrel hstrip with
    ⟨rho, HFd, hrho0, _hrho1, hHFd, hFdHolder⟩
  let D : ℝ := HFd + 2 * MF
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro t ht x
  have ht0 : 0 < t := ha.trans_le ht.1
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht0.le, ht.2.trans hbT⟩
  have hext : wholeLineBUCTrajectoryExtend hT U t = U zt :=
    wholeLineBUCTrajectoryExtend_eq hT U zt.2
  have htStrip : ∀ y, (U zt).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro y
    rw [← hext]
    exact hstrip t ht y
  have hFdDeriv : ∀ y, HasDerivAt (F t).1 (deriv (F t).1 y) y := by
    intro y
    have h := wholeLineCauchyFluxSourceTrajectory_slice_hasDerivAt_positive
      p hM hT u₀ hsmall zt ht0 htStrip y
    simpa [F, U] using h.differentiableAt.hasDerivAt
  have hFdHold : ∀ y w,
      |deriv (F t).1 y - deriv (F t).1 w| ≤
        HFd * |y - w| ^ rho := by
    intro y w
    simpa [F, U] using hFdHolder t ht y w
  have hFbound : ∀ y, |(F t).1 y| ≤ MF := by
    intro y
    exact (WholeLineBUC.abs_apply_le_norm (F t) y).trans (hFnorm t)
  change |deriv (F t).1 x| ≤ D
  exact deriv_abs_le_of_bounded_of_deriv_holder
    hHFd hrho0 hFbound
    (fun y => (hFdDeriv y).differentiableAt) hFdHold x

/-- On a compact window strictly inside the canonical lifespan, the ordinary
time derivative has one global-in-space bound.  This is an immediate bounded
PDE consequence of the preceding `u_xx` and physical-flux bounds. -/
theorem wholeLineCauchyBUCMildFixedPoint_time_deriv_bounded_positive_window
    (p : CMParams) {M T a b theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc a b, ∀ x,
      |deriv (fun q : ℝ =>
        (wholeLineBUCTrajectoryExtend hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) q).1 x) t| ≤ B := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  have hstripHalf : ∀ s ∈ Set.Icc (a / 2) b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT U s).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    have hs0 : 0 ≤ s := (half_pos ha).le.trans hs.1
    have hsT : s ≤ T := hs.2.trans hbT.le
    let zs : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
    rw [wholeLineBUCTrajectoryExtend_eq hT U zs.2]
    exact hstrip zs x
  have hstripWindow : ∀ s ∈ Set.Icc a b, ∀ x,
      (wholeLineBUCTrajectoryExtend hT U s).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro s hs x
    exact hstripHalf s ⟨(div_le_self ha.le (by norm_num)).trans hs.1, hs.2⟩ x
  rcases wholeLineCauchyBUCMildFixedPoint_spatial_second_bounded_positive_window
      p hM hT ha hab hbT.le u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel hstripHalf with
    ⟨Bxx, hBxx, hxx⟩
  rcases wholeLineCauchyFluxSourceTrajectory_deriv_bounded_positive_window
      p hM hT ha hab hbT.le u₀ hsmall htheta0 htheta1
        heta0 heta1 hrel hstripWindow with
    ⟨BF, hBF, hF⟩
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by dsimp [MR]; positivity
  have hRnorm : ∀ s, ‖R s‖ ≤ MR := by
    intro s
    simpa [R, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  let B : ℝ := Bxx + M + |p.χ| * BF + MR
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro t ht x
  have ht0 : 0 < t := ha.trans_le ht.1
  have htT : t < T := ht.2.trans_lt hbT
  let zt : Set.Icc (0 : ℝ) T := ⟨t, ht0.le, htT.le⟩
  have hext : wholeLineBUCTrajectoryExtend hT U t = U zt :=
    wholeLineBUCTrajectoryExtend_eq hT U zt.2
  have htime :=
    (wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_positive
      p hM hT u₀ hsmall ht0 htT htheta0 htheta1
        heta0 heta1 hrel hstrip x).deriv
  let XX : ℝ := deriv (fun xi : ℝ => deriv
    (fun w : ℝ => (wholeLineBUCTrajectoryExtend hT U t).1 w) xi) x
  let V : ℝ := (wholeLineBUCTrajectoryExtend hT U t).1 x
  let FX : ℝ := deriv (F t).1 x
  let RV : ℝ := (R t).1 x
  rw [htime]
  change |XX - V + (-p.χ) * FX + RV| ≤ B
  have hXX : |XX| ≤ Bxx := by
    simpa [XX, U] using hxx t ht x
  have hV : |V| ≤ M := by
    have hVeq : V = (U zt).1 x := by simp [V, hext]
    rw [hVeq]
    rw [abs_of_nonneg (hstrip zt x).1]
    exact (hstrip zt x).2
  have hFX : |FX| ≤ BF := by
    simpa [FX, F, U] using hF t ht x
  have hRV : |RV| ≤ MR := by
    dsimp [RV]
    exact (WholeLineBUC.abs_apply_le_norm (R t) x).trans (hRnorm t)
  calc
    |XX - V + (-p.χ) * FX + RV| ≤
        |XX| + |V| + |p.χ| * |FX| + |RV| := by
      calc
        |XX - V + (-p.χ) * FX + RV| ≤
            |XX - V + (-p.χ) * FX| + |RV| := abs_add_le _ _
        _ ≤ (|XX - V| + |(-p.χ) * FX|) + |RV| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ ≤ (|XX| + |V| + |(-p.χ) * FX|) + |RV| :=
          add_le_add (add_le_add (abs_sub XX V) le_rfl) le_rfl
        _ = |XX| + |V| + |p.χ| * |FX| + |RV| := by
          rw [abs_mul, abs_neg]
    _ ≤ Bxx + M + |p.χ| * BF + MR := by
      exact add_le_add
        (add_le_add (add_le_add hXX hV)
          (mul_le_mul_of_nonneg_left hFX (abs_nonneg p.χ))) hRV
    _ = B := rfl

section WholeLineWeightedRegularityUnweightedSecondBoundAxiomAudit

#print axioms wholeLineCauchyValueHistory_secondCoeff_bounded_of_window_Ctheta
#print axioms wholeLineCauchyFluxThirdHistory_bounded_positive
#print axioms wholeLineCauchyReactionHessianHistory_bounded_positive
#print axioms wholeLineCauchyHeatHessOp_bounded_positive
#print axioms
  wholeLineCauchyBUCMildFixedPoint_spatial_second_bounded_positive
#print axioms
  wholeLineCauchyValueHistory_secondCoeff_bounded_positive_window
#print axioms
  wholeLineCauchyReactionHessianHistory_bounded_positive_window
#print axioms wholeLineCauchyHeatHessOp_bounded_positive_window
#print axioms wholeLineCauchyFluxThirdHistory_bounded_positive_window
#print axioms
  wholeLineCauchyBUCMildFixedPoint_spatial_second_bounded_positive_window
#print axioms
  wholeLineCauchyFluxSourceTrajectory_deriv_bounded_positive_window
#print axioms
  wholeLineCauchyBUCMildFixedPoint_time_deriv_bounded_positive_window

end WholeLineWeightedRegularityUnweightedSecondBoundAxiomAudit

end ShenWork.Paper1
