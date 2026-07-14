import ShenWork.Paper1.WholeLineCauchyBUCHeatPositiveTime
import ShenWork.PDE.IntervalGradDuhamelBound

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# BUC-valued whole-line Duhamel operators

The nonlinear source trajectories are continuously extended by clamping time
to `[0,T]`.  The value and gradient Gaussian operators then act on the genuine
complete BUC phase space, so their time integrals are Bochner integrals in BUC.
-/

/-- Constant time extension of a compact BUC trajectory. -/
def wholeLineBUCTrajectoryExtend
    {T : ℝ} (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T) (s : ℝ) :
    WholeLineBUC :=
  U (Set.projIcc 0 T hT s)

theorem wholeLineBUCTrajectoryExtend_continuous
    {T : ℝ} (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T) :
    Continuous (wholeLineBUCTrajectoryExtend hT U) :=
  U.continuous.comp continuous_projIcc

theorem wholeLineBUCTrajectoryExtend_eq
    {T s : ℝ} (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T)
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    wholeLineBUCTrajectoryExtend hT U s = U ⟨s, hs⟩ := by
  unfold wholeLineBUCTrajectoryExtend
  rw [Set.projIcc_of_mem hT hs]

def wholeLineCauchyFluxSourceTrajectory
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s : ℝ) : WholeLineBUC :=
  wholeLineCauchyTruncatedFluxBUC p M hM
    (wholeLineBUCTrajectoryExtend hT U s)

def wholeLineCauchyReactionSourceTrajectory
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (s : ℝ) : WholeLineBUC :=
  wholeLineCauchyTruncatedReactionBUC p M hM
    (wholeLineBUCTrajectoryExtend hT U s)

theorem wholeLineCauchyFluxSourceTrajectory_continuous
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    Continuous (wholeLineCauchyFluxSourceTrajectory p hM hT U) :=
  (wholeLineCauchyTruncatedFluxBUC_lipschitz p hM).continuous.comp
    (wholeLineBUCTrajectoryExtend_continuous hT U)

theorem wholeLineCauchyReactionSourceTrajectory_continuous
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    Continuous (wholeLineCauchyReactionSourceTrajectory p hM hT U) :=
  (wholeLineCauchyTruncatedReactionBUC_lipschitz p hM).continuous.comp
    (wholeLineBUCTrajectoryExtend_continuous hT U)

theorem wholeLineCauchyTruncatedFluxBUC_norm_le
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u : WholeLineBUC) :
    ‖wholeLineCauchyTruncatedFluxBUC p M hM u‖ ≤ M ^ p.m * M ^ p.γ := by
  change ‖(wholeLineCauchyTruncatedFluxBUC p M hM u).1‖ ≤ _
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 ?_
  intro x
  rw [Real.norm_eq_abs, wholeLineCauchyTruncatedFluxBUC_apply]
  exact wholeLineCauchyTruncatedFlux_abs_le p hM (WholeLineBUC.isCUnifBdd u) x

theorem wholeLineCauchyTruncatedReactionBUC_norm_le
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u : WholeLineBUC) :
    ‖wholeLineCauchyTruncatedReactionBUC p M hM u‖ ≤
      M + M * (1 + M ^ p.α) := by
  change ‖(wholeLineCauchyTruncatedReactionBUC p M hM u).1‖ ≤ _
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 ?_
  intro x
  rw [Real.norm_eq_abs, wholeLineCauchyTruncatedReactionBUC_apply]
  exact wholeLineCauchyTruncatedReaction_abs_le p hM (u.1 : ℝ → ℝ) x

theorem wholeLineCauchyHeatGradientBUC_norm_le_rpow
    {t : ℝ} (ht : 0 < t) (f : WholeLineBUC) :
    ‖wholeLineCauchyHeatGradientBUC t ht f‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) * ‖f‖) *
        t ^ (-(1 / 2 : ℝ)) := by
  have hbase := kernelConvBUC_norm_le
    (wholeLineModifiedHeatGradientKernel_continuous ht)
    (wholeLineModifiedHeatGradientKernel_integrable ht) f
  rw [wholeLineModifiedHeatGradientKernel_integral_abs ht] at hbase
  have hexp : Real.exp (-t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hnonneg : 0 ≤ (2 / Real.sqrt (4 * Real.pi * t)) * ‖f‖ := by
    positivity
  calc
    ‖wholeLineCauchyHeatGradientBUC t ht f‖
        ≤ (Real.exp (-t) * (2 / Real.sqrt (4 * Real.pi * t))) * ‖f‖ :=
      hbase
    _ ≤ 1 * ((2 / Real.sqrt (4 * Real.pi * t)) * ‖f‖) := by
      nlinarith
    _ = ((2 / Real.sqrt (4 * Real.pi)) * ‖f‖) *
          t ^ (-(1 / 2 : ℝ)) := by
      rw [two_div_sqrt_four_pi_mul_eq_rpow_cauchy ht]
      ring

def wholeLineCauchyGradientBUCIntegrand
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (t s : ℝ) : WholeLineBUC :=
  wholeLineCauchyHeatGradientBUCTotal (t - s)
    (wholeLineCauchyFluxSourceTrajectory p hM hT U s)

def wholeLineCauchyValueBUCIntegrand
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (t s : ℝ) : WholeLineBUC :=
  wholeLineCauchyHeatBUCTotal (t - s)
    (wholeLineCauchyReactionSourceTrajectory p hM hT U s)

theorem wholeLineCauchyGradientBUCIntegrand_continuousOn_Iio
    (p : CMParams) {M T t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    ContinuousOn (wholeLineCauchyGradientBUCIntegrand p hM hT U t)
      (Set.Iio t) := by
  intro s hs
  have hτ : 0 < t - s := sub_pos.mpr hs
  have hpair : ContinuousAt
      (fun r : ℝ =>
        (t - r, wholeLineCauchyFluxSourceTrajectory p hM hT U r)) s := by
    exact (continuousAt_const.sub continuousAt_id).prodMk
      (wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U).continuousAt
  exact (ContinuousAt.comp'
    (f := fun r : ℝ =>
      (t - r, wholeLineCauchyFluxSourceTrajectory p hM hT U r))
    (wholeLineCauchyHeatGradientBUCTotal_jointContinuousAt_of_pos hτ
      (wholeLineCauchyFluxSourceTrajectory p hM hT U s))
    hpair).continuousWithinAt

theorem wholeLineCauchyGradientBUCIntegrand_norm_le
    (p : CMParams) {M T t s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hs : s < t) :
    ‖wholeLineCauchyGradientBUCIntegrand p hM hT U t s‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
        (t - s) ^ (-(1 / 2 : ℝ)) := by
  have hτ : 0 < t - s := sub_pos.mpr hs
  let F := wholeLineCauchyFluxSourceTrajectory p hM hT U s
  have hFnorm : ‖F‖ ≤ M ^ p.m * M ^ p.γ :=
    wholeLineCauchyTruncatedFluxBUC_norm_le p hM
      (wholeLineBUCTrajectoryExtend hT U s)
  have hcoeff : 0 ≤ 2 / Real.sqrt (4 * Real.pi) := by positivity
  have hrpow : 0 ≤ (t - s) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hτ.le _
  unfold wholeLineCauchyGradientBUCIntegrand
  have htotal : wholeLineCauchyHeatGradientBUCTotal (t - s) F =
      wholeLineCauchyHeatGradientBUC (t - s) hτ F := by
    simp [wholeLineCauchyHeatGradientBUCTotal, hτ]
  rw [htotal]
  calc
    ‖wholeLineCauchyHeatGradientBUC (t - s) hτ F‖ ≤
        ((2 / Real.sqrt (4 * Real.pi)) * ‖F‖) *
          (t - s) ^ (-(1 / 2 : ℝ)) :=
      wholeLineCauchyHeatGradientBUC_norm_le_rpow hτ F
    _ ≤ ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
          (t - s) ^ (-(1 / 2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFnorm hcoeff) hrpow

theorem wholeLineCauchyGradientBUCIntegrand_intervalIntegrable
    (p : CMParams) {M T t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 ≤ t) :
    IntervalIntegrable
      (wholeLineCauchyGradientBUCIntegrand p hM hT U t) volume 0 t := by
  let A : ℝ := (2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)
  have hdomII : IntervalIntegrable
      (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul A
  have hdom : IntegrableOn
      (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ)))
      (Set.Ico (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le ht).1 hdomII
  have hmeas : AEStronglyMeasurable
      (wholeLineCauchyGradientBUCIntegrand p hM hT U t)
      (volume.restrict (Set.Ico (0 : ℝ) t)) :=
    ((wholeLineCauchyGradientBUCIntegrand_continuousOn_Iio p hM hT U).mono
      Set.Ico_subset_Iio_self).aestronglyMeasurable measurableSet_Ico
  rw [intervalIntegrable_iff_integrableOn_Ico_of_le ht]
  refine ⟨hmeas, hdom.2.mono_enorm ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
  have hnorm := wholeLineCauchyGradientBUCIntegrand_norm_le p hM hT U hs.2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hg : 0 ≤ A * (t - s) ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hA (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _)
  rw [← ofReal_norm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.norm_eq_abs, abs_of_nonneg hg] using hnorm

/-- The divergence-form source integrated as an honest Bochner integral in
`BUC(ℝ)`. -/
def wholeLineCauchyGradientDuhamelBUC
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (t : ℝ) : WholeLineBUC :=
  ∫ s in (0 : ℝ)..t,
    wholeLineCauchyGradientBUCIntegrand p hM hT U t s

@[simp] theorem wholeLineCauchyGradientDuhamelBUC_zero
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    wholeLineCauchyGradientDuhamelBUC p hM hT U 0 = 0 := by
  simp [wholeLineCauchyGradientDuhamelBUC]

theorem wholeLineCauchyGradientDuhamelBUC_norm_le
    (p : CMParams) {M T t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 ≤ t) :
    ‖wholeLineCauchyGradientDuhamelBUC p hM hT U t‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
        (2 * Real.sqrt t) := by
  let A : ℝ := (2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)
  have hdom : IntervalIntegrable
      (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul A
  unfold wholeLineCauchyGradientDuhamelBUC
  calc
    ‖∫ s in (0 : ℝ)..t,
        wholeLineCauchyGradientBUCIntegrand p hM hT U t s‖
        ≤ ∫ s in (0 : ℝ)..t, A * (t - s) ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hdom
      filter_upwards with s
      intro hs
      by_cases hst : s = t
      · subst s
        simp [wholeLineCauchyGradientBUCIntegrand,
          wholeLineCauchyHeatGradientBUCTotal]
      · simpa [A] using
          wholeLineCauchyGradientBUCIntegrand_norm_le p hM hT U
            (lt_of_le_of_ne hs.2 hst)
    _ = A * (2 * Real.sqrt t) := by
      rw [intervalIntegral.integral_const_mul,
        ShenWork.IntervalGradDuhamelBound.integral_sub_rpow_neg_half ht]
    _ = ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
          (2 * Real.sqrt t) := rfl

theorem wholeLineCauchyHeatBUCTotal_norm_le_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) (f : WholeLineBUC) :
    ‖wholeLineCauchyHeatBUCTotal t f‖ ≤ ‖f‖ := by
  by_cases ht0 : t = 0
  · subst t
    simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have htotal : wholeLineCauchyHeatBUCTotal t f =
        wholeLineCauchyHeatBUC t htpos f := by
      simp [wholeLineCauchyHeatBUCTotal, htpos]
    rw [htotal]
    have hbase := kernelConvBUC_norm_le
      (wholeLineModifiedHeatKernel_continuous htpos)
      (wholeLineModifiedHeatKernel_integrable htpos) f
    rw [wholeLineModifiedHeatKernel_integral_abs htpos] at hbase
    exact hbase.trans (by
      have hexp : Real.exp (-t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      exact mul_le_of_le_one_left (norm_nonneg f) hexp)

theorem wholeLineCauchyValueBUCIntegrand_continuousOn_Iio
    (p : CMParams) {M T t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    ContinuousOn (wholeLineCauchyValueBUCIntegrand p hM hT U t)
      (Set.Iio t) := by
  intro s hs
  have hτ : 0 < t - s := sub_pos.mpr hs
  have hpair : ContinuousAt
      (fun r : ℝ =>
        (t - r, wholeLineCauchyReactionSourceTrajectory p hM hT U r)) s := by
    exact (continuousAt_const.sub continuousAt_id).prodMk
      (wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U).continuousAt
  exact (ContinuousAt.comp'
    (f := fun r : ℝ =>
      (t - r, wholeLineCauchyReactionSourceTrajectory p hM hT U r))
    (wholeLineCauchyHeatBUCTotal_jointContinuousAt_of_pos hτ
      (wholeLineCauchyReactionSourceTrajectory p hM hT U s))
    hpair).continuousWithinAt

theorem wholeLineCauchyValueBUCIntegrand_norm_le
    (p : CMParams) {M T t s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hs : s ≤ t) :
    ‖wholeLineCauchyValueBUCIntegrand p hM hT U t s‖ ≤
      M + M * (1 + M ^ p.α) := by
  unfold wholeLineCauchyValueBUCIntegrand
  exact (wholeLineCauchyHeatBUCTotal_norm_le_of_nonneg (sub_nonneg.mpr hs) _).trans
    (wholeLineCauchyTruncatedReactionBUC_norm_le p hM _)

theorem wholeLineCauchyValueBUCIntegrand_intervalIntegrable
    (p : CMParams) {M T t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 ≤ t) :
    IntervalIntegrable
      (wholeLineCauchyValueBUCIntegrand p hM hT U t) volume 0 t := by
  let C : ℝ := M + M * (1 + M ^ p.α)
  have hdomII : IntervalIntegrable (fun _ : ℝ => C) volume 0 t :=
    intervalIntegrable_const
  have hdom : IntegrableOn (fun _ : ℝ => C) (Set.Ico (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le ht).1 hdomII
  have hmeas : AEStronglyMeasurable
      (wholeLineCauchyValueBUCIntegrand p hM hT U t)
      (volume.restrict (Set.Ico (0 : ℝ) t)) :=
    ((wholeLineCauchyValueBUCIntegrand_continuousOn_Iio p hM hT U).mono
      Set.Ico_subset_Iio_self).aestronglyMeasurable measurableSet_Ico
  rw [intervalIntegrable_iff_integrableOn_Ico_of_le ht]
  refine ⟨hmeas, hdom.2.mono_enorm ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
  rw [← ofReal_norm, ← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by
    dsimp [C]
    positivity : 0 ≤ C)] using
      wholeLineCauchyValueBUCIntegrand_norm_le p hM hT U hs.2.le

/-- The corrected reaction source integrated as a Bochner integral in BUC. -/
def wholeLineCauchyValueDuhamelBUC
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (t : ℝ) : WholeLineBUC :=
  ∫ s in (0 : ℝ)..t,
    wholeLineCauchyValueBUCIntegrand p hM hT U t s

@[simp] theorem wholeLineCauchyValueDuhamelBUC_zero
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    wholeLineCauchyValueDuhamelBUC p hM hT U 0 = 0 := by
  simp [wholeLineCauchyValueDuhamelBUC]

theorem wholeLineCauchyValueDuhamelBUC_norm_le
    (p : CMParams) {M T t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 ≤ t) :
    ‖wholeLineCauchyValueDuhamelBUC p hM hT U t‖ ≤
      (M + M * (1 + M ^ p.α)) * t := by
  let C : ℝ := M + M * (1 + M ^ p.α)
  have hdom : IntervalIntegrable (fun _ : ℝ => C) volume 0 t :=
    intervalIntegrable_const
  unfold wholeLineCauchyValueDuhamelBUC
  calc
    ‖∫ s in (0 : ℝ)..t,
        wholeLineCauchyValueBUCIntegrand p hM hT U t s‖
        ≤ ∫ _s in (0 : ℝ)..t, C := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hdom
      filter_upwards with s
      intro hs
      simpa [C] using
        wholeLineCauchyValueBUCIntegrand_norm_le p hM hT U hs.2
    _ = C * t := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul, mul_comm]
    _ = (M + M * (1 + M ^ p.α)) * t := rfl

theorem wholeLineBUCTrajectoryExtend_dist_le
    {T s : ℝ} (hT : 0 ≤ T) (U W : WholeLineBUCTrajectory T) :
    dist (wholeLineBUCTrajectoryExtend hT U s)
        (wholeLineBUCTrajectoryExtend hT W s) ≤ dist U W := by
  exact (ContinuousMap.dist_le dist_nonneg).1 le_rfl
    (Set.projIcc 0 T hT s)

theorem wholeLineCauchyFluxSourceTrajectory_dist_le
    (p : CMParams) {M T s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U W : WholeLineBUCTrajectory T) :
    dist (wholeLineCauchyFluxSourceTrajectory p hM hT U s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT W s) ≤
      wholeLineCauchyFluxLip p M * dist U W := by
  exact (wholeLineCauchyTruncatedFluxBUC_dist_le p hM _ _).trans
    (mul_le_mul_of_nonneg_left
      (wholeLineBUCTrajectoryExtend_dist_le hT U W)
      (wholeLineCauchyFluxLip_nonneg p hM))

theorem wholeLineCauchyReactionSourceTrajectory_dist_le
    (p : CMParams) {M T s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U W : WholeLineBUCTrajectory T) :
    dist (wholeLineCauchyReactionSourceTrajectory p hM hT U s)
        (wholeLineCauchyReactionSourceTrajectory p hM hT W s) ≤
      (1 + reactionLip p.α M) * dist U W := by
  have hL : 0 ≤ 1 + reactionLip p.α M := by
    linarith [reactionLip_nonneg p.hα hM]
  exact (wholeLineCauchyTruncatedReactionBUC_dist_le p hM _ _).trans
    (mul_le_mul_of_nonneg_left
      (wholeLineBUCTrajectoryExtend_dist_le hT U W) hL)

theorem wholeLineCauchyHeatGradientBUC_dist_le_rpow
    {t : ℝ} (ht : 0 < t) (f g : WholeLineBUC) :
    dist (wholeLineCauchyHeatGradientBUC t ht f)
        (wholeLineCauchyHeatGradientBUC t ht g) ≤
      ((2 / Real.sqrt (4 * Real.pi)) * dist f g) *
        t ^ (-(1 / 2 : ℝ)) := by
  have hbase := wholeLineCauchyHeatGradientBUC_dist_le ht f g
  have hexp : Real.exp (-t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hnonneg : 0 ≤ (2 / Real.sqrt (4 * Real.pi * t)) * dist f g := by
    positivity
  calc
    dist (wholeLineCauchyHeatGradientBUC t ht f)
        (wholeLineCauchyHeatGradientBUC t ht g)
        ≤ (Real.exp (-t) * (2 / Real.sqrt (4 * Real.pi * t))) *
            dist f g := hbase
    _ ≤ 1 * ((2 / Real.sqrt (4 * Real.pi * t)) * dist f g) := by
      nlinarith
    _ = ((2 / Real.sqrt (4 * Real.pi)) * dist f g) *
          t ^ (-(1 / 2 : ℝ)) := by
      rw [two_div_sqrt_four_pi_mul_eq_rpow_cauchy ht]
      ring

theorem wholeLineCauchyHeatBUCTotal_dist_le_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) (f g : WholeLineBUC) :
    dist (wholeLineCauchyHeatBUCTotal t f)
        (wholeLineCauchyHeatBUCTotal t g) ≤ dist f g := by
  by_cases ht0 : t = 0
  · subst t
    simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hf : wholeLineCauchyHeatBUCTotal t f =
        wholeLineCauchyHeatBUC t htpos f := by
      simp [wholeLineCauchyHeatBUCTotal, htpos]
    have hg : wholeLineCauchyHeatBUCTotal t g =
        wholeLineCauchyHeatBUC t htpos g := by
      simp [wholeLineCauchyHeatBUCTotal, htpos]
    rw [hf, hg]
    exact (wholeLineCauchyHeatBUC_dist_le htpos f g).trans
      (mul_le_of_le_one_left dist_nonneg
        (Real.exp_le_one_iff.mpr (by linarith)))

theorem wholeLineCauchyGradientBUCIntegrand_sub_norm_le
    (p : CMParams) {M T t s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U W : WholeLineBUCTrajectory T) (hs : s < t) :
    ‖wholeLineCauchyGradientBUCIntegrand p hM hT U t s -
        wholeLineCauchyGradientBUCIntegrand p hM hT W t s‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) *
          (wholeLineCauchyFluxLip p M * dist U W)) *
        (t - s) ^ (-(1 / 2 : ℝ)) := by
  have hτ : 0 < t - s := sub_pos.mpr hs
  have hsrc := wholeLineCauchyFluxSourceTrajectory_dist_le
    p hM hT U W (s := s)
  unfold wholeLineCauchyGradientBUCIntegrand
  have hleft : wholeLineCauchyHeatGradientBUCTotal (t - s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s) =
      wholeLineCauchyHeatGradientBUC (t - s) hτ
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s) := by
    simp [wholeLineCauchyHeatGradientBUCTotal, hτ]
  have hright : wholeLineCauchyHeatGradientBUCTotal (t - s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT W s) =
      wholeLineCauchyHeatGradientBUC (t - s) hτ
        (wholeLineCauchyFluxSourceTrajectory p hM hT W s) := by
    simp [wholeLineCauchyHeatGradientBUCTotal, hτ]
  calc
    ‖wholeLineCauchyHeatGradientBUCTotal (t - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT U s) -
        wholeLineCauchyHeatGradientBUCTotal (t - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT W s)‖ =
        dist (wholeLineCauchyHeatGradientBUCTotal (t - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT U s))
          (wholeLineCauchyHeatGradientBUCTotal (t - s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT W s)) :=
      (WholeLineBUC.dist_eq_norm_sub _ _).symm
    _ = dist (wholeLineCauchyHeatGradientBUC (t - s) hτ
          (wholeLineCauchyFluxSourceTrajectory p hM hT U s))
        (wholeLineCauchyHeatGradientBUC (t - s) hτ
          (wholeLineCauchyFluxSourceTrajectory p hM hT W s)) := by
      rw [hleft, hright]
    _ ≤ ((2 / Real.sqrt (4 * Real.pi)) *
          dist (wholeLineCauchyFluxSourceTrajectory p hM hT U s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT W s)) *
        (t - s) ^ (-(1 / 2 : ℝ)) :=
      wholeLineCauchyHeatGradientBUC_dist_le_rpow hτ _ _
    _ ≤ ((2 / Real.sqrt (4 * Real.pi)) *
          (wholeLineCauchyFluxLip p M * dist U W)) *
        (t - s) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsrc (by positivity))
        (Real.rpow_nonneg hτ.le _)

theorem wholeLineCauchyValueBUCIntegrand_sub_norm_le
    (p : CMParams) {M T t s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U W : WholeLineBUCTrajectory T) (hs : s ≤ t) :
    ‖wholeLineCauchyValueBUCIntegrand p hM hT U t s -
        wholeLineCauchyValueBUCIntegrand p hM hT W t s‖ ≤
      (1 + reactionLip p.α M) * dist U W := by
  unfold wholeLineCauchyValueBUCIntegrand
  calc
    ‖wholeLineCauchyHeatBUCTotal (t - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT U s) -
        wholeLineCauchyHeatBUCTotal (t - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT W s)‖ =
        dist (wholeLineCauchyHeatBUCTotal (t - s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT U s))
          (wholeLineCauchyHeatBUCTotal (t - s)
            (wholeLineCauchyReactionSourceTrajectory p hM hT W s)) :=
      (WholeLineBUC.dist_eq_norm_sub _ _).symm
    _ ≤ dist (wholeLineCauchyReactionSourceTrajectory p hM hT U s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT W s) :=
      wholeLineCauchyHeatBUCTotal_dist_le_of_nonneg
        (sub_nonneg.mpr hs) _ _
    _ ≤ (1 + reactionLip p.α M) * dist U W :=
      wholeLineCauchyReactionSourceTrajectory_dist_le p hM hT U W

theorem wholeLineCauchyGradientDuhamelBUC_dist_le
    (p : CMParams) {M T t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U W : WholeLineBUCTrajectory T) (ht : 0 ≤ t) :
    dist (wholeLineCauchyGradientDuhamelBUC p hM hT U t)
        (wholeLineCauchyGradientDuhamelBUC p hM hT W t) ≤
      ((2 / Real.sqrt (4 * Real.pi)) *
          (wholeLineCauchyFluxLip p M * dist U W)) *
        (2 * Real.sqrt t) := by
  let A : ℝ := (2 / Real.sqrt (4 * Real.pi)) *
    (wholeLineCauchyFluxLip p M * dist U W)
  have hdom : IntervalIntegrable
      (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul A
  have hsub :
      (∫ s in (0 : ℝ)..t,
        (wholeLineCauchyGradientBUCIntegrand p hM hT U t s -
          wholeLineCauchyGradientBUCIntegrand p hM hT W t s)) =
        wholeLineCauchyGradientDuhamelBUC p hM hT U t -
          wholeLineCauchyGradientDuhamelBUC p hM hT W t := by
    unfold wholeLineCauchyGradientDuhamelBUC
    exact intervalIntegral.integral_sub
      (wholeLineCauchyGradientBUCIntegrand_intervalIntegrable p hM hT U ht)
      (wholeLineCauchyGradientBUCIntegrand_intervalIntegrable p hM hT W ht)
  calc
    dist (wholeLineCauchyGradientDuhamelBUC p hM hT U t)
        (wholeLineCauchyGradientDuhamelBUC p hM hT W t) =
        ‖wholeLineCauchyGradientDuhamelBUC p hM hT U t -
          wholeLineCauchyGradientDuhamelBUC p hM hT W t‖ :=
      WholeLineBUC.dist_eq_norm_sub _ _
    _ = ‖∫ s in (0 : ℝ)..t,
        (wholeLineCauchyGradientBUCIntegrand p hM hT U t s -
          wholeLineCauchyGradientBUCIntegrand p hM hT W t s)‖ :=
      congrArg norm hsub.symm
    _ ≤ ∫ s in (0 : ℝ)..t, A * (t - s) ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hdom
      filter_upwards with s
      intro hs
      by_cases hst : s = t
      · subst s
        simp [wholeLineCauchyGradientBUCIntegrand,
          wholeLineCauchyHeatGradientBUCTotal]
      · simpa [A] using
          wholeLineCauchyGradientBUCIntegrand_sub_norm_le
            p hM hT U W (lt_of_le_of_ne hs.2 hst)
    _ = A * (2 * Real.sqrt t) := by
      rw [intervalIntegral.integral_const_mul,
        ShenWork.IntervalGradDuhamelBound.integral_sub_rpow_neg_half ht]
    _ = ((2 / Real.sqrt (4 * Real.pi)) *
          (wholeLineCauchyFluxLip p M * dist U W)) *
        (2 * Real.sqrt t) := rfl

theorem wholeLineCauchyValueDuhamelBUC_dist_le
    (p : CMParams) {M T t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U W : WholeLineBUCTrajectory T) (ht : 0 ≤ t) :
    dist (wholeLineCauchyValueDuhamelBUC p hM hT U t)
        (wholeLineCauchyValueDuhamelBUC p hM hT W t) ≤
      ((1 + reactionLip p.α M) * dist U W) * t := by
  let C : ℝ := (1 + reactionLip p.α M) * dist U W
  have hdom : IntervalIntegrable (fun _ : ℝ => C) volume 0 t :=
    intervalIntegrable_const
  have hsub :
      (∫ s in (0 : ℝ)..t,
        (wholeLineCauchyValueBUCIntegrand p hM hT U t s -
          wholeLineCauchyValueBUCIntegrand p hM hT W t s)) =
        wholeLineCauchyValueDuhamelBUC p hM hT U t -
          wholeLineCauchyValueDuhamelBUC p hM hT W t := by
    unfold wholeLineCauchyValueDuhamelBUC
    exact intervalIntegral.integral_sub
      (wholeLineCauchyValueBUCIntegrand_intervalIntegrable p hM hT U ht)
      (wholeLineCauchyValueBUCIntegrand_intervalIntegrable p hM hT W ht)
  calc
    dist (wholeLineCauchyValueDuhamelBUC p hM hT U t)
        (wholeLineCauchyValueDuhamelBUC p hM hT W t) =
        ‖wholeLineCauchyValueDuhamelBUC p hM hT U t -
          wholeLineCauchyValueDuhamelBUC p hM hT W t‖ :=
      WholeLineBUC.dist_eq_norm_sub _ _
    _ = ‖∫ s in (0 : ℝ)..t,
        (wholeLineCauchyValueBUCIntegrand p hM hT U t s -
          wholeLineCauchyValueBUCIntegrand p hM hT W t s)‖ :=
      congrArg norm hsub.symm
    _ ≤ ∫ _s in (0 : ℝ)..t, C := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hdom
      filter_upwards with s
      intro hs
      simpa [C] using
        wholeLineCauchyValueBUCIntegrand_sub_norm_le p hM hT U W hs.2
    _ = C * t := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul, mul_comm]
    _ = ((1 + reactionLip p.α M) * dist U W) * t := rfl

section WholeLineCauchyBUCDuhamelAxiomAudit

#print axioms wholeLineCauchyGradientDuhamelBUC_norm_le
#print axioms wholeLineCauchyValueDuhamelBUC_norm_le
#print axioms wholeLineCauchyGradientDuhamelBUC_dist_le
#print axioms wholeLineCauchyValueDuhamelBUC_dist_le

end WholeLineCauchyBUCDuhamelAxiomAudit

end ShenWork.Paper1
