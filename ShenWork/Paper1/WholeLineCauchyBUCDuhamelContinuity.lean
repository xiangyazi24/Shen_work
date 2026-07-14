import ShenWork.Paper1.WholeLineCauchyBUCDuhamel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Topology MeasureTheory Real Set intervalIntegral
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Time continuity of the BUC-valued Duhamel operators

The gradient kernel has the integrable diagonal singularity
`(t-s)^(-1/2)`.  Rescaling `s = t*r` converts the moving interval to
`[0,1]`; the extra Jacobian changes the singularity into the fixed integrable
majorant `sqrt T * (1-r)^(-1/2)`.
-/

/-- Banach-valued version of the fixed-window rescaling argument for a
variable-upper-limit Duhamel integral. -/
theorem continuous_singular_duhamel_banach
    {X E : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : X → ℝ → E} {τ : X → ℝ} {bound : ℝ → ℝ}
    (hG_meas : ∀ z, AEStronglyMeasurable
      (fun r => τ z • F z (τ z * r))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)))
    (hbound_int : IntervalIntegrable bound volume 0 1)
    (hG_bound : ∀ z, ∀ᵐ r ∂volume, r ∈ Set.uIoc (0 : ℝ) 1 →
      ‖τ z • F z (τ z * r)‖ ≤ bound r)
    (hG_cont : ∀ᵐ r ∂volume, r ∈ Set.uIoc (0 : ℝ) 1 →
      Continuous (fun z => τ z • F z (τ z * r))) :
    Continuous (fun z => ∫ s in (0 : ℝ)..(τ z), F z s) := by
  have hrescale : (fun z => ∫ s in (0 : ℝ)..(τ z), F z s) =
      fun z => ∫ r in (0 : ℝ)..1, τ z • F z (τ z * r) := by
    funext z
    have h := intervalIntegral.smul_integral_comp_mul_left
      (a := (0 : ℝ)) (b := 1) (f := F z) (τ z)
    simp only [mul_zero, mul_one] at h
    rw [← h, intervalIntegral.integral_smul]
  rw [hrescale]
  exact intervalIntegral.continuous_of_dominated_interval
    hG_meas hG_bound hbound_int hG_cont

def wholeLineCauchyGradientBUCRescaled
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (r : ℝ)
    (z : Set.Icc (0 : ℝ) T) : WholeLineBUC :=
  z.1 • wholeLineCauchyGradientBUCIntegrand
    p hM hT U z.1 (z.1 * r)

theorem wholeLineCauchyGradientBUCRescaled_continuousOn_Iio
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (z : Set.Icc (0 : ℝ) T) :
    ContinuousOn
      (fun r => wholeLineCauchyGradientBUCRescaled p hM hT U r z)
      (Set.Iio 1) := by
  by_cases hz : z.1 = 0
  · have heq : (fun r => wholeLineCauchyGradientBUCRescaled p hM hT U r z) =
        fun _ : ℝ => (0 : WholeLineBUC) := by
      funext r
      simp [wholeLineCauchyGradientBUCRescaled, hz]
    rw [heq]
    exact continuousOn_const
  · have hzpos : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz)
    intro r hr
    have hrlt : r < 1 := hr
    have hlag : 0 < z.1 - z.1 * r := by
      rw [show z.1 - z.1 * r = z.1 * (1 - r) by ring]
      exact mul_pos hzpos (sub_pos.mpr hrlt)
    have htime : ContinuousAt (fun q : ℝ => z.1 * q) r :=
      continuousAt_const.mul continuousAt_id
    have hpair : ContinuousAt
        (fun q : ℝ =>
          (z.1 - z.1 * q,
            wholeLineCauchyFluxSourceTrajectory p hM hT U (z.1 * q))) r := by
      exact (continuousAt_const.sub htime).prodMk
        ((wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U).continuousAt.comp'
          htime)
    have hop : ContinuousAt
        (fun q : ℝ => wholeLineCauchyGradientBUCIntegrand
          p hM hT U z.1 (z.1 * q)) r := by
      change ContinuousAt
        (fun q : ℝ => wholeLineCauchyHeatGradientBUCTotal
          (z.1 - z.1 * q)
          (wholeLineCauchyFluxSourceTrajectory p hM hT U (z.1 * q))) r
      exact ContinuousAt.comp'
        (f := fun q : ℝ =>
          (z.1 - z.1 * q,
            wholeLineCauchyFluxSourceTrajectory p hM hT U (z.1 * q)))
        (wholeLineCauchyHeatGradientBUCTotal_jointContinuousAt_of_pos hlag
          (wholeLineCauchyFluxSourceTrajectory p hM hT U (z.1 * r)))
        hpair
    exact (continuousAt_const.smul hop).continuousWithinAt

theorem wholeLineCauchyGradientBUCRescaled_norm_le_sqrt
    (p : CMParams) {M T r : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hr : r < 1)
    (z : Set.Icc (0 : ℝ) T) :
    ‖wholeLineCauchyGradientBUCRescaled p hM hT U r z‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
        Real.sqrt z.1 * (1 - r) ^ (-(1 / 2 : ℝ)) := by
  by_cases hz : z.1 = 0
  · have hzero : wholeLineCauchyGradientBUCRescaled p hM hT U r z = 0 := by
      simp [wholeLineCauchyGradientBUCRescaled, hz]
    rw [hzero]
    have hC : 0 ≤ (2 / Real.sqrt (4 * Real.pi)) *
        (M ^ p.m * M ^ p.γ) := by positivity
    have h1r : 0 ≤ 1 - r := (sub_pos.mpr hr).le
    have hnonneg : 0 ≤ ((2 / Real.sqrt (4 * Real.pi)) *
        (M ^ p.m * M ^ p.γ)) * Real.sqrt z.1 *
          (1 - r) ^ (-(1 / 2 : ℝ)) := mul_nonneg
      (mul_nonneg hC (Real.sqrt_nonneg z.1))
      (Real.rpow_nonneg h1r _)
    have hnormzero : ‖(0 : WholeLineBUC)‖ = 0 := by
      change ‖(0 : BoundedContinuousFunction ℝ ℝ)‖ = 0
      exact norm_zero
    rw [hnormzero]
    exact hnonneg
  · have hzpos : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz)
    have hsr : z.1 * r < z.1 := by nlinarith
    have hbase := wholeLineCauchyGradientBUCIntegrand_norm_le
      p hM hT U hsr
    have hfac : z.1 - z.1 * r = z.1 * (1 - r) := by ring
    rw [hfac, Real.mul_rpow z.2.1 (by linarith : 0 ≤ 1 - r)] at hbase
    have hhalf : z.1 * z.1 ^ (-(1 / 2 : ℝ)) =
        z.1 ^ (1 / 2 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one z.1]
      rw [← Real.rpow_add hzpos]
      norm_num
    have hsqrt : z.1 ^ (1 / 2 : ℝ) = Real.sqrt z.1 := by
      rw [Real.sqrt_eq_rpow]
    have hC : 0 ≤ (2 / Real.sqrt (4 * Real.pi)) *
        (M ^ p.m * M ^ p.γ) := by positivity
    have hrpow : 0 ≤ (1 - r) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (by linarith) _
    unfold wholeLineCauchyGradientBUCRescaled
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg z.2.1]
    calc
      z.1 * ‖wholeLineCauchyGradientBUCIntegrand
          p hM hT U z.1 (z.1 * r)‖ ≤
          z.1 * (((2 / Real.sqrt (4 * Real.pi)) *
            (M ^ p.m * M ^ p.γ)) *
              (z.1 ^ (-(1 / 2 : ℝ)) *
                (1 - r) ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbase z.2.1
      _ = ((2 / Real.sqrt (4 * Real.pi)) *
            (M ^ p.m * M ^ p.γ)) *
          (z.1 * z.1 ^ (-(1 / 2 : ℝ))) *
            (1 - r) ^ (-(1 / 2 : ℝ)) := by ring
      _ = ((2 / Real.sqrt (4 * Real.pi)) *
            (M ^ p.m * M ^ p.γ)) * Real.sqrt z.1 *
            (1 - r) ^ (-(1 / 2 : ℝ)) := by rw [hhalf, hsqrt]

theorem wholeLineCauchyGradientBUCRescaled_norm_le
    (p : CMParams) {M T r : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hr : r < 1)
    (z : Set.Icc (0 : ℝ) T) :
    ‖wholeLineCauchyGradientBUCRescaled p hM hT U r z‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
        Real.sqrt T * (1 - r) ^ (-(1 / 2 : ℝ)) := by
  have hC : 0 ≤ (2 / Real.sqrt (4 * Real.pi)) *
      (M ^ p.m * M ^ p.γ) := by positivity
  have hrpow : 0 ≤ (1 - r) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (sub_nonneg.mpr hr.le) _
  exact (wholeLineCauchyGradientBUCRescaled_norm_le_sqrt
    p hM hT U hr z).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt z.2.2) hC) hrpow)

theorem wholeLineCauchyGradientBUCRescaled_continuous
    (p : CMParams) {M T r : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hr : r < 1) :
    Continuous
      (fun z : Set.Icc (0 : ℝ) T =>
        wholeLineCauchyGradientBUCRescaled p hM hT U r z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.1 = 0
  · have hzero : wholeLineCauchyGradientBUCRescaled p hM hT U r z = 0 := by
      simp [wholeLineCauchyGradientBUCRescaled, hz]
    change Tendsto
      (fun y : Set.Icc (0 : ℝ) T =>
        wholeLineCauchyGradientBUCRescaled p hM hT U r y)
      (nhds z) (nhds (wholeLineCauchyGradientBUCRescaled p hM hT U r z))
    rw [hzero]
    refine tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero'
        (g := fun y : Set.Icc (0 : ℝ) T =>
          ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
            Real.sqrt y.1 * (1 - r) ^ (-(1 / 2 : ℝ)))
        (Eventually.of_forall fun _ => dist_nonneg) ?_ ?_)
    · exact Eventually.of_forall fun y => by
        rw [WholeLineBUC.dist_zero_eq_norm]
        exact wholeLineCauchyGradientBUCRescaled_norm_le_sqrt
          p hM hT U hr y
    · have hcont : ContinuousAt
          (fun y : Set.Icc (0 : ℝ) T =>
            ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
              Real.sqrt y.1 * (1 - r) ^ (-(1 / 2 : ℝ))) z :=
          ((continuousAt_const.mul continuousAt_subtype_val.sqrt).mul
            continuousAt_const)
      change Tendsto
        (fun y : Set.Icc (0 : ℝ) T =>
          ((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
            Real.sqrt y.1 * (1 - r) ^ (-(1 / 2 : ℝ)))
        (nhds z)
        (nhds (((2 / Real.sqrt (4 * Real.pi)) * (M ^ p.m * M ^ p.γ)) *
          Real.sqrt z.1 * (1 - r) ^ (-(1 / 2 : ℝ)))) at hcont
      simpa [hz] using hcont
  · have hzpos : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz)
    have hlag : 0 < z.1 - z.1 * r := by
      rw [show z.1 - z.1 * r = z.1 * (1 - r) by ring]
      exact mul_pos hzpos (sub_pos.mpr hr)
    have htime : Continuous
        (fun y : Set.Icc (0 : ℝ) T => y.1 * r) :=
      continuous_subtype_val.mul continuous_const
    have hpair : ContinuousAt
        (fun y : Set.Icc (0 : ℝ) T =>
          (y.1 - y.1 * r,
            wholeLineCauchyFluxSourceTrajectory p hM hT U (y.1 * r))) z := by
      exact (continuous_subtype_val.sub htime).continuousAt.prodMk
        ((wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U).comp
          htime).continuousAt
    have hop : ContinuousAt
        (fun y : Set.Icc (0 : ℝ) T =>
          wholeLineCauchyGradientBUCIntegrand
            p hM hT U y.1 (y.1 * r)) z := by
      change ContinuousAt
        (fun y : Set.Icc (0 : ℝ) T =>
          wholeLineCauchyHeatGradientBUCTotal
            (y.1 - y.1 * r)
            (wholeLineCauchyFluxSourceTrajectory p hM hT U (y.1 * r))) z
      exact ContinuousAt.comp'
        (f := fun y : Set.Icc (0 : ℝ) T =>
          (y.1 - y.1 * r,
            wholeLineCauchyFluxSourceTrajectory p hM hT U (y.1 * r)))
        (wholeLineCauchyHeatGradientBUCTotal_jointContinuousAt_of_pos hlag
          (wholeLineCauchyFluxSourceTrajectory p hM hT U (z.1 * r)))
        hpair
    change ContinuousAt
      (fun y : Set.Icc (0 : ℝ) T => y.1 •
        wholeLineCauchyGradientBUCIntegrand p hM hT U y.1 (y.1 * r)) z
    exact continuousAt_subtype_val.smul hop

theorem wholeLineCauchyGradientDuhamelBUC_continuous
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    Continuous
      (fun z : Set.Icc (0 : ℝ) T =>
        wholeLineCauchyGradientDuhamelBUC p hM hT U z.1) := by
  let C : ℝ := ((2 / Real.sqrt (4 * Real.pi)) *
    (M ^ p.m * M ^ p.γ)) * Real.sqrt T
  have hbound_int : IntervalIntegrable
      (fun r : ℝ => C * (1 - r) ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half 1).const_mul C
  have hne : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  apply continuous_singular_duhamel_banach
    (F := fun z s => wholeLineCauchyGradientBUCIntegrand
      p hM hT U z.1 s)
    (τ := fun z : Set.Icc (0 : ℝ) T => z.1)
    (bound := fun r => C * (1 - r) ^ (-(1 / 2 : ℝ)))
  · intro z
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact ((wholeLineCauchyGradientBUCRescaled_continuousOn_Iio
      p hM hT U z).mono Set.Ioo_subset_Iio_self).aestronglyMeasurable
        measurableSet_Ioo
  · exact hbound_int
  · intro z
    filter_upwards [hne] with r hrne hrmem
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hrmem
    have hr : r < 1 := lt_of_le_of_ne hrmem.2 hrne
    simpa [wholeLineCauchyGradientBUCRescaled, C] using
      wholeLineCauchyGradientBUCRescaled_norm_le p hM hT U hr z
  · filter_upwards [hne] with r hrne hrmem
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hrmem
    have hr : r < 1 := lt_of_le_of_ne hrmem.2 hrne
    simpa [wholeLineCauchyGradientBUCRescaled] using
      wholeLineCauchyGradientBUCRescaled_continuous p hM hT U hr

def wholeLineCauchyValueBUCRescaled
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (r : ℝ)
    (z : Set.Icc (0 : ℝ) T) : WholeLineBUC :=
  z.1 • wholeLineCauchyValueBUCIntegrand p hM hT U z.1 (z.1 * r)

theorem wholeLineCauchyValueBUCRescaled_continuousOn_Iio
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (z : Set.Icc (0 : ℝ) T) :
    ContinuousOn
      (fun r => wholeLineCauchyValueBUCRescaled p hM hT U r z)
      (Set.Iio 1) := by
  by_cases hz : z.1 = 0
  · have heq : (fun r => wholeLineCauchyValueBUCRescaled p hM hT U r z) =
        fun _ : ℝ => (0 : WholeLineBUC) := by
      funext r
      simp [wholeLineCauchyValueBUCRescaled, hz]
    rw [heq]
    exact continuousOn_const
  · have hzpos : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz)
    intro r hrmem
    have hr : r < 1 := hrmem
    have hlag : 0 < z.1 - z.1 * r := by
      rw [show z.1 - z.1 * r = z.1 * (1 - r) by ring]
      exact mul_pos hzpos (sub_pos.mpr hr)
    have htime : ContinuousAt (fun q : ℝ => z.1 * q) r :=
      continuousAt_const.mul continuousAt_id
    have hpair : ContinuousAt
        (fun q : ℝ =>
          (z.1 - z.1 * q,
            wholeLineCauchyReactionSourceTrajectory p hM hT U (z.1 * q))) r := by
      exact (continuousAt_const.sub htime).prodMk
        ((wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U).continuousAt.comp'
          htime)
    have hop : ContinuousAt
        (fun q : ℝ => wholeLineCauchyValueBUCIntegrand
          p hM hT U z.1 (z.1 * q)) r := by
      change ContinuousAt
        (fun q : ℝ => wholeLineCauchyHeatBUCTotal
          (z.1 - z.1 * q)
          (wholeLineCauchyReactionSourceTrajectory p hM hT U (z.1 * q))) r
      exact ContinuousAt.comp'
        (f := fun q : ℝ =>
          (z.1 - z.1 * q,
            wholeLineCauchyReactionSourceTrajectory p hM hT U (z.1 * q)))
        (wholeLineCauchyHeatBUCTotal_jointContinuousAt_of_pos hlag
          (wholeLineCauchyReactionSourceTrajectory p hM hT U (z.1 * r)))
        hpair
    exact (continuousAt_const.smul hop).continuousWithinAt

theorem wholeLineCauchyValueBUCRescaled_norm_le_time
    (p : CMParams) {M T r : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hr : r ≤ 1)
    (z : Set.Icc (0 : ℝ) T) :
    ‖wholeLineCauchyValueBUCRescaled p hM hT U r z‖ ≤
      z.1 * (M + M * (1 + M ^ p.α)) := by
  have hsr : z.1 * r ≤ z.1 :=
    mul_le_of_le_one_right z.2.1 hr
  unfold wholeLineCauchyValueBUCRescaled
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg z.2.1]
  exact mul_le_mul_of_nonneg_left
    (wholeLineCauchyValueBUCIntegrand_norm_le p hM hT U hsr) z.2.1

theorem wholeLineCauchyValueBUCRescaled_norm_le
    (p : CMParams) {M T r : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hr : r ≤ 1)
    (z : Set.Icc (0 : ℝ) T) :
    ‖wholeLineCauchyValueBUCRescaled p hM hT U r z‖ ≤
      T * (M + M * (1 + M ^ p.α)) := by
  have hC : 0 ≤ M + M * (1 + M ^ p.α) := by positivity
  exact (wholeLineCauchyValueBUCRescaled_norm_le_time
    p hM hT U hr z).trans (mul_le_mul_of_nonneg_right z.2.2 hC)

theorem wholeLineCauchyValueBUCRescaled_continuous
    (p : CMParams) {M T r : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hr : r < 1) :
    Continuous
      (fun z : Set.Icc (0 : ℝ) T =>
        wholeLineCauchyValueBUCRescaled p hM hT U r z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.1 = 0
  · have hzero : wholeLineCauchyValueBUCRescaled p hM hT U r z = 0 := by
      simp [wholeLineCauchyValueBUCRescaled, hz]
    change Tendsto
      (fun y : Set.Icc (0 : ℝ) T =>
        wholeLineCauchyValueBUCRescaled p hM hT U r y)
      (nhds z) (nhds (wholeLineCauchyValueBUCRescaled p hM hT U r z))
    rw [hzero]
    refine tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero'
        (g := fun y : Set.Icc (0 : ℝ) T =>
          y.1 * (M + M * (1 + M ^ p.α)))
        (Eventually.of_forall fun _ => dist_nonneg) ?_ ?_)
    · exact Eventually.of_forall fun y => by
        rw [WholeLineBUC.dist_zero_eq_norm]
        exact wholeLineCauchyValueBUCRescaled_norm_le_time
          p hM hT U hr.le y
    · have hcont : ContinuousAt
          (fun y : Set.Icc (0 : ℝ) T =>
            y.1 * (M + M * (1 + M ^ p.α))) z :=
          continuousAt_subtype_val.mul continuousAt_const
      change Tendsto
        (fun y : Set.Icc (0 : ℝ) T =>
          y.1 * (M + M * (1 + M ^ p.α)))
        (nhds z)
        (nhds (z.1 * (M + M * (1 + M ^ p.α)))) at hcont
      simpa [hz] using hcont
  · have hzpos : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz)
    have hlag : 0 < z.1 - z.1 * r := by
      rw [show z.1 - z.1 * r = z.1 * (1 - r) by ring]
      exact mul_pos hzpos (sub_pos.mpr hr)
    have htime : Continuous
        (fun y : Set.Icc (0 : ℝ) T => y.1 * r) :=
      continuous_subtype_val.mul continuous_const
    have hpair : ContinuousAt
        (fun y : Set.Icc (0 : ℝ) T =>
          (y.1 - y.1 * r,
            wholeLineCauchyReactionSourceTrajectory p hM hT U (y.1 * r))) z := by
      exact (continuous_subtype_val.sub htime).continuousAt.prodMk
        ((wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U).comp
          htime).continuousAt
    have hop : ContinuousAt
        (fun y : Set.Icc (0 : ℝ) T =>
          wholeLineCauchyValueBUCIntegrand
            p hM hT U y.1 (y.1 * r)) z := by
      change ContinuousAt
        (fun y : Set.Icc (0 : ℝ) T =>
          wholeLineCauchyHeatBUCTotal
            (y.1 - y.1 * r)
            (wholeLineCauchyReactionSourceTrajectory p hM hT U (y.1 * r))) z
      exact ContinuousAt.comp'
        (f := fun y : Set.Icc (0 : ℝ) T =>
          (y.1 - y.1 * r,
            wholeLineCauchyReactionSourceTrajectory p hM hT U (y.1 * r)))
        (wholeLineCauchyHeatBUCTotal_jointContinuousAt_of_pos hlag
          (wholeLineCauchyReactionSourceTrajectory p hM hT U (z.1 * r)))
        hpair
    change ContinuousAt
      (fun y : Set.Icc (0 : ℝ) T => y.1 •
        wholeLineCauchyValueBUCIntegrand p hM hT U y.1 (y.1 * r)) z
    exact continuousAt_subtype_val.smul hop

theorem wholeLineCauchyValueDuhamelBUC_continuous
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    Continuous
      (fun z : Set.Icc (0 : ℝ) T =>
        wholeLineCauchyValueDuhamelBUC p hM hT U z.1) := by
  let C : ℝ := T * (M + M * (1 + M ^ p.α))
  have hne : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  apply continuous_singular_duhamel_banach
    (F := fun z s => wholeLineCauchyValueBUCIntegrand p hM hT U z.1 s)
    (τ := fun z : Set.Icc (0 : ℝ) T => z.1)
    (bound := fun _ => C)
  · intro z
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact ((wholeLineCauchyValueBUCRescaled_continuousOn_Iio
      p hM hT U z).mono Set.Ioo_subset_Iio_self).aestronglyMeasurable
        measurableSet_Ioo
  · exact _root_.intervalIntegrable_const
  · intro z
    filter_upwards [hne] with r hrne hrmem
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hrmem
    have hr : r < 1 := lt_of_le_of_ne hrmem.2 hrne
    simpa [wholeLineCauchyValueBUCRescaled, C] using
      wholeLineCauchyValueBUCRescaled_norm_le p hM hT U hr.le z
  · filter_upwards [hne] with r hrne hrmem
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hrmem
    have hr : r < 1 := lt_of_le_of_ne hrmem.2 hrne
    simpa [wholeLineCauchyValueBUCRescaled] using
      wholeLineCauchyValueBUCRescaled_continuous p hM hT U hr

section WholeLineCauchyBUCDuhamelContinuityAxiomAudit

#print axioms continuous_singular_duhamel_banach
#print axioms wholeLineCauchyGradientDuhamelBUC_continuous
#print axioms wholeLineCauchyValueDuhamelBUC_continuous

end WholeLineCauchyBUCDuhamelContinuityAxiomAudit

end ShenWork.Paper1
