import ShenWork.Paper1.WholeLineWeightedRegularityHeatGradientTimeModulus
import ShenWork.Paper1.WholeLineWeightedRegularityDuhamelHolder
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Square-root time modulus for weighted heat-gradient Duhamel histories

For two ordered times `s < t`, split the old history at
`m = s - (t - s)`.  The two recent pieces use the integrable
`r^(-1/2)` heat-gradient singularity, while the far piece uses the
positive-lag `r^(-3/2)` time modulus.  Both contributions are of order
`sqrt (t - s)`.
-/

/-- A horizon-uniform coefficient for the exact-weight heat-gradient
`r^(-1/2)` estimate. -/
def weightedMovingHeatGradientHorizonConst (eta c H : ℝ) : ℝ :=
  Real.exp (|eta ^ 2 - c * eta| * H) / Real.sqrt Real.pi

theorem weightedMovingHeatGradientHorizonConst_nonneg
    (eta c H : ℝ) :
    0 ≤ weightedMovingHeatGradientHorizonConst eta c H := by
  unfold weightedMovingHeatGradientHorizonConst
  positivity

/-- A horizon-uniform coefficient for the positive-lag time difference of
the weighted heat gradient. -/
def weightedMovingHeatGradientTimeHorizonConst (eta c H : ℝ) : ℝ :=
  weightedMovingHeatGradientHorizonConst eta c H *
    weightedMovingHeatGeneratorHorizonConst eta c H *
    (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / 2 : ℝ) ^ (-(1 : ℝ))

theorem weightedMovingHeatGradientTimeHorizonConst_nonneg
    {eta c H : ℝ} (hH : 0 ≤ H) :
    0 ≤ weightedMovingHeatGradientTimeHorizonConst eta c H := by
  unfold weightedMovingHeatGradientTimeHorizonConst
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (weightedMovingHeatGradientHorizonConst_nonneg eta c H)
        (weightedMovingHeatGeneratorHorizonConst_nonneg hH))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _)

theorem weightedMovingHeatGradientMass_le_horizon_rpow_neg_half
    {eta c H r : ℝ} (hr : 0 < r) (hrH : r ≤ H) :
    weightedMovingHeatGrowth eta c r / Real.sqrt (Real.pi * r) ≤
      weightedMovingHeatGradientHorizonConst eta c H *
        r ^ (-(1 / 2 : ℝ)) := by
  have hgrowth : weightedMovingHeatGrowth eta c r ≤
      Real.exp (|eta ^ 2 - c * eta| * H) :=
    weightedMovingHeatGrowth_le_exp_abs_mul_of_mem_Icc ⟨hr.le, hrH⟩
  have hsqrtPi : 0 < Real.sqrt Real.pi :=
    Real.sqrt_pos.mpr Real.pi_pos
  have hsqrtR : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  calc
    weightedMovingHeatGrowth eta c r / Real.sqrt (Real.pi * r) ≤
        Real.exp (|eta ^ 2 - c * eta| * H) /
          Real.sqrt (Real.pi * r) := by gcongr
    _ = (Real.exp (|eta ^ 2 - c * eta| * H) / Real.sqrt Real.pi) *
          r ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_mul Real.pi_pos.le,
        Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow]
      field_simp [ne_of_gt hsqrtPi, ne_of_gt hsqrtR]
    _ = weightedMovingHeatGradientHorizonConst eta c H *
          r ^ (-(1 / 2 : ℝ)) := rfl

/-- Horizon-uniform `r^(-1/2)` bound for the totalized heat gradient. -/
theorem weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half
    {eta c H r : ℝ} (hr0 : 0 ≤ r) (hrH : r ≤ H)
    (Z : WholeLineRealL2) :
    ‖weightedMovingHeatL2Gradient eta c r Z‖ ≤
      weightedMovingHeatGradientHorizonConst eta c H *
        r ^ (-(1 / 2 : ℝ)) * ‖Z‖ := by
  rcases hr0.eq_or_lt with hzero | hr
  · rw [← hzero, weightedMovingHeatL2Gradient_zero,
      ContinuousLinearMap.zero_apply, norm_zero]
    exact mul_nonneg
      (mul_nonneg
        (weightedMovingHeatGradientHorizonConst_nonneg eta c H)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) _))
      (norm_nonneg Z)
  · rw [weightedMovingHeatL2Gradient_of_pos hr]
    have hraw := weightedMovingHeatGradientL2CLM_apply_norm_le
      (eta := eta) (c := c) hr Z
    have hgrowth : weightedMovingHeatGrowth eta c r ≤
        Real.exp (|eta ^ 2 - c * eta| * H) :=
      weightedMovingHeatGrowth_le_exp_abs_mul_of_mem_Icc ⟨hr.le, hrH⟩
    have hsqrtPi : 0 < Real.sqrt Real.pi :=
      Real.sqrt_pos.mpr Real.pi_pos
    have hsqrtR : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    calc
      ‖weightedMovingHeatGradientL2CLM eta c r hr Z‖ ≤
          (weightedMovingHeatGrowth eta c r /
            Real.sqrt (Real.pi * r)) * ‖Z‖ := hraw
      _ = (weightedMovingHeatGrowth eta c r / Real.sqrt Real.pi) *
            r ^ (-(1 / 2 : ℝ)) * ‖Z‖ := by
        rw [Real.sqrt_mul Real.pi_pos.le,
          Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow]
        field_simp [ne_of_gt hsqrtPi, ne_of_gt hsqrtR]
      _ ≤ (Real.exp (|eta ^ 2 - c * eta| * H) / Real.sqrt Real.pi) *
            r ^ (-(1 / 2 : ℝ)) * ‖Z‖ := by
        gcongr
      _ = weightedMovingHeatGradientHorizonConst eta c H *
            r ^ (-(1 / 2 : ℝ)) * ‖Z‖ := rfl

/-- Horizon-uniform positive-lag time modulus in the native
`h * r^(-3/2)` form. -/
theorem weightedMovingHeatL2Gradient_sub_apply_norm_le_rpow_neg_three_half
    {eta c H r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hrhH : r + h ≤ H)
    (Z : WholeLineRealL2) :
    ‖weightedMovingHeatL2Gradient eta c (r + h) Z -
        weightedMovingHeatL2Gradient eta c r Z‖ ≤
      weightedMovingHeatGradientTimeHorizonConst eta c H * h *
        r ^ (-(3 / 2 : ℝ)) * ‖Z‖ := by
  have hrs : 0 < r / 2 := by linarith
  have hH : 0 ≤ H := hr.le.trans (le_add_of_nonneg_right hh) |>.trans hrhH
  have hrsH : r / 2 ≤ H := by linarith
  have hmass := weightedMovingHeatGradientMass_le_horizon_rpow_neg_half
    (eta := eta) (c := c) hrs hrsH
  have hraw :=
    weightedMovingHeatL2Gradient_sub_apply_norm_le_of_positive_lag
      (eta := eta) (c := c) hr hh hrhH Z
  have hgen : 0 ≤ weightedMovingHeatGeneratorHorizonConst eta c H :=
    weightedMovingHeatGeneratorHorizonConst_nonneg hH
  have hinv : 0 ≤ (r / 2)⁻¹ := inv_nonneg.mpr hrs.le
  have hhalf :
      (r / 2) ^ (-(1 / 2 : ℝ)) =
        (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
          r ^ (-(1 / 2 : ℝ)) := by
    rw [show r / 2 = (1 / 2 : ℝ) * r by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hr.le]
  have hone :
      (r / 2) ^ (-(1 : ℝ)) =
        (1 / 2 : ℝ) ^ (-(1 : ℝ)) * r ^ (-(1 : ℝ)) := by
    rw [show r / 2 = (1 / 2 : ℝ) * r by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hr.le]
  have hcombine :
      r ^ (-(1 / 2 : ℝ)) * r ^ (-(1 : ℝ)) =
        r ^ (-(3 / 2 : ℝ)) := by
    calc
      r ^ (-(1 / 2 : ℝ)) * r ^ (-(1 : ℝ)) =
          r ^ (-(1 / 2 : ℝ) + -(1 : ℝ)) :=
        (Real.rpow_add hr _ _).symm
      _ = r ^ (-(3 / 2 : ℝ)) := by congr 1; ring
  calc
    ‖weightedMovingHeatL2Gradient eta c (r + h) Z -
        weightedMovingHeatL2Gradient eta c r Z‖ ≤
        (weightedMovingHeatGrowth eta c (r / 2) /
            Real.sqrt (Real.pi * (r / 2)) *
          weightedMovingHeatGeneratorHorizonConst eta c H *
            (r / 2)⁻¹ * h) * ‖Z‖ := hraw
    _ ≤ ((weightedMovingHeatGradientHorizonConst eta c H *
            (r / 2) ^ (-(1 / 2 : ℝ))) *
          weightedMovingHeatGeneratorHorizonConst eta c H *
            (r / 2)⁻¹ * h) * ‖Z‖ := by
      gcongr
    _ = weightedMovingHeatGradientTimeHorizonConst eta c H * h *
          r ^ (-(3 / 2 : ℝ)) * ‖Z‖ := by
      rw [show (r / 2)⁻¹ = (r / 2) ^ (-(1 : ℝ)) by
        exact (Real.rpow_neg_one (r / 2)).symm,
        hhalf, hone]
      calc
        ((weightedMovingHeatGradientHorizonConst eta c H *
                ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) *
                  r ^ (-(1 / 2 : ℝ)))) *
              weightedMovingHeatGeneratorHorizonConst eta c H *
                ((1 / 2 : ℝ) ^ (-(1 : ℝ)) *
                  r ^ (-(1 : ℝ))) * h) * ‖Z‖ =
            weightedMovingHeatGradientTimeHorizonConst eta c H * h *
              (r ^ (-(1 / 2 : ℝ)) * r ^ (-(1 : ℝ))) * ‖Z‖ := by
          unfold weightedMovingHeatGradientTimeHorizonConst
          ring
        _ = _ := by rw [hcombine]

/-- Exact mass of a translated inverse-square-root singularity. -/
theorem intervalIntegral_sub_rpow_neg_half_eq_two_sqrt
    {a b : ℝ} (hab : a ≤ b) :
    (∫ q in a..b, (b - q) ^ (-(1 / 2 : ℝ))) =
      2 * Real.sqrt (b - a) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) b]
  rw [sub_self]
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  rw [show (-(1 / 2 : ℝ) + 1) = (1 / 2 : ℝ) by ring,
    Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero,
    show (b - a) ^ (1 / 2 : ℝ) = Real.sqrt (b - a) by
      exact (Real.sqrt_eq_rpow (b - a)).symm]
  ring

/-- Integrability of a translated inverse-square-root singularity. -/
theorem intervalIntegrable_sub_rpow_neg_half_between
    (a b : ℝ) :
    IntervalIntegrable (fun q : ℝ => (b - q) ^ (-(1 / 2 : ℝ)))
      volume a b := by
  have hbase : IntervalIntegrable
      (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) volume (b - b) (b - a) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hcomp := (hbase.comp_sub_left b).symm
  simpa only [sub_sub_cancel, sub_self, sub_zero] using hcomp

/-- The far-history `r^(-3/2)` mass is controlled by its lower lag. -/
theorem intervalIntegral_sub_rpow_neg_three_half_le
    {a s h : ℝ} (hh : 0 < h) (ham : a ≤ s - h) :
    (∫ q in a..s - h, (s - q) ^ (-(3 / 2 : ℝ))) ≤
      2 * h ^ (-(1 / 2 : ℝ)) := by
  have hupper : 0 < s - a := by linarith
  rw [intervalIntegral.integral_comp_sub_left
    (fun r : ℝ => r ^ (-(3 / 2 : ℝ))) s]
  have hzero : (0 : ℝ) ∉ Set.uIcc h (s - a) := by
    intro hz
    rw [Set.mem_uIcc] at hz
    rcases hz with hz | hz <;> linarith
  rw [show s - (s - h) = h by ring]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  rw [show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by ring]
  have hup : 0 ≤ (s - a) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hupper.le _
  nlinarith

/-- The far-history `r^(-3/2)` profile is integrable away from zero lag. -/
theorem intervalIntegrable_sub_rpow_neg_three_half_far
    {a s h : ℝ} (hh : 0 < h) (ham : a ≤ s - h) :
    IntervalIntegrable (fun q : ℝ => (s - q) ^ (-(3 / 2 : ℝ)))
      volume a (s - h) := by
  have hupper : 0 < s - a := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc h (s - a) := by
    intro hz
    rw [Set.mem_uIcc] at hz
    rcases hz with hz | hz <;> linarith
  have hbase : IntervalIntegrable
      (fun r : ℝ => r ^ (-(3 / 2 : ℝ))) volume h (s - a) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hcomp := (hbase.comp_sub_left s).symm
  simpa only [sub_sub_cancel] using hcomp

theorem mul_rpow_neg_half_eq_sqrt {h : ℝ} (hh : 0 < h) :
    h * h ^ (-(1 / 2 : ℝ)) = Real.sqrt h := by
  rw [Real.rpow_neg hh.le, ← Real.sqrt_eq_rpow]
  have hn : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hh)
  have hs : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  calc
    h * (Real.sqrt h)⁻¹ =
        (Real.sqrt h * Real.sqrt h) * (Real.sqrt h)⁻¹ := by rw [hs]
    _ = Real.sqrt h := by field_simp

/-- Bochner integration of a translated inverse-square-root majorant. -/
theorem wholeLineRealL2_intervalIntegral_norm_le_sub_rpow_neg_half
    {a b C : ℝ} (hab : a ≤ b)
    {Z : ℝ → WholeLineRealL2}
    (hZ : IntervalIntegrable Z volume a b)
    (hmajor : ∀ q ∈ Set.Icc a b,
      ‖Z q‖ ≤ C * (b - q) ^ (-(1 / 2 : ℝ))) :
    ‖∫ q in a..b, Z q‖ ≤ 2 * C * Real.sqrt (b - a) := by
  let g : ℝ → ℝ := fun q => C * (b - q) ^ (-(1 / 2 : ℝ))
  have hg : IntervalIntegrable g volume a b :=
    (intervalIntegrable_sub_rpow_neg_half_between a b).const_mul C
  have hbound := wholeLineRealL2_intervalIntegral_norm_le_of_majorant
    hab hZ hg hmajor
  calc
    ‖∫ q in a..b, Z q‖ ≤ ∫ q in a..b, g q := hbound
    _ = C * (∫ q in a..b, (b - q) ^ (-(1 / 2 : ℝ))) := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]
    _ = 2 * C * Real.sqrt (b - a) := by
      rw [intervalIntegral_sub_rpow_neg_half_eq_two_sqrt hab]
      ring

/-- Bochner integration of the far-history `r^(-3/2)` majorant. -/
theorem wholeLineRealL2_intervalIntegral_norm_le_sub_rpow_neg_three_half
    {a s h C : ℝ} (hh : 0 < h) (ham : a ≤ s - h) (hC : 0 ≤ C)
    {Z : ℝ → WholeLineRealL2}
    (hZ : IntervalIntegrable Z volume a (s - h))
    (hmajor : ∀ q ∈ Set.Icc a (s - h),
      ‖Z q‖ ≤ C * (s - q) ^ (-(3 / 2 : ℝ))) :
    ‖∫ q in a..s - h, Z q‖ ≤
      2 * C * h ^ (-(1 / 2 : ℝ)) := by
  let g : ℝ → ℝ := fun q => C * (s - q) ^ (-(3 / 2 : ℝ))
  have hg : IntervalIntegrable g volume a (s - h) :=
    (intervalIntegrable_sub_rpow_neg_three_half_far hh ham).const_mul C
  have hbound := wholeLineRealL2_intervalIntegral_norm_le_of_majorant
    ham hZ hg hmajor
  calc
    ‖∫ q in a..s - h, Z q‖ ≤ ∫ q in a..s - h, g q := hbound
    _ = C * (∫ q in a..s - h,
        (s - q) ^ (-(3 / 2 : ℝ))) := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]
    _ ≤ C * (2 * h ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (intervalIntegral_sub_rpow_neg_three_half_le hh ham) hC
    _ = 2 * C * h ^ (-(1 / 2 : ℝ)) := by ring

/-- Ordered-time square-root modulus for a weighted heat-gradient Duhamel
history.  The hypotheses expose only the two actual Bochner integrability
statements and one uniform forcing bound. -/
theorem weightedMovingHeatL2Gradient_duhamel_sub_norm_le_sqrt
    {eta c a R s t K : ℝ}
    (haR : a < R) (hK : 0 ≤ K)
    (has : a ≤ s) (hst : s ≤ t) (htR : t ≤ R)
    (hstep : 0 < t - s) (hfar : a ≤ s - (t - s))
    {F : ℝ → WholeLineRealL2}
    (hF : ∀ q ∈ Set.Icc a R, ‖F q‖ ≤ K)
    (hTint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (t - q) (F q))
      volume a t)
    (hSint : IntervalIntegrable
      (fun q => weightedMovingHeatL2Gradient eta c (s - q) (F q))
      volume a s) :
    ‖(∫ q in a..t,
          weightedMovingHeatL2Gradient eta c (t - q) (F q)) -
        ∫ q in a..s,
          weightedMovingHeatL2Gradient eta c (s - q) (F q)‖ ≤
      (5 * weightedMovingHeatGradientHorizonConst eta c (R - a) * K +
        2 * weightedMovingHeatGradientTimeHorizonConst eta c (R - a) * K) *
        Real.sqrt (t - s) := by
  let h : ℝ := t - s
  let m : ℝ := s - h
  let A : ℝ := weightedMovingHeatGradientHorizonConst eta c (R - a)
  let B : ℝ := weightedMovingHeatGradientTimeHorizonConst eta c (R - a)
  let Tfun : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Gradient eta c (t - q) (F q)
  let Sfun : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Gradient eta c (s - q) (F q)
  let Old : ℝ → WholeLineRealL2 := fun q => Tfun q - Sfun q
  have hat : a ≤ t := has.trans hst
  have haRle : a ≤ R := haR.le
  have hsR : s ≤ R := hst.trans htR
  have hH : 0 ≤ R - a := sub_nonneg.mpr haRle
  have hpos : 0 < h := by simpa only [h] using hstep
  have ham : a ≤ m := by simpa only [m, h] using hfar
  have hms : m ≤ s := sub_le_self _ hpos.le
  have hA : 0 ≤ A := by
    exact weightedMovingHeatGradientHorizonConst_nonneg eta c (R - a)
  have hB : 0 ≤ B := by
    exact weightedMovingHeatGradientTimeHorizonConst_nonneg hH
  have hT_as : IntervalIntegrable Tfun volume a s := by
    apply hTint.mono_set
    rw [Set.uIcc_of_le hat, Set.uIcc_of_le has]
    exact Set.Icc_subset_Icc_right hst
  have hT_st : IntervalIntegrable Tfun volume s t := by
    apply hTint.mono_set
    rw [Set.uIcc_of_le hat, Set.uIcc_of_le hst]
    exact Set.Icc_subset_Icc_left has
  have hT_ms : IntervalIntegrable Tfun volume m s := by
    apply hT_as.mono_set
    rw [Set.uIcc_of_le has, Set.uIcc_of_le hms]
    exact Set.Icc_subset_Icc_left ham
  have hS_ms : IntervalIntegrable Sfun volume m s := by
    apply hSint.mono_set
    rw [Set.uIcc_of_le has, Set.uIcc_of_le hms]
    exact Set.Icc_subset_Icc_left ham
  have hOld : IntervalIntegrable Old volume a s := hT_as.sub hSint
  have hOld_far : IntervalIntegrable Old volume a m := by
    apply hOld.mono_set
    rw [Set.uIcc_of_le has, Set.uIcc_of_le ham]
    exact Set.Icc_subset_Icc_right hms
  have hOld_near : IntervalIntegrable Old volume m s := hT_ms.sub hS_ms
  have hdecomp :
      (∫ q in a..t, Tfun q) - ∫ q in a..s, Sfun q =
        ((∫ q in a..m, Old q) + ∫ q in m..s, Old q) +
          ∫ q in s..t, Tfun q := by
    have hTsplit :=
      intervalIntegral.integral_add_adjacent_intervals hT_as hT_st
    have hOldSplit :=
      intervalIntegral.integral_add_adjacent_intervals hOld_far hOld_near
    rw [← hTsplit, hOldSplit,
      intervalIntegral.integral_sub hT_as hSint]
    abel
  have hnew_point : ∀ q ∈ Set.Icc s t,
      ‖Tfun q‖ ≤ A * K * (t - q) ^ (-(1 / 2 : ℝ)) := by
    intro q hq
    have hqmem : q ∈ Set.Icc a R :=
      ⟨has.trans hq.1, hq.2.trans htR⟩
    have hlag0 : 0 ≤ t - q := sub_nonneg.mpr hq.2
    have hlagH : t - q ≤ R - a := by linarith [hqmem.1, htR]
    calc
      ‖Tfun q‖ ≤ A * (t - q) ^ (-(1 / 2 : ℝ)) * ‖F q‖ := by
        dsimp only [Tfun, A]
        exact weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half
          hlag0 hlagH (F q)
      _ ≤ A * (t - q) ^ (-(1 / 2 : ℝ)) * K := by
        exact mul_le_mul_of_nonneg_left (hF q hqmem)
          (mul_nonneg hA (Real.rpow_nonneg hlag0 _))
      _ = A * K * (t - q) ^ (-(1 / 2 : ℝ)) := by ring
  have hnew_bound :
      ‖∫ q in s..t, Tfun q‖ ≤ 2 * A * K * Real.sqrt h := by
    have hraw := wholeLineRealL2_intervalIntegral_norm_le_sub_rpow_neg_half
      hst hT_st hnew_point
    simpa only [h, mul_assoc] using hraw
  have hTnear_point : ∀ q ∈ Set.Icc m s,
      ‖Tfun q‖ ≤ A * h ^ (-(1 / 2 : ℝ)) * K := by
    intro q hq
    have hqmem : q ∈ Set.Icc a R :=
      ⟨ham.trans hq.1, hq.2.trans hsR⟩
    have hlag0 : 0 < t - q := by
      have : h ≤ t - q := by dsimp only [h]; linarith [hq.2]
      exact hpos.trans_le this
    have hlagH : t - q ≤ R - a := by linarith [hqmem.1, htR]
    have hpow : (t - q) ^ (-(1 / 2 : ℝ)) ≤
        h ^ (-(1 / 2 : ℝ)) := by
      apply Real.rpow_le_rpow_of_nonpos hpos
      · dsimp only [h]
        linarith [hq.2]
      · norm_num
    calc
      ‖Tfun q‖ ≤ A * (t - q) ^ (-(1 / 2 : ℝ)) * ‖F q‖ := by
        dsimp only [Tfun, A]
        exact weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half
          hlag0.le hlagH (F q)
      _ ≤ A * h ^ (-(1 / 2 : ℝ)) * ‖F q‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hA) (norm_nonneg _)
      _ ≤ A * h ^ (-(1 / 2 : ℝ)) * K := by
        exact mul_le_mul_of_nonneg_left (hF q hqmem)
          (mul_nonneg hA (Real.rpow_nonneg hpos.le _))
  have hTnear_bound :
      ‖∫ q in m..s, Tfun q‖ ≤ A * K * Real.sqrt h := by
    have hraw := intervalIntegral_norm_le_const_mul_sub hms hTnear_point
    calc
      ‖∫ q in m..s, Tfun q‖ ≤
          (A * h ^ (-(1 / 2 : ℝ)) * K) * (s - m) := hraw
      _ = A * K * Real.sqrt h := by
        rw [show s - m = h by dsimp only [m]; ring,
          ← mul_rpow_neg_half_eq_sqrt hpos]
        ring
  have hSnear_point : ∀ q ∈ Set.Icc m s,
      ‖Sfun q‖ ≤ A * K * (s - q) ^ (-(1 / 2 : ℝ)) := by
    intro q hq
    have hqmem : q ∈ Set.Icc a R :=
      ⟨ham.trans hq.1, hq.2.trans hsR⟩
    have hlag0 : 0 ≤ s - q := sub_nonneg.mpr hq.2
    have hlagH : s - q ≤ R - a := by linarith [hqmem.1, hsR]
    calc
      ‖Sfun q‖ ≤ A * (s - q) ^ (-(1 / 2 : ℝ)) * ‖F q‖ := by
        dsimp only [Sfun, A]
        exact weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half
          hlag0 hlagH (F q)
      _ ≤ A * (s - q) ^ (-(1 / 2 : ℝ)) * K := by
        exact mul_le_mul_of_nonneg_left (hF q hqmem)
          (mul_nonneg hA (Real.rpow_nonneg hlag0 _))
      _ = A * K * (s - q) ^ (-(1 / 2 : ℝ)) := by ring
  have hSnear_bound :
      ‖∫ q in m..s, Sfun q‖ ≤ 2 * A * K * Real.sqrt h := by
    have hraw := wholeLineRealL2_intervalIntegral_norm_le_sub_rpow_neg_half
      hms hS_ms hSnear_point
    simpa only [show s - m = h by dsimp only [m]; ring, mul_assoc] using hraw
  have hnear_bound :
      ‖∫ q in m..s, Old q‖ ≤ 3 * A * K * Real.sqrt h := by
    rw [intervalIntegral.integral_sub hT_ms hS_ms]
    calc
      ‖(∫ q in m..s, Tfun q) - ∫ q in m..s, Sfun q‖ ≤
          ‖∫ q in m..s, Tfun q‖ + ‖∫ q in m..s, Sfun q‖ :=
        norm_sub_le _ _
      _ ≤ A * K * Real.sqrt h + 2 * A * K * Real.sqrt h :=
        add_le_add hTnear_bound hSnear_bound
      _ = 3 * A * K * Real.sqrt h := by ring
  have hfar_point : ∀ q ∈ Set.Icc a m,
      ‖Old q‖ ≤ B * K * h * (s - q) ^ (-(3 / 2 : ℝ)) := by
    intro q hq
    have hr : 0 < s - q := by
      have : h ≤ s - q := by dsimp only [m] at hq; linarith [hq.2]
      exact hpos.trans_le this
    have hrH : (s - q) + h ≤ R - a := by
      dsimp only [h]
      linarith [hq.1, htR]
    have hqmem : q ∈ Set.Icc a R :=
      ⟨hq.1, hq.2.trans (hms.trans hsR)⟩
    have hgrad :=
      weightedMovingHeatL2Gradient_sub_apply_norm_le_rpow_neg_three_half
        (eta := eta) (c := c) hr hpos.le hrH (F q)
    calc
      ‖Old q‖ =
          ‖weightedMovingHeatL2Gradient eta c ((s - q) + h) (F q) -
            weightedMovingHeatL2Gradient eta c (s - q) (F q)‖ := by
        dsimp only [Old, Tfun, Sfun, h]
        congr 3
        ring
      _ ≤ B * h * (s - q) ^ (-(3 / 2 : ℝ)) * ‖F q‖ := by
        simpa only [B] using hgrad
      _ ≤ B * h * (s - q) ^ (-(3 / 2 : ℝ)) * K := by
        exact mul_le_mul_of_nonneg_left (hF q hqmem)
          (mul_nonneg
            (mul_nonneg hB hpos.le)
            (Real.rpow_nonneg hr.le _))
      _ = B * K * h * (s - q) ^ (-(3 / 2 : ℝ)) := by ring
  have hfar_bound :
      ‖∫ q in a..m, Old q‖ ≤ 2 * B * K * Real.sqrt h := by
    have hC : 0 ≤ B * K * h :=
      mul_nonneg (mul_nonneg hB hK) hpos.le
    have hraw :=
      wholeLineRealL2_intervalIntegral_norm_le_sub_rpow_neg_three_half
        hpos ham hC hOld_far hfar_point
    calc
      ‖∫ q in a..m, Old q‖ ≤
          2 * (B * K * h) * h ^ (-(1 / 2 : ℝ)) := by
        simpa only [m] using hraw
      _ = 2 * B * K * Real.sqrt h := by
        rw [show 2 * (B * K * h) * h ^ (-(1 / 2 : ℝ)) =
            2 * B * K * (h * h ^ (-(1 / 2 : ℝ))) by ring,
          mul_rpow_neg_half_eq_sqrt hpos]
  rw [show
      (∫ q in a..t,
          weightedMovingHeatL2Gradient eta c (t - q) (F q)) -
        ∫ q in a..s,
          weightedMovingHeatL2Gradient eta c (s - q) (F q) =
        (∫ q in a..t, Tfun q) - ∫ q in a..s, Sfun q by rfl,
    hdecomp]
  calc
    ‖((∫ q in a..m, Old q) + ∫ q in m..s, Old q) +
        ∫ q in s..t, Tfun q‖ ≤
      (‖∫ q in a..m, Old q‖ + ‖∫ q in m..s, Old q‖) +
          ‖∫ q in s..t, Tfun q‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2 * B * K * Real.sqrt h + 3 * A * K * Real.sqrt h) +
          2 * A * K * Real.sqrt h :=
      add_le_add (add_le_add hfar_bound hnear_bound) hnew_bound
    _ = (5 * weightedMovingHeatGradientHorizonConst eta c (R - a) * K +
          2 * weightedMovingHeatGradientTimeHorizonConst eta c (R - a) * K) *
        Real.sqrt (t - s) := by
      dsimp only [A, B, h]
      ring

section AxiomAudit

#print axioms weightedMovingHeatGradientMass_le_horizon_rpow_neg_half
#print axioms weightedMovingHeatL2Gradient_apply_norm_le_rpow_neg_half
#print axioms
  weightedMovingHeatL2Gradient_sub_apply_norm_le_rpow_neg_three_half
#print axioms intervalIntegral_sub_rpow_neg_half_eq_two_sqrt
#print axioms intervalIntegrable_sub_rpow_neg_half_between
#print axioms intervalIntegral_sub_rpow_neg_three_half_le
#print axioms intervalIntegrable_sub_rpow_neg_three_half_far
#print axioms mul_rpow_neg_half_eq_sqrt
#print axioms wholeLineRealL2_intervalIntegral_norm_le_sub_rpow_neg_half
#print axioms wholeLineRealL2_intervalIntegral_norm_le_sub_rpow_neg_three_half
#print axioms weightedMovingHeatL2Gradient_duhamel_sub_norm_le_sqrt

end AxiomAudit

end ShenWork.Paper1
