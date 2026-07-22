import ShenWork.Paper1.WholeLineChiLargeGradientBound
import ShenWork.PDE.RestartedMildSmoothing
import ShenWork.PDE.IntervalFullKernelGradientLinfty

/-!
# Weighted whole-line `L² → L∞` gradient smoothing

This is the Stage-3 semigroup estimate adapted directly to the translated
uniformly-local moment.  Splitting the localizing weight symmetrically between
the source and the Gaussian derivative avoids importing interval estimates.
-/

open Filter MeasureTheory Real Set
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper1

/-- Completing the square leaves half of the Gaussian decay available for
integration. -/
theorem linear_abs_sub_quadratic_le
    {t κ z : ℝ} (ht : 0 < t) :
    κ * |z| - z ^ 2 / (4 * t) ≤
      2 * κ ^ 2 * t - z ^ 2 / (8 * t) := by
  have hsq : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
  rw [hsq]
  have h : 0 ≤ (2 * κ ^ 2 * t - |z| ^ 2 / (8 * t)) - (κ * |z| - |z| ^ 2 / (4 * t)) := by
    have h_diff_eq : (2 * κ ^ 2 * t - |z| ^ 2 / (8 * t)) - (κ * |z| - |z| ^ 2 / (4 * t)) =
        2 * κ ^ 2 * t - κ * |z| + |z| ^ 2 / (8 * t) := by ring
    rw [h_diff_eq]
    have h_eq2 : 2 * κ ^ 2 * t - κ * |z| + |z| ^ 2 / (8 * t) =
        ((|z| - 4 * t * κ) ^ 2) / (8 * t) := by
      field_simp [ne_of_gt ht]
      ring
    rw [h_eq2]
    exact div_nonneg (pow_two_nonneg _) (by nlinarith)
  linarith

/-- The half-weight assigned to the derivative kernel. -/
def wholeLineChiLargeKernelHalfWeight (κ x y : ℝ) : ℝ :=
  Real.exp ((κ / 2) * regDist (y - x))

/-- The complementary half-weight assigned to the source. -/
def wholeLineChiLargeSourceHalfWeight (κ x y : ℝ) : ℝ :=
  Real.exp (-(κ / 2) * regDist (y - x))

theorem kernelHalfWeight_mul_sourceHalfWeight
    (κ x y : ℝ) :
    wholeLineChiLargeKernelHalfWeight κ x y *
        wholeLineChiLargeSourceHalfWeight κ x y = 1 := by
  unfold wholeLineChiLargeKernelHalfWeight
    wholeLineChiLargeSourceHalfWeight
  rw [← Real.exp_add]
  convert Real.exp_zero using 1
  ring

theorem sourceHalfWeight_sq_eq_localizingWeightAt
    (κ x y : ℝ) :
    wholeLineChiLargeSourceHalfWeight κ x y ^ 2 =
      localizingWeightAt κ x y := by
  unfold wholeLineChiLargeSourceHalfWeight localizingWeightAt
    localizingWeight
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Coefficient in the pointwise square bound for the weighted derivative
kernel. -/
def wholeLineWeightedHeatDerivL2PointConstant (t κ : ℝ) : ℝ :=
  Real.exp κ *
    ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
      Real.exp (2 * κ ^ 2 * t)

def wholeLineWeightedHeatDerivL2NormBound (t κ : ℝ) : ℝ :=
  (wholeLineWeightedHeatDerivL2PointConstant t κ *
    Real.sqrt (Real.pi / (1 / (8 * t)))) ^ (1 / 2 : ℝ)

theorem heatGradPointwiseBound_le_inv
    {t : ℝ} (ht : 0 < t) :
    ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ≤ 1 / t := by
  have hsqrt : Real.sqrt (4 * (2 * t)) ≤
      2 * Real.sqrt (4 * Real.pi * t) := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
    rw [Real.sq_sqrt (by positivity), mul_pow,
      Real.sq_sqrt (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hfac : 0 ≤
      (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) := by
    positivity
  unfold ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound
  calc
    (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) *
        Real.sqrt (4 * (2 * t)) ≤
      (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) *
        (2 * Real.sqrt (4 * Real.pi * t)) :=
      mul_le_mul_of_nonneg_left hsqrt hfac
    _ = 1 / t := by
      field_simp [ne_of_gt ht,
        ne_of_gt (show 0 < Real.sqrt (4 * Real.pi * t) by positivity)]

theorem gaussianL2MassRoot_le_six_sqrt
    {t : ℝ} (ht : 0 < t) :
    Real.sqrt (Real.pi / (1 / (8 * t))) ≤ 6 * Real.sqrt t := by
  rw [← sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
  rw [Real.sq_sqrt (by positivity), mul_pow,
    Real.sq_sqrt ht.le]
  have heq : Real.pi / (1 / (8 * t)) = 8 * Real.pi * t := by
    field_simp [ne_of_gt ht]
  rw [heq]
  nlinarith [Real.pi_le_four]

theorem inv_sq_mul_sqrt_eq_rpow_neg_three_halves
    {t : ℝ} (ht : 0 < t) :
    (1 / t) ^ 2 * Real.sqrt t = t ^ (-3 / 2 : ℝ) := by
  rw [one_div, ← Real.rpow_neg_one, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul_natCast ht.le (-1) 2,
    ← Real.rpow_add ht]
  congr 1
  norm_num

theorem heatGrad_sq_mul_gaussianMassRoot_le
    {t : ℝ} (ht : 0 < t) :
    ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
        Real.sqrt (Real.pi / (1 / (8 * t))) ≤
      16 * t ^ (-3 / 2 : ℝ) := by
  have hH := heatGradPointwiseBound_le_inv ht
  have hH0 : 0 ≤
      ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t := by
    unfold ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound
    positivity
  have hinv0 : 0 ≤ 1 / t := by positivity
  calc
    ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
        Real.sqrt (Real.pi / (1 / (8 * t))) ≤
      (1 / t) ^ 2 * (6 * Real.sqrt t) :=
        mul_le_mul (pow_le_pow_left₀ hH0 hH 2)
          (gaussianL2MassRoot_le_six_sqrt ht)
          (Real.sqrt_nonneg _)
          (pow_nonneg hinv0 2)
    _ = 6 * t ^ (-3 / 2 : ℝ) := by
      rw [← inv_sq_mul_sqrt_eq_rpow_neg_three_halves ht]
      ring
    _ ≤ 16 * t ^ (-3 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (Real.rpow_nonneg ht.le _)

theorem wholeLineWeightedHeatDerivL2NormBound_le
    {t κ : ℝ} (ht : 0 < t) :
    wholeLineWeightedHeatDerivL2NormBound t κ ≤
      4 * Real.exp (κ / 2) * Real.exp (κ ^ 2 * t) *
        t ^ (-3 / 4 : ℝ) := by
  let H := ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t
  let R := Real.sqrt (Real.pi / (1 / (8 * t)))
  let I := wholeLineWeightedHeatDerivL2PointConstant t κ * R
  let U := 16 * Real.exp κ * Real.exp (2 * κ ^ 2 * t) *
    t ^ (-3 / 2 : ℝ)
  have hI0 : 0 ≤ I := by
    dsimp [I, R]
    unfold wholeLineWeightedHeatDerivL2PointConstant
    positivity
  have hU0 : 0 ≤ U := by
    dsimp [U]
    positivity
  have hIU : I ≤ U := by
    dsimp [I, U, R, H]
    unfold wholeLineWeightedHeatDerivL2PointConstant
    have hcore := heatGrad_sq_mul_gaussianMassRoot_le ht
    calc
      Real.exp κ *
            ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
          Real.exp (2 * κ ^ 2 * t) *
            Real.sqrt (Real.pi / (1 / (8 * t))) =
        (Real.exp κ * Real.exp (2 * κ ^ 2 * t)) *
          (ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
            Real.sqrt (Real.pi / (1 / (8 * t))) ) := by ring
      _ ≤ (Real.exp κ * Real.exp (2 * κ ^ 2 * t)) *
          (16 * t ^ (-3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcore
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = 16 * Real.exp κ * Real.exp (2 * κ ^ 2 * t) *
          t ^ (-3 / 2 : ℝ) := by ring
  have hroot := Real.rpow_le_rpow hI0 hIU (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have h16 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
    rw [← Real.sqrt_eq_rpow]
    norm_num
  have hexpκ : Real.exp κ ^ (1 / 2 : ℝ) = Real.exp (κ / 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hexpt : Real.exp (2 * κ ^ 2 * t) ^ (1 / 2 : ℝ) =
      Real.exp (κ ^ 2 * t) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have htpow : (t ^ (-3 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
      t ^ (-3 / 4 : ℝ) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    ring
  have hrootU : U ^ (1 / 2 : ℝ) =
      4 * Real.exp (κ / 2) * Real.exp (κ ^ 2 * t) *
        t ^ (-3 / 4 : ℝ) := by
    dsimp [U]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      h16, hexpκ, hexpt, htpow]
  unfold wholeLineWeightedHeatDerivL2NormBound
  change I ^ (1 / 2 : ℝ) ≤ _
  exact hroot.trans_eq hrootU

theorem damped_wholeLineWeightedHeatDerivL2NormBound_le
    {t κ : ℝ} (ht : 0 < t) :
    Real.exp (-t) * wholeLineWeightedHeatDerivL2NormBound t κ ≤
      4 * Real.exp (κ / 2) *
        (t ^ (-3 / 4 : ℝ) * Real.exp (-(1 - κ ^ 2) * t)) := by
  have h := mul_le_mul_of_nonneg_left
    (wholeLineWeightedHeatDerivL2NormBound_le (t := t) (κ := κ) ht)
    (Real.exp_nonneg (-t))
  have hexp : Real.exp (-t) * Real.exp (κ ^ 2 * t) =
      Real.exp (-(1 - κ ^ 2) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-t) * wholeLineWeightedHeatDerivL2NormBound t κ ≤
      Real.exp (-t) *
        (4 * Real.exp (κ / 2) * Real.exp (κ ^ 2 * t) *
          t ^ (-3 / 4 : ℝ)) := h
    _ = (4 * Real.exp (κ / 2) * t ^ (-3 / 4 : ℝ)) *
        (Real.exp (-t) * Real.exp (κ ^ 2 * t)) := by ring
    _ = 4 * Real.exp (κ / 2) *
        (t ^ (-3 / 4 : ℝ) * Real.exp (-(1 - κ ^ 2) * t)) := by
      rw [hexp]
      ring

/-- In the committed critical window one may choose the localization rate
strictly below one.  The shifted heat semigroup then makes the weighted
`L² → L∞` derivative norm integrable for all positive times. -/
theorem damped_wholeLineWeightedHeatDerivL2NormBound_integrableOn_Ioi
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-t) *
        wholeLineWeightedHeatDerivL2NormBound t κ)
      (Set.Ioi 0) := by
  have hκmul : 0 ≤ κ * (1 - κ) :=
    mul_nonneg hκ0 (sub_nonneg.mpr hκ1.le)
  have hgap : 0 < 1 - κ ^ 2 := by
    nlinarith
  let C : ℝ := 4 * Real.exp (κ / 2)
  let g : ℝ → ℝ := fun t =>
    t ^ (-(3 / 4 : ℝ)) * Real.exp (-(1 - κ ^ 2) * t)
  have hg : IntegrableOn g (Set.Ioi 0) := by
    simpa [g] using
      (ShenWork.PDE.rpow_neg_mul_exp_integrableOn_Ioi
        (theta := (3 / 4 : ℝ)) (nu := 1 - κ ^ 2)
        (by norm_num) (by norm_num) hgap)
  have hmajor : IntegrableOn (fun t => C * g t) (Set.Ioi 0) :=
    hg.const_mul C
  have htargetMeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-t) *
        wholeLineWeightedHeatDerivL2NormBound t κ)
      (volume.restrict (Set.Ioi 0)) := by
    unfold wholeLineWeightedHeatDerivL2NormBound
      wholeLineWeightedHeatDerivL2PointConstant
      ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound
    measurability
  refine hmajor.mono' htargetMeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hnormBound0 : 0 ≤ wholeLineWeightedHeatDerivL2NormBound t κ := by
    unfold wholeLineWeightedHeatDerivL2NormBound
    apply Real.rpow_nonneg
    exact mul_nonneg
      (by
        unfold wholeLineWeightedHeatDerivL2PointConstant
        positivity)
      (Real.sqrt_nonneg _)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hnormBound0)]
  have hexponent : (-3 / 4 : ℝ) = -(3 / 4 : ℝ) := by ring_nf
  simpa [C, g, hexponent] using
    (damped_wholeLineWeightedHeatDerivL2NormBound_le
      (t := t) (κ := κ) ht0)

theorem wholeLineWeightedHeatDerivL2PointConstant_nonneg
    (t κ : ℝ) :
    0 ≤ wholeLineWeightedHeatDerivL2PointConstant t κ := by
  unfold wholeLineWeightedHeatDerivL2PointConstant
  positivity

/-- After inserting the inverse half-weight, the square of a translated
Gaussian derivative retains a Gaussian with variance `4t`. -/
theorem weighted_heatKernel_deriv_sq_pointwise
    {t κ : ℝ} (ht : 0 < t) (hκ : 0 ≤ κ) (x y : ℝ) :
    ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
        wholeLineChiLargeKernelHalfWeight κ x y‖ ^ 2 ≤
      wholeLineWeightedHeatDerivL2PointConstant t κ *
        Real.exp (-(x - y) ^ 2 / (8 * t)) := by
  have hderiv :
      deriv (fun z : ℝ => heatKernel t (z - y)) x =
        deriv (fun z : ℝ => heatKernel t z) (x - y) := by
    rw [deriv_heatKernel_translated_left ht x y,
      deriv_heatKernel ht (x - y)]
  have hgrad' :
      |deriv (fun z : ℝ => heatKernel t z) (x - y)| ≤
        ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t *
          Real.exp (-(x - y) ^ 2 / (8 * t)) := by
    have hraw :=
      ShenWork.IntervalNeumannFullKernel.abs_deriv_heatKernel_le
        ht (x - y)
    have heq : -(x - y) ^ 2 / (4 * (2 * t)) =
        -(x - y) ^ 2 / (8 * t) := by ring_nf
    simpa only [heq] using hraw
  have hH : 0 ≤
      ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t := by
    unfold ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound
    positivity
  have hweighted :
      |deriv (fun z : ℝ => heatKernel t z) (x - y)| *
          wholeLineChiLargeKernelHalfWeight κ x y ≤
        (ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t *
            Real.exp (-(x - y) ^ 2 / (8 * t))) *
          wholeLineChiLargeKernelHalfWeight κ x y := by
    exact mul_le_mul_of_nonneg_right hgrad'
      (Real.exp_pos _).le
  have hsquare :=
    (sq_le_sq₀
      (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      (mul_nonneg
        (mul_nonneg hH (Real.exp_pos _).le)
        (Real.exp_pos _).le)).2 hweighted
  have hreg :
      κ * regDist (y - x) - (x - y) ^ 2 / (4 * t) ≤
        κ + 2 * κ ^ 2 * t - (x - y) ^ 2 / (8 * t) := by
    have hr := regDist_le_one_add_abs (y - x)
    have hmul := mul_le_mul_of_nonneg_left hr hκ
    have habs : |y - x| = |x - y| := abs_sub_comm y x
    rw [habs] at hmul
    linarith [linear_abs_sub_quadratic_le
      (t := t) (κ := κ) (z := x - y) ht]
  have hwpos : 0 < wholeLineChiLargeKernelHalfWeight κ x y := by
    unfold wholeLineChiLargeKernelHalfWeight
    positivity
  rw [hderiv, Real.norm_eq_abs,
    abs_mul, abs_of_pos hwpos]
  calc
    (|deriv (fun z : ℝ => heatKernel t z) (x - y)| *
        wholeLineChiLargeKernelHalfWeight κ x y) ^ 2 ≤
      ((ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t *
          Real.exp (-(x - y) ^ 2 / (8 * t))) *
        wholeLineChiLargeKernelHalfWeight κ x y) ^ 2 := hsquare
    _ = ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
        Real.exp
          (κ * regDist (y - x) - (x - y) ^ 2 / (4 * t)) := by
      unfold wholeLineChiLargeKernelHalfWeight
      have exp_sq (a : ℝ) : Real.exp a ^ 2 = Real.exp (2 * a) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      have hexp :
          (Real.exp (-(x - y) ^ 2 / (8 * t)) *
              Real.exp (κ / 2 * regDist (y - x))) ^ 2 =
            Real.exp
              (κ * regDist (y - x) - (x - y) ^ 2 / (4 * t)) := by
        rw [mul_pow, exp_sq, exp_sq, ← Real.exp_add]
        congr 1
        ring
      rw [show
          (ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t *
              Real.exp (-(x - y) ^ 2 / (8 * t)) *
                Real.exp (κ / 2 * regDist (y - x))) ^ 2 =
            ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
              (Real.exp (-(x - y) ^ 2 / (8 * t)) *
                Real.exp (κ / 2 * regDist (y - x))) ^ 2 by ring,
        hexp]
    _ ≤ ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
        Real.exp
          (κ + 2 * κ ^ 2 * t - (x - y) ^ 2 / (8 * t)) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hreg)
        (sq_nonneg _)
    _ = wholeLineWeightedHeatDerivL2PointConstant t κ *
        Real.exp (-(x - y) ^ 2 / (8 * t)) := by
      unfold wholeLineWeightedHeatDerivL2PointConstant
      have hexp :
          Real.exp κ * Real.exp (2 * κ ^ 2 * t) *
              Real.exp (-(x - y) ^ 2 / (8 * t)) =
            Real.exp
              (κ + 2 * κ ^ 2 * t - (x - y) ^ 2 / (8 * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [show Real.exp κ *
              ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
                Real.exp (2 * κ ^ 2 * t) *
                  Real.exp (-(x - y) ^ 2 / (8 * t)) =
            ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound t ^ 2 *
              (Real.exp κ * Real.exp (2 * κ ^ 2 * t) *
                Real.exp (-(x - y) ^ 2 / (8 * t))) by ring,
        hexp]

/-- Integrated square bound for the weighted translated derivative row. -/
theorem weighted_heatKernel_deriv_sq_integral_le
    {t κ : ℝ} (ht : 0 < t) (hκ : 0 ≤ κ) (x : ℝ) :
    (∫ y : ℝ,
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
          wholeLineChiLargeKernelHalfWeight κ x y‖ ^ 2) ≤
      wholeLineWeightedHeatDerivL2PointConstant t κ *
        Real.sqrt (Real.pi / (1 / (8 * t))) := by
  have hb : 0 < 1 / (8 * t) := by positivity
  have hgauss : Integrable
      (fun y : ℝ => Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)) := by
    have hbase := integrable_exp_neg_mul_sq hb
    have hkey :
        (fun y : ℝ => Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)) =
          fun y : ℝ =>
            (fun z : ℝ => Real.exp (-(1 / (8 * t)) * z ^ 2))
              (y + (-x)) := by
      funext y
      congr 1
      ring
    rw [hkey]
    exact hbase.comp_add_right (-x)
  have hmajor : Integrable (fun y : ℝ =>
      wholeLineWeightedHeatDerivL2PointConstant t κ *
        Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)) :=
    hgauss.const_mul _
  have htarget : Integrable (fun y : ℝ =>
      ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
        wholeLineChiLargeKernelHalfWeight κ x y‖ ^ 2) := by
    refine hmajor.mono' ?_ ?_
    · have hderivCont : Continuous (fun y : ℝ =>
          deriv (fun z : ℝ => heatKernel t (z - y)) x) := by
        have hbase :=
          ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht
        have heq : (fun y : ℝ =>
            deriv (fun z : ℝ => heatKernel t (z - y)) x) =
              fun y : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - y) := by
          funext y
          rw [deriv_heatKernel_translated_left ht x y,
            deriv_heatKernel ht (x - y)]
        rw [heq]
        exact hbase.comp (continuous_const.sub continuous_id)
      have hweightCont : Continuous
          (wholeLineChiLargeKernelHalfWeight κ x) := by
        unfold wholeLineChiLargeKernelHalfWeight
        exact Real.continuous_exp.comp
          (continuous_const.mul
            (contDiff_two_regDist.continuous.comp
              (continuous_id.sub continuous_const)))
      exact ((hderivCont.mul hweightCont).norm.pow 2).aestronglyMeasurable
    · filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have heqexp : -(1 / (8 * t)) * (x - y) ^ 2 =
          -(x - y) ^ 2 / (8 * t) := by
        field_simp [ne_of_gt ht]
      change
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
          wholeLineChiLargeKernelHalfWeight κ x y‖ ^ 2 ≤
        wholeLineWeightedHeatDerivL2PointConstant t κ *
          Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)
      rw [heqexp]
      exact weighted_heatKernel_deriv_sq_pointwise ht hκ x y
  calc
    (∫ y : ℝ,
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
          wholeLineChiLargeKernelHalfWeight κ x y‖ ^ 2) ≤
      ∫ y : ℝ, wholeLineWeightedHeatDerivL2PointConstant t κ *
        Real.exp (-(1 / (8 * t)) * (x - y) ^ 2) := by
      apply integral_mono htarget hmajor
      intro y
      have heqexp : -(1 / (8 * t)) * (x - y) ^ 2 =
          -(x - y) ^ 2 / (8 * t) := by
        field_simp [ne_of_gt ht]
      change
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
          wholeLineChiLargeKernelHalfWeight κ x y‖ ^ 2 ≤
        wholeLineWeightedHeatDerivL2PointConstant t κ *
          Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)
      rw [heqexp]
      exact weighted_heatKernel_deriv_sq_pointwise ht hκ x y
    _ = wholeLineWeightedHeatDerivL2PointConstant t κ *
        ∫ y : ℝ, Real.exp (-(1 / (8 * t)) * (x - y) ^ 2) := by
      rw [integral_const_mul]
    _ = wholeLineWeightedHeatDerivL2PointConstant t κ *
        Real.sqrt (Real.pi / (1 / (8 * t))) := by
      congr 1
      have hkey :
          (∫ y : ℝ, Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)) =
            ∫ y : ℝ, Real.exp (-(1 / (8 * t)) * y ^ 2) := by
        have hfun :
            (fun y : ℝ => Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)) =
              fun y : ℝ =>
                (fun z : ℝ => Real.exp (-(1 / (8 * t)) * z ^ 2))
                  (y + (-x)) := by
          funext y
          congr 1
          ring
        rw [hfun]
        exact integral_add_right_eq_self (μ := (volume : Measure ℝ))
          (fun z : ℝ => Real.exp (-(1 / (8 * t)) * z ^ 2)) (-x)
      rw [hkey, integral_gaussian]

theorem weighted_heatKernel_deriv_sq_integrable
    {t κ : ℝ} (ht : 0 < t) (hκ : 0 ≤ κ) (x : ℝ) :
    Integrable (fun y : ℝ =>
      ‖deriv (fun z : ℝ => heatKernel t (z - y)) x *
        wholeLineChiLargeKernelHalfWeight κ x y‖ ^ (2 : ℝ)) := by
  have hb : 0 < 1 / (8 * t) := by positivity
  have hbase : Integrable
      (fun y : ℝ => Real.exp (-(1 / (8 * t)) * y ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hgauss : Integrable
      (fun y : ℝ => Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)) := by
    have hkey :
        (fun y : ℝ => Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)) =
          fun y : ℝ =>
            (fun z : ℝ => Real.exp (-(1 / (8 * t)) * z ^ 2))
              (y + (-x)) := by
      funext y
      congr 1
      ring
    rw [hkey]
    exact hbase.comp_add_right (-x)
  have hmajor : Integrable (fun y : ℝ =>
      wholeLineWeightedHeatDerivL2PointConstant t κ *
        Real.exp (-(1 / (8 * t)) * (x - y) ^ 2)) :=
    hgauss.const_mul _
  refine hmajor.mono' ?_ ?_
  · have hderivCont : Continuous (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel t (z - y)) x) := by
      have hbaseCont :=
        ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht
      have heq : (fun y : ℝ =>
          deriv (fun z : ℝ => heatKernel t (z - y)) x) =
            fun y : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - y) := by
        funext y
        rw [deriv_heatKernel_translated_left ht x y,
          deriv_heatKernel ht (x - y)]
      rw [heq]
      exact hbaseCont.comp (continuous_const.sub continuous_id)
    have hweightCont : Continuous
        (wholeLineChiLargeKernelHalfWeight κ x) := by
      unfold wholeLineChiLargeKernelHalfWeight
      exact Real.continuous_exp.comp
        (continuous_const.mul
          (contDiff_two_regDist.continuous.comp
            (continuous_id.sub continuous_const)))
    exact ((hderivCont.mul hweightCont).norm.rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2))).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) 2)]
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    have heqexp : -(1 / (8 * t)) * (x - y) ^ 2 =
        -(x - y) ^ 2 / (8 * t) := by
      field_simp [ne_of_gt ht]
    rw [heqexp]
    exact weighted_heatKernel_deriv_sq_pointwise ht hκ x y

theorem weighted_heatKernel_deriv_memLp_two
    {t κ : ℝ} (ht : 0 < t) (hκ : 0 ≤ κ) (x : ℝ) :
    MemLp (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t (z - y)) x *
        wholeLineChiLargeKernelHalfWeight κ x y)
      (ENNReal.ofReal 2) volume := by
  have hcont : Continuous (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t (z - y)) x *
        wholeLineChiLargeKernelHalfWeight κ x y) := by
    have hderivCont : Continuous (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel t (z - y)) x) := by
      have hbaseCont :=
        ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht
      have heq : (fun y : ℝ =>
          deriv (fun z : ℝ => heatKernel t (z - y)) x) =
            fun y : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - y) := by
        funext y
        rw [deriv_heatKernel_translated_left ht x y,
          deriv_heatKernel ht (x - y)]
      rw [heq]
      exact hbaseCont.comp (continuous_const.sub continuous_id)
    apply hderivCont.mul
    unfold wholeLineChiLargeKernelHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  apply (integrable_norm_rpow_iff hcont.aestronglyMeasurable
    (by norm_num) (by norm_num)).mp
  simpa using weighted_heatKernel_deriv_sq_integrable ht hκ x

/-! ## The weighted source half -/

/-- A continuous scalar function with integrable square belongs to `L²`. -/
theorem memLp_two_of_continuous_of_integrable_sq
    {f : ℝ → ℝ} (hf : Continuous f)
    (hsq : Integrable (fun x : ℝ => ‖f x‖ ^ (2 : ℝ))) :
    MemLp f (ENNReal.ofReal 2) volume := by
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (by norm_num) (by norm_num)).mp
  simpa using hsq

/-- The square of the source half-weight is exactly the translated
localizing weight, so a uniformly-local moment is a genuine global `L²`
bound after the half-weight is inserted. -/
theorem weighted_source_sq_integrable_and_bound
    {P κ K L : ℝ} {u : ℝ → ℝ} {F : ℝ → ℝ}
    (hP : 0 ≤ P) (hκ : 0 < κ)
    (huC : IsCUnifBdd u)
    (hF : Continuous F)
    (hpoint : ∀ y,
      |F y| ^ 2 ≤ L ^ 2 * (1 + (u y) ^ P))
    (x : ℝ)
    (hmoment :
      (∫ y : ℝ, (u y) ^ P * localizingWeightAt κ x y) ≤ K) :
    Integrable (fun y : ℝ =>
        ‖F y * wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ)) ∧
      (∫ y : ℝ,
        ‖F y * wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ)) ≤
        L ^ 2 * (K + 2 / κ) := by
  have hmomentInt : Integrable (fun y : ℝ =>
      (u y) ^ P * localizingWeightAt κ x y) :=
    wholeLineLocalLpIntegrable_of_isCUnifBdd
      (u := fun _ => u) (t := 0) hP hκ huC
  have hweightInt := localizingWeightAt_integrable hκ x
  let G : ℝ → ℝ := fun y => L ^ 2 *
    ((u y) ^ P * localizingWeightAt κ x y +
      localizingWeightAt κ x y)
  have hG : Integrable G := by
    dsimp [G]
    exact (hmomentInt.add hweightInt).const_mul (L ^ 2)
  have hsourceCont : Continuous (fun y : ℝ =>
      F y * wholeLineChiLargeSourceHalfWeight κ x y) := by
    apply hF.mul
    unfold wholeLineChiLargeSourceHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  have hdom : ∀ y : ℝ,
      ‖F y * wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ) ≤
        G y := by
    intro y
    have hw0 : 0 ≤ localizingWeightAt κ x y :=
      (localizingWeightAt_pos κ x y).le
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
    rw [norm_mul, mul_pow, Real.norm_eq_abs,
      show ‖wholeLineChiLargeSourceHalfWeight κ x y‖ ^ 2 =
          localizingWeightAt κ x y by
        rw [Real.norm_eq_abs,
          abs_of_pos (by
            unfold wholeLineChiLargeSourceHalfWeight
            positivity)]
        exact sourceHalfWeight_sq_eq_localizingWeightAt κ x y]
    dsimp [G]
    calc
      |F y| ^ 2 * localizingWeightAt κ x y ≤
          (L ^ 2 * (1 + (u y) ^ P)) *
            localizingWeightAt κ x y :=
        mul_le_mul_of_nonneg_right (hpoint y) hw0
      _ = L ^ 2 *
          ((u y) ^ P * localizingWeightAt κ x y +
            localizingWeightAt κ x y) := by ring
  have hsourceInt : Integrable (fun y : ℝ =>
      ‖F y * wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ)) := by
    refine hG.mono' ?_ ?_
    · exact (hsourceCont.norm.rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2))).aestronglyMeasurable
    · filter_upwards [] with y
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) 2)]
      exact hdom y
  refine ⟨hsourceInt, ?_⟩
  calc
    (∫ y : ℝ,
        ‖F y * wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ)) ≤
      ∫ y : ℝ, G y := integral_mono hsourceInt hG hdom
    _ = L ^ 2 *
        ((∫ y : ℝ, (u y) ^ P * localizingWeightAt κ x y) +
          ∫ y : ℝ, localizingWeightAt κ x y) := by
      dsimp [G]
      rw [integral_const_mul, integral_add hmomentInt hweightInt]
    _ ≤ L ^ 2 * (K + 2 / κ) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hmoment
          (integral_localizingWeightAt_le_two_div hκ x))
        (sq_nonneg L)

/-- The preceding square-integrability package in `MemLp` form. -/
theorem weighted_source_memLp_two
    {P κ K L : ℝ} {u : ℝ → ℝ} {F : ℝ → ℝ}
    (hP : 0 ≤ P) (hκ : 0 < κ)
    (huC : IsCUnifBdd u)
    (hF : Continuous F)
    (hpoint : ∀ y,
      |F y| ^ 2 ≤ L ^ 2 * (1 + (u y) ^ P))
    (x : ℝ)
    (hmoment :
      (∫ y : ℝ, (u y) ^ P * localizingWeightAt κ x y) ≤ K) :
    MemLp (fun y : ℝ =>
      F y * wholeLineChiLargeSourceHalfWeight κ x y)
        (ENNReal.ofReal 2) volume := by
  apply memLp_two_of_continuous_of_integrable_sq
  · apply hF.mul
    unfold wholeLineChiLargeSourceHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  · exact (weighted_source_sq_integrable_and_bound hP hκ huC
      hF hpoint x hmoment).1

/-- A bounded resolver gradient and `P ≥ 2m` turn the chemotaxis flux into a
weighted `L²` source controlled by the local `P`-moment. -/
theorem wholeLineChemotaxisFlux_sq_le_of_gradient
    (p : CMParams) {P L : ℝ} {u : ℝ → ℝ}
    (hP : 2 * p.m ≤ P) (hL : 0 ≤ L)
    (hu0 : ∀ y, 0 ≤ u y)
    (hgrad : ∀ y, |deriv (frozenElliptic p u) y| ≤ L)
    (y : ℝ) :
    |wholeLineChemotaxisFlux p u y| ^ 2 ≤
      L ^ 2 * (1 + (u y) ^ P) := by
  have hum0 : 0 ≤ (u y) ^ p.m := Real.rpow_nonneg (hu0 y) _
  have hflux : |wholeLineChemotaxisFlux p u y| ≤ (u y) ^ p.m * L := by
    rw [wholeLineChemotaxisFlux, abs_mul,
      abs_of_nonneg hum0]
    exact mul_le_mul_of_nonneg_left (hgrad y) hum0
  have hfluxSq : |wholeLineChemotaxisFlux p u y| ^ 2 ≤
      ((u y) ^ p.m * L) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg hum0 hL)).2 hflux
  have hpowSq : ((u y) ^ p.m) ^ 2 = (u y) ^ (2 * p.m) := by
    simpa [mul_comm] using
      (Real.rpow_mul_natCast (hu0 y) p.m 2).symm
  have hp2m : (u y) ^ (2 * p.m) ≤ 1 + (u y) ^ P :=
    rpow_le_one_add_rpow_of_exponent_le (hu0 y)
      (by linarith [p.hm]) hP
  calc
    |wholeLineChemotaxisFlux p u y| ^ 2 ≤
        ((u y) ^ p.m * L) ^ 2 := hfluxSq
    _ = L ^ 2 * (u y) ^ (2 * p.m) := by
      rw [mul_pow, hpowSq]
      ring
    _ ≤ L ^ 2 * (1 + (u y) ^ P) :=
      mul_le_mul_of_nonneg_left hp2m (sq_nonneg L)

/-- Concrete weighted `L²` flux package consumed by the final Duhamel
estimate. -/
theorem weighted_chemotaxisFlux_sq_integrable_and_bound
    (p : CMParams) {P κ K L : ℝ} {u : ℝ → ℝ}
    (hP0 : 0 ≤ P) (hP2m : 2 * p.m ≤ P)
    (hκ : 0 < κ) (hL : 0 ≤ L)
    (huC : IsCUnifBdd u) (hu0 : ∀ y, 0 ≤ u y)
    (hfluxC : Continuous (wholeLineChemotaxisFlux p u))
    (hgrad : ∀ y, |deriv (frozenElliptic p u) y| ≤ L)
    (x : ℝ)
    (hmoment :
      (∫ y : ℝ, (u y) ^ P * localizingWeightAt κ x y) ≤ K) :
    Integrable (fun y : ℝ =>
        ‖wholeLineChemotaxisFlux p u y *
          wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ)) ∧
      (∫ y : ℝ,
        ‖wholeLineChemotaxisFlux p u y *
          wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ)) ≤
        L ^ 2 * (K + 2 / κ) :=
  weighted_source_sq_integrable_and_bound hP0 hκ huC hfluxC
    (wholeLineChemotaxisFlux_sq_le_of_gradient
      p hP2m hL hu0 hgrad) x hmoment

/-! ## Weighted `L² → L∞` convolution -/

/-- Cauchy--Schwarz after splitting the translated localizing weight between
the source and the Gaussian derivative. -/
theorem weighted_heatKernel_deriv_convolution_abs_le
    {t κ B : ℝ} (ht : 0 < t) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    {F : ℝ → ℝ} (hF : Continuous F) (x : ℝ)
    (hFsq : Integrable (fun y : ℝ =>
      ‖F y * wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ)))
    (hFsqBound :
      (∫ y : ℝ,
        ‖F y * wholeLineChiLargeSourceHalfWeight κ x y‖ ^ (2 : ℝ)) ≤ B) :
    |∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel t (z - y)) x * F y| ≤
      wholeLineWeightedHeatDerivL2NormBound t κ * B ^ (1 / 2 : ℝ) := by
  let A : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => heatKernel t (z - y)) x *
      wholeLineChiLargeKernelHalfWeight κ x y
  let S : ℝ → ℝ := fun y =>
    F y * wholeLineChiLargeSourceHalfWeight κ x y
  have hAcont : Continuous A := by
    have hderivCont : Continuous (fun y : ℝ =>
        deriv (fun z : ℝ => heatKernel t (z - y)) x) := by
      have hbaseCont :=
        ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht
      have heq : (fun y : ℝ =>
          deriv (fun z : ℝ => heatKernel t (z - y)) x) =
            fun y : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - y) := by
        funext y
        rw [deriv_heatKernel_translated_left ht x y,
          deriv_heatKernel ht (x - y)]
      rw [heq]
      exact hbaseCont.comp (continuous_const.sub continuous_id)
    apply hderivCont.mul
    unfold wholeLineChiLargeKernelHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  have hScont : Continuous S := by
    apply hF.mul
    unfold wholeLineChiLargeSourceHalfWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul
        (contDiff_two_regDist.continuous.comp
          (continuous_id.sub continuous_const)))
  have hAmem : MemLp A (ENNReal.ofReal 2) volume := by
    simpa [A] using weighted_heatKernel_deriv_memLp_two ht hκ x
  have hSmem : MemLp S (ENNReal.ofReal 2) volume :=
    memLp_two_of_continuous_of_integrable_sq hScont (by simpa [S] using hFsq)
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder :
      (∫ y : ℝ, ‖A y‖ * ‖S y‖) ≤
        (∫ y : ℝ, ‖A y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ y : ℝ, ‖S y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    integral_mul_norm_le_Lp_mul_Lq hpq hAmem hSmem
  have hAint :
      (∫ y : ℝ, ‖A y‖ ^ (2 : ℝ)) ≤
        wholeLineWeightedHeatDerivL2PointConstant t κ *
          Real.sqrt (Real.pi / (1 / (8 * t))) := by
    simpa [A, Real.rpow_natCast] using
      weighted_heatKernel_deriv_sq_integral_le ht hκ x
  have hAbound0 : 0 ≤
      wholeLineWeightedHeatDerivL2PointConstant t κ *
        Real.sqrt (Real.pi / (1 / (8 * t))) :=
    mul_nonneg (wholeLineWeightedHeatDerivL2PointConstant_nonneg t κ)
      (Real.sqrt_nonneg _)
  have hAroot :
      (∫ y : ℝ, ‖A y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        wholeLineWeightedHeatDerivL2NormBound t κ := by
    unfold wholeLineWeightedHeatDerivL2NormBound
    exact Real.rpow_le_rpow
      (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) 2)
      hAint (by norm_num)
  have hSroot :
      (∫ y : ℝ, ‖S y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        B ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow
      (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) 2)
      (by simpa [S] using hFsqBound)
    norm_num
  have hSroot0 : 0 ≤
      (∫ y : ℝ, ‖S y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun y =>
      Real.rpow_nonneg (norm_nonneg _) 2) _
  have hBroot0 : 0 ≤ B ^ (1 / 2 : ℝ) := Real.rpow_nonneg hB _
  have hAroot0 : 0 ≤
      (∫ y : ℝ, ‖A y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun y =>
      Real.rpow_nonneg (norm_nonneg _) 2) _
  have hnormProduct :
      (∫ y : ℝ, ‖A y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ y : ℝ, ‖S y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        wholeLineWeightedHeatDerivL2NormBound t κ *
          B ^ (1 / 2 : ℝ) := by
    exact mul_le_mul hAroot hSroot hSroot0
      (Real.rpow_nonneg hAbound0 _)
  have hfactor : (fun y : ℝ =>
      deriv (fun z : ℝ => heatKernel t (z - y)) x * F y) =
      fun y : ℝ => A y * S y := by
    funext y
    dsimp [A, S]
    rw [show
        (deriv (fun z : ℝ => heatKernel t (z - y)) x *
            wholeLineChiLargeKernelHalfWeight κ x y) *
          (F y * wholeLineChiLargeSourceHalfWeight κ x y) =
        (deriv (fun z : ℝ => heatKernel t (z - y)) x * F y) *
          (wholeLineChiLargeKernelHalfWeight κ x y *
            wholeLineChiLargeSourceHalfWeight κ x y) by ring,
      kernelHalfWeight_mul_sourceHalfWeight, mul_one]
  rw [hfactor]
  calc
    |∫ y : ℝ, A y * S y| = ‖∫ y : ℝ, A y * S y‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ, ‖A y * S y‖ := norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, ‖A y‖ * ‖S y‖ := by
      congr 1
      funext y
      rw [norm_mul]
    _ ≤ (∫ y : ℝ, ‖A y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ y : ℝ, ‖S y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hholder
    _ ≤ wholeLineWeightedHeatDerivL2NormBound t κ *
          B ^ (1 / 2 : ℝ) := hnormProduct

/-- The concrete whole-line chemotaxis-flux smoothing estimate from one
uniformly-local moment slice. -/
theorem weighted_chemotaxisFlux_convolution_abs_le
    (p : CMParams) {P κ K L t : ℝ}
    (hP0 : 0 ≤ P) (hP2m : 2 * p.m ≤ P)
    (hκ : 0 < κ) (hL : 0 ≤ L) (ht : 0 < t)
    {u : ℝ → ℝ} (huC : IsCUnifBdd u) (hu0 : ∀ y, 0 ≤ u y)
    (hfluxC : Continuous (wholeLineChemotaxisFlux p u))
    (hgrad : ∀ y, |deriv (frozenElliptic p u) y| ≤ L)
    (x : ℝ)
    (hmoment :
      (∫ y : ℝ, (u y) ^ P * localizingWeightAt κ x y) ≤ K) :
    |∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel t (z - y)) x *
          wholeLineChemotaxisFlux p u y| ≤
      wholeLineWeightedHeatDerivL2NormBound t κ *
        (L ^ 2 * (K + 2 / κ)) ^ (1 / 2 : ℝ) := by
  have hmoment0 : 0 ≤
      ∫ y : ℝ, (u y) ^ P * localizingWeightAt κ x y :=
    integral_nonneg fun y => mul_nonneg
      (Real.rpow_nonneg (hu0 y) P)
      (localizingWeightAt_pos κ x y).le
  have hK : 0 ≤ K := hmoment0.trans hmoment
  have hB : 0 ≤ L ^ 2 * (K + 2 / κ) := by positivity
  have hsource := weighted_chemotaxisFlux_sq_integrable_and_bound
    p hP0 hP2m hκ hL huC hu0 hfluxC hgrad x hmoment
  exact weighted_heatKernel_deriv_convolution_abs_le ht hκ.le hB
    hfluxC x hsource.1 hsource.2

section AxiomAudit

#print axioms linear_abs_sub_quadratic_le
#print axioms wholeLineWeightedHeatDerivL2NormBound_le
#print axioms damped_wholeLineWeightedHeatDerivL2NormBound_le
#print axioms damped_wholeLineWeightedHeatDerivL2NormBound_integrableOn_Ioi
#print axioms weighted_heatKernel_deriv_sq_pointwise
#print axioms weighted_heatKernel_deriv_sq_integral_le
#print axioms weighted_source_sq_integrable_and_bound
#print axioms weighted_source_memLp_two
#print axioms wholeLineChemotaxisFlux_sq_le_of_gradient
#print axioms weighted_chemotaxisFlux_sq_integrable_and_bound
#print axioms weighted_heatKernel_deriv_convolution_abs_le
#print axioms weighted_chemotaxisFlux_convolution_abs_le

end AxiomAudit

end ShenWork.Paper1
