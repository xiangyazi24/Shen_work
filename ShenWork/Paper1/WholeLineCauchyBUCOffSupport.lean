import ShenWork.Paper1.WholeLineCauchyBUCNegativeSet
import ShenWork.Paper1.WholeLineHeatThirdDerivative
import ShenWork.PDE.F1ProbeFractionalMultiplier

open Filter Topology MeasureTheory Real Set
open scoped Interval
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.Paper1

open ShenWork.PDE.F1ProbeFractionalMultiplier

/-!
# Off-support regularity of the whole-line BUC Duhamel history

The positive-time Gaussian slices are differentiated first.  Later sections
split a Duhamel history into an old positive-lag part and a recent part whose
source vanishes near the evaluation point.
-/

def wholeLineCauchyHeatHessOp
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-t) * ∫ y : ℝ,
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y) * f y

def wholeLineCauchyHeatThirdOp
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-t) * ∫ y : ℝ,
    deriv
      (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
      (x - y) * f y

theorem wholeLineCauchyHeatHessOp_eq_zero_of_nonpos
    {f : ℝ → ℝ} {t x : ℝ} (ht : t ≤ 0) :
    wholeLineCauchyHeatHessOp t f x = 0 := by
  unfold wholeLineCauchyHeatHessOp
  have hkernel : ∀ y : ℝ,
      deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y) = 0 := by
    intro y
    rw [deriv_deriv_heatKernel_global]
    rw [heatKernel_of_nonpos ht]
    ring
  simp_rw [hkernel, zero_mul, integral_zero, mul_zero]

theorem wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos
    {f : ℝ → ℝ} {t x : ℝ} (ht : t ≤ 0) :
    wholeLineCauchyHeatThirdOp t f x = 0 := by
  unfold wholeLineCauchyHeatThirdOp
  have hkernel : ∀ y : ℝ,
      deriv
        (fun z : ℝ => deriv
          (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        (x - y) = 0 := by
    intro y
    rw [deriv_deriv_deriv_heatKernel_global]
    rw [heatKernel_of_nonpos ht]
    ring
  simp_rw [hkernel, zero_mul, integral_zero, mul_zero]

theorem wholeLineCauchyHeatGradOp_eq_deriv
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    wholeLineCauchyHeatGradOp t f x =
      Real.exp (-t) * deriv (fun z : ℝ => heatSemigroup t f z) x := by
  have hderiv := (ShenWork.PaperOne.ConvLeibniz.heatConvolution_space_deriv
    (f := f) (t := t) (x := x) (M := M) ht hf_meas hf).deriv
  unfold wholeLineCauchyHeatGradOp
  rw [integral_const_mul, hderiv]

theorem wholeLineCauchyHeatOp_hasDerivAt
    {f : ℝ → ℝ} {t x M : ℝ} (ht : 0 < t)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun z : ℝ => wholeLineCauchyHeatOp t f z)
      (wholeLineCauchyHeatGradOp t f x) x := by
  have hbase := ShenWork.PaperOne.ConvLeibniz.heatConvolution_space_deriv
    (f := f) (t := t) (x := x) (M := M) ht hf_meas hf
  have hmul := hbase.const_mul (Real.exp (-t))
  simpa [wholeLineCauchyHeatOp, modifiedSemigroup,
    wholeLineCauchyHeatGradOp, integral_const_mul] using hmul

theorem wholeLineCauchyHeatGradOp_hasDerivAt
    {f : ℝ → ℝ} {t x M : ℝ} (ht : 0 < t)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun z : ℝ => wholeLineCauchyHeatGradOp t f z)
      (wholeLineCauchyHeatHessOp t f x) x := by
  have hbase := ShenWork.PaperOne.ConvLeibniz.heatConvolution_space_second_deriv
    (f := f) (t := t) (x := x) (M := M) ht hf_meas hf
  have hmul := hbase.const_mul (Real.exp (-t))
  have heq : (fun z : ℝ => wholeLineCauchyHeatGradOp t f z) =
      fun z : ℝ => Real.exp (-t) * deriv (fun w : ℝ => heatSemigroup t f w) z := by
    funext z
    exact wholeLineCauchyHeatGradOp_eq_deriv ht hf_meas hf z
  rw [heq]
  simpa [wholeLineCauchyHeatHessOp] using hmul

theorem wholeLineCauchyHeatHessOp_hasDerivAt
    {f : ℝ → ℝ} {t x M : ℝ} (ht : 0 < t)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun z : ℝ => wholeLineCauchyHeatHessOp t f z)
      (wholeLineCauchyHeatThirdOp t f x) x := by
  have hbase := heatConvolution_space_third_deriv
    (f := f) (t := t) (x := x) (M := M) ht hf_meas hf
  have hmul := hbase.const_mul (Real.exp (-t))
  have heq : (fun z : ℝ => wholeLineCauchyHeatHessOp t f z) =
      fun z : ℝ => Real.exp (-t) *
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatSemigroup t f w) u) z := by
    funext z
    unfold wholeLineCauchyHeatHessOp
    rw [(ShenWork.PaperOne.ConvLeibniz.heatConvolution_space_second_deriv
      (f := f) (t := t) (x := z) (M := M) ht hf_meas hf).deriv]
  rw [heq]
  simpa [wholeLineCauchyHeatThirdOp] using hmul

/-- The modified heat Hessian inherits the Gaussian off-support gain. -/
theorem wholeLineCauchyHeatHessOp_abs_le_of_zero_ball
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |wholeLineCauchyHeatHessOp t f x| ≤
      (5 / t) * Real.exp (-r ^ 2 / (16 * t)) * M := by
  have hraw := secondDeriv_heatKernel_convolution_zero_ball_abs_le
    ht hM hr hf_meas hf hzero
  have hexp : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
  unfold wholeLineCauchyHeatHessOp
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) *
          |∫ y : ℝ,
            deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x - y) * f y| ≤
        1 *
          |∫ y : ℝ,
            deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
              (x - y) * f y| := by
      gcongr
    _ ≤ (heatHessPointwiseBound t * Real.exp (-r ^ 2 / (16 * t)) * M) *
          Real.sqrt (Real.pi / (1 / (16 * t))) := by simpa using hraw
    _ = (5 / t) * Real.exp (-r ^ 2 / (16 * t)) * M := by
      rw [show
        (heatHessPointwiseBound t * Real.exp (-r ^ 2 / (16 * t)) * M) *
              Real.sqrt (Real.pi / (1 / (16 * t))) =
            (heatHessPointwiseBound t *
              Real.sqrt (Real.pi / (1 / (16 * t)))) *
              Real.exp (-r ^ 2 / (16 * t)) * M by ring]
      rw [heatHessPointwiseBound_mul_tailGaussianScale ht]

/-- The modified heat third derivative inherits the Gaussian off-support gain. -/
theorem wholeLineCauchyHeatThirdOp_abs_le_of_zero_ball
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |wholeLineCauchyHeatThirdOp t f x| ≤
      (heatThirdTailConstant / (t * Real.sqrt t)) *
        Real.exp (-r ^ 2 / (16 * t)) * M := by
  have hraw := thirdDeriv_heatKernel_convolution_zero_ball_abs_le
    ht hM hr hf_meas hf hzero
  have hexp : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
  unfold wholeLineCauchyHeatThirdOp
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) *
          |∫ y : ℝ,
            deriv
              (fun z : ℝ => deriv
                (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
              (x - y) * f y| ≤
        1 *
          |∫ y : ℝ,
            deriv
              (fun z : ℝ => deriv
                (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
              (x - y) * f y| := by
      gcongr
    _ ≤ (heatThirdPointwiseBound t * Real.exp (-r ^ 2 / (16 * t)) * M) *
          Real.sqrt (Real.pi / (1 / (16 * t))) := by simpa using hraw
    _ = (heatThirdTailConstant / (t * Real.sqrt t)) *
          Real.exp (-r ^ 2 / (16 * t)) * M := by
      rw [show
        (heatThirdPointwiseBound t * Real.exp (-r ^ 2 / (16 * t)) * M) *
              Real.sqrt (Real.pi / (1 / (16 * t))) =
            (heatThirdPointwiseBound t *
              Real.sqrt (Real.pi / (1 / (16 * t)))) *
              Real.exp (-r ^ 2 / (16 * t)) * M by ring]
      rw [heatThirdPointwiseBound_mul_tailGaussianScale ht]

/-- Global positive-lag Hessian bound for a bounded source. -/
theorem wholeLineCauchyHeatHessOp_abs_le
    {f : ℝ → ℝ} {t M x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    |wholeLineCauchyHeatHessOp t f x| ≤
      ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ))) * M := by
  let K : ℝ → ℝ := fun y =>
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y)
  have hint : Integrable (fun y : ℝ => K y * f y) := by
    simpa [K] using
      ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
        ht x hf hf_meas
  have hmajor : Integrable (fun y : ℝ => M * |K y|) := by
    have htrans : Integrable (fun y : ℝ => |K y|) := by
      simpa [K, sub_eq_add_neg, add_comm] using
        ((secondDeriv_heatKernel_abs_integrable ht).comp_neg.comp_add_right (-x))
    exact htrans.const_mul M
  have hmass : (∫ y : ℝ, |K y|) =
      ∫ w : ℝ,
        |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| := by
    calc
      (∫ y : ℝ, |K y|) =
          ∫ y : ℝ,
            (fun q : ℝ =>
              |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (-q)|)
              (y - x) := by
            congr 1
            funext y
            simp only [K]
            congr 2
            ring
      _ = ∫ q : ℝ,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (-q)| :=
        integral_sub_right_eq_self (μ := volume)
          (fun q : ℝ =>
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (-q)|)
          x
      _ = ∫ w : ℝ,
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w| :=
        integral_neg_eq_self
          (fun w : ℝ =>
            |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) w|)
          volume
  have hconv : |∫ y : ℝ, K y * f y| ≤
      ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ))) * M := by
    calc
      |∫ y : ℝ, K y * f y| ≤ ∫ y : ℝ, |K y * f y| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ y : ℝ, M * |K y| := by
        refine integral_mono hint.abs hmajor (fun y => ?_)
        rw [abs_mul]
        calc
          |K y| * |f y| ≤ |K y| * M :=
            mul_le_mul_of_nonneg_left (hf y) (abs_nonneg _)
          _ = M * |K y| := by ring
      _ = M * ∫ y : ℝ, |K y| := by rw [integral_const_mul]
      _ ≤ M * ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ))) := by
        gcongr
        rw [hmass]
        exact secondDeriv_heatKernel_abs_integral_le ht
      _ = ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ))) * M := by ring
  have hexp : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
  unfold wholeLineCauchyHeatHessOp
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) * |∫ y : ℝ, K y * f y| ≤
        1 * |∫ y : ℝ, K y * f y| := by gcongr
    _ ≤ ((5 * Real.sqrt 2 / 2) * t ^ (-(1 : ℝ))) * M := by
      simpa using hconv

/-- Global positive-lag third-derivative bound for a bounded source. -/
theorem wholeLineCauchyHeatThirdOp_abs_le
    {f : ℝ → ℝ} {t M x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    |wholeLineCauchyHeatThirdOp t f x| ≤
      (heatThirdTailConstant / (t * Real.sqrt t)) * M := by
  let K : ℝ → ℝ := fun y =>
    deriv
      (fun z : ℝ => deriv
        (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
      (x - y)
  have hint : Integrable (fun y : ℝ => K y * f y) := by
    simpa [K] using thirdDeriv_heatKernel_mul_bounded_integrable ht x hf hf_meas
  have hmajor : Integrable (fun y : ℝ => M * |K y|) := by
    have htrans : Integrable (fun y : ℝ => |K y|) := by
      simpa [K, sub_eq_add_neg, add_comm] using
        ((thirdDeriv_heatKernel_abs_integrable ht).comp_neg.comp_add_right (-x))
    exact htrans.const_mul M
  have hmass : (∫ y : ℝ, |K y|) =
      ∫ w : ℝ,
        |deriv
          (fun z : ℝ => deriv
            (fun u : ℝ => deriv (fun v : ℝ => heatKernel t v) u) z)
          w| := by
    calc
      (∫ y : ℝ, |K y|) =
          ∫ y : ℝ,
            (fun q : ℝ =>
              |deriv
                (fun z : ℝ => deriv
                  (fun u : ℝ => deriv (fun v : ℝ => heatKernel t v) u) z)
                (-q)|) (y - x) := by
            congr 1
            funext y
            simp only [K]
            congr 2
            ring
      _ = ∫ q : ℝ,
            |deriv
              (fun z : ℝ => deriv
                (fun u : ℝ => deriv (fun v : ℝ => heatKernel t v) u) z)
              (-q)| := integral_sub_right_eq_self (μ := volume)
        (fun q : ℝ =>
          |deriv
            (fun z : ℝ => deriv
              (fun u : ℝ => deriv (fun v : ℝ => heatKernel t v) u) z)
            (-q)|) x
      _ = ∫ w : ℝ,
            |deriv
              (fun z : ℝ => deriv
                (fun u : ℝ => deriv (fun v : ℝ => heatKernel t v) u) z)
              w| := integral_neg_eq_self
        (fun w : ℝ =>
          |deriv
            (fun z : ℝ => deriv
              (fun u : ℝ => deriv (fun v : ℝ => heatKernel t v) u) z)
            w|) volume
  have hconv : |∫ y : ℝ, K y * f y| ≤
      (heatThirdTailConstant / (t * Real.sqrt t)) * M := by
    calc
      |∫ y : ℝ, K y * f y| ≤ ∫ y : ℝ, |K y * f y| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ y : ℝ, M * |K y| := by
        refine integral_mono hint.abs hmajor (fun y => ?_)
        rw [abs_mul]
        calc
          |K y| * |f y| ≤ |K y| * M :=
            mul_le_mul_of_nonneg_left (hf y) (abs_nonneg _)
          _ = M * |K y| := by ring
      _ = M * ∫ y : ℝ, |K y| := by rw [integral_const_mul]
      _ ≤ M * (heatThirdTailConstant / (t * Real.sqrt t)) := by
        gcongr
        rw [hmass]
        exact thirdDeriv_heatKernel_abs_integral_le ht
      _ = (heatThirdTailConstant / (t * Real.sqrt t)) * M := by ring
  have hexp : Real.exp (-t) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
  unfold wholeLineCauchyHeatThirdOp
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) * |∫ y : ℝ, K y * f y| ≤
        1 * |∫ y : ℝ, K y * f y| := by gcongr
    _ ≤ (heatThirdTailConstant / (t * Real.sqrt t)) * M := by
      simpa using hconv

/-- The first inverse-time Gaussian tail is uniformly bounded. -/
theorem inv_mul_exp_neg_div_le
    {tau c : ℝ} (htau : 0 < tau) (hc : 0 < c) :
    (1 / tau) * Real.exp (-c / tau) ≤
      (1 / Real.exp 1) * c⁻¹ := by
  have h := rpow_mul_exp_neg_mul_le (σ := (1 : ℝ)) (by norm_num)
    (lam := 1 / tau) (t := c) (by positivity) hc
  simpa [Real.rpow_one, Real.rpow_neg_one, div_eq_mul_inv, mul_comm] using h

/-- The three-halves inverse-time Gaussian tail is uniformly bounded. -/
theorem inv_mul_sqrt_inv_exp_neg_div_le
    {tau c : ℝ} (htau : 0 < tau) (hc : 0 < c) :
    (1 / (tau * Real.sqrt tau)) * Real.exp (-c / tau) ≤
      (((3 : ℝ) / 2) / Real.exp 1) ^ ((3 : ℝ) / 2) *
        c ^ (-((3 : ℝ) / 2)) := by
  have hpow : (1 / tau) ^ ((3 : ℝ) / 2) =
      1 / (tau * Real.sqrt tau) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_div (by positivity), Real.sqrt_one]
    field_simp
  have h := rpow_mul_exp_neg_mul_le
    (σ := (3 : ℝ) / 2) (by norm_num)
    (lam := 1 / tau) (t := c) (by positivity) hc
  rw [hpow] at h
  simpa [div_eq_mul_inv, mul_comm] using h

/-- Uniform Hessian bound when the source vanishes on a fixed ball. -/
theorem wholeLineCauchyHeatHessOp_abs_le_of_zero_ball_uniform
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |wholeLineCauchyHeatHessOp t f x| ≤
      5 * M * ((1 / Real.exp 1) * (r ^ 2 / 16)⁻¹) := by
  have hc : 0 < r ^ 2 / 16 := by positivity
  have htail := inv_mul_exp_neg_div_le ht hc
  have hop := wholeLineCauchyHeatHessOp_abs_le_of_zero_ball
    ht hM hr hf_meas hf hzero
  have hexponent : -r ^ 2 / (16 * t) = -(r ^ 2 / 16) / t := by
    field_simp [ne_of_gt ht]
  calc
    |wholeLineCauchyHeatHessOp t f x| ≤
        (5 / t) * Real.exp (-r ^ 2 / (16 * t)) * M := hop
    _ = 5 * M * ((1 / t) * Real.exp (-(r ^ 2 / 16) / t)) := by
      rw [hexponent]
      ring
    _ ≤ 5 * M * ((1 / Real.exp 1) * (r ^ 2 / 16)⁻¹) := by
      exact mul_le_mul_of_nonneg_left htail (mul_nonneg (by norm_num) hM)

/-- Uniform third-derivative bound when the source vanishes on a fixed ball. -/
theorem wholeLineCauchyHeatThirdOp_abs_le_of_zero_ball_uniform
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |wholeLineCauchyHeatThirdOp t f x| ≤
      heatThirdTailConstant * M *
        ((((3 : ℝ) / 2) / Real.exp 1) ^ ((3 : ℝ) / 2) *
          (r ^ 2 / 16) ^ (-((3 : ℝ) / 2))) := by
  have hc : 0 < r ^ 2 / 16 := by positivity
  have htail := inv_mul_sqrt_inv_exp_neg_div_le ht hc
  have hop := wholeLineCauchyHeatThirdOp_abs_le_of_zero_ball
    ht hM hr hf_meas hf hzero
  have hexponent : -r ^ 2 / (16 * t) = -(r ^ 2 / 16) / t := by
    field_simp [ne_of_gt ht]
  calc
    |wholeLineCauchyHeatThirdOp t f x| ≤
        (heatThirdTailConstant / (t * Real.sqrt t)) *
          Real.exp (-r ^ 2 / (16 * t)) * M := hop
    _ = heatThirdTailConstant * M *
          ((1 / (t * Real.sqrt t)) * Real.exp (-(r ^ 2 / 16) / t)) := by
      rw [hexponent]
      ring
    _ ≤ heatThirdTailConstant * M *
          ((((3 : ℝ) / 2) / Real.exp 1) ^ ((3 : ℝ) / 2) *
            (r ^ 2 / 16) ^ (-((3 : ℝ) / 2))) := by
      exact mul_le_mul_of_nonneg_left htail
        (mul_nonneg heatThirdTailConstant_nonneg hM)

/-- A terminal space-time zero neighborhood removes the Hessian singularity
from an entire Duhamel history. -/
theorem wholeLineCauchyHeatHessOp_history_uniform_bound
    {F : ℝ → WholeLineBUC} {t M delta r x : ℝ}
    (hM : 0 ≤ M) (hdelta : 0 < delta) (hr : 0 < r)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hzero : ∀ s, 0 ≤ s → s < t → t - delta < s →
      ∀ y, dist y x < r → (F s).1 y = 0) :
    ∃ C ≥ 0, ∀ s, 0 ≤ s → s < t →
      ∀ z ∈ Metric.ball x (r / 2),
        |wholeLineCauchyHeatHessOp (t - s) (F s).1 z| ≤ C := by
  let Cold : ℝ :=
    ((5 * Real.sqrt 2 / 2) * delta ^ (-(1 : ℝ))) * M
  let Crecent : ℝ :=
    5 * M * ((1 / Real.exp 1) * ((r / 2) ^ 2 / 16)⁻¹)
  have hCold : 0 ≤ Cold := by
    dsimp [Cold]
    positivity
  have hCrecent : 0 ≤ Crecent := by
    dsimp [Crecent]
    positivity
  refine ⟨max Cold Crecent, le_max_of_le_left hCold, ?_⟩
  intro s hs0 hst z hz
  have htau : 0 < t - s := sub_pos.mpr hst
  have hf : ∀ y, |(F s).1 y| ≤ M := fun y =>
    (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
  by_cases hold : s ≤ t - delta
  · have hlag : delta ≤ t - s := by linarith
    have hinv : (t - s) ^ (-(1 : ℝ)) ≤ delta ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one, Real.rpow_neg_one]
      simpa [one_div] using one_div_le_one_div_of_le hdelta hlag
    have hglobal := wholeLineCauchyHeatHessOp_abs_le (x := z)
      htau hM (F s).1.continuous.aestronglyMeasurable hf
    refine hglobal.trans (le_max_of_le_left ?_)
    dsimp [Cold]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinv (by positivity)) hM
  · have hnear : t - delta < s := lt_of_not_ge hold
    have hzero_z : ∀ y, dist y z < r / 2 → (F s).1 y = 0 := by
      intro y hy
      apply hzero s hs0 hst hnear y
      have hzx : dist z x < r / 2 := by
        simpa [Metric.mem_ball] using hz
      calc
        dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add hy hzx
        _ = r := by ring
    have hrecent := wholeLineCauchyHeatHessOp_abs_le_of_zero_ball_uniform (x := z)
      htau hM (half_pos hr) (F s).1.continuous.aestronglyMeasurable hf hzero_z
    exact hrecent.trans (le_max_right _ _)

/-- A terminal space-time zero neighborhood likewise removes the third-kernel
singularity from an entire Duhamel history. -/
theorem wholeLineCauchyHeatThirdOp_history_uniform_bound
    {F : ℝ → WholeLineBUC} {t M delta r x : ℝ}
    (hM : 0 ≤ M) (hdelta : 0 < delta) (hr : 0 < r)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hzero : ∀ s, 0 ≤ s → s < t → t - delta < s →
      ∀ y, dist y x < r → (F s).1 y = 0) :
    ∃ C ≥ 0, ∀ s, 0 ≤ s → s < t →
      ∀ z ∈ Metric.ball x (r / 2),
        |wholeLineCauchyHeatThirdOp (t - s) (F s).1 z| ≤ C := by
  let Cold : ℝ :=
    (heatThirdTailConstant / (delta * Real.sqrt delta)) * M
  let Crecent : ℝ :=
    heatThirdTailConstant * M *
      ((((3 : ℝ) / 2) / Real.exp 1) ^ ((3 : ℝ) / 2) *
        (((r / 2) ^ 2 / 16) ^ (-((3 : ℝ) / 2))))
  have hCold : 0 ≤ Cold := by
    dsimp [Cold]
    exact mul_nonneg
      (div_nonneg heatThirdTailConstant_nonneg
        (mul_nonneg hdelta.le (Real.sqrt_nonneg _))) hM
  have hCrecent : 0 ≤ Crecent := by
    dsimp [Crecent]
    exact mul_nonneg (mul_nonneg heatThirdTailConstant_nonneg hM)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _))
  refine ⟨max Cold Crecent, le_max_of_le_left hCold, ?_⟩
  intro s hs0 hst z hz
  have htau : 0 < t - s := sub_pos.mpr hst
  have hf : ∀ y, |(F s).1 y| ≤ M := fun y =>
    (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
  by_cases hold : s ≤ t - delta
  · have hlag : delta ≤ t - s := by linarith
    have hsqrt : Real.sqrt delta ≤ Real.sqrt (t - s) :=
      Real.sqrt_le_sqrt hlag
    have hprod : delta * Real.sqrt delta ≤
        (t - s) * Real.sqrt (t - s) :=
      mul_le_mul hlag hsqrt (Real.sqrt_nonneg _) htau.le
    have hinv : 1 / ((t - s) * Real.sqrt (t - s)) ≤
        1 / (delta * Real.sqrt delta) :=
      one_div_le_one_div_of_le (mul_pos hdelta (Real.sqrt_pos.mpr hdelta)) hprod
    have hglobal := wholeLineCauchyHeatThirdOp_abs_le (x := z)
      htau hM (F s).1.continuous.aestronglyMeasurable hf
    refine hglobal.trans (le_max_of_le_left ?_)
    dsimp [Cold]
    have hcoef := mul_le_mul_of_nonneg_left hinv heatThirdTailConstant_nonneg
    exact mul_le_mul_of_nonneg_right (by simpa [div_eq_mul_inv] using hcoef) hM
  · have hnear : t - delta < s := lt_of_not_ge hold
    have hzero_z : ∀ y, dist y z < r / 2 → (F s).1 y = 0 := by
      intro y hy
      apply hzero s hs0 hst hnear y
      have hzx : dist z x < r / 2 := by
        simpa [Metric.mem_ball] using hz
      calc
        dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
        _ < r / 2 + r / 2 := add_lt_add hy hzx
        _ = r := by ring
    have hrecent := wholeLineCauchyHeatThirdOp_abs_le_of_zero_ball_uniform (x := z)
      htau hM (half_pos hr) (F s).1.continuous.aestronglyMeasurable hf hzero_z
    exact hrecent.trans (le_max_right _ _)

theorem wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable
    {F : ℝ → WholeLineBUC} (hF : Continuous F) (t x : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (F s).1 x) volume := by
  let J : ℝ × ℝ → ℝ := fun q =>
    deriv
      (fun u : ℝ => deriv (fun z : ℝ => heatKernel (t - q.1) z) u)
      (x - q.2) * (F q.1).1 q.2
  have hsource : Continuous (fun q : ℝ × ℝ => (F q.1).1 q.2) := by
    fun_prop
  have hJ : AEStronglyMeasurable J (volume.prod volume) := by
    exact (measurable_secondDeriv_heatKernel_comp (by fun_prop) (by fun_prop)).aestronglyMeasurable.mul
      hsource.aestronglyMeasurable
  have hint : AEStronglyMeasurable (fun s : ℝ => ∫ y : ℝ, J (s, y)) volume :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := volume) (f := J) hJ
  have hexp : StronglyMeasurable (fun s : ℝ => Real.exp (-(t - s))) := by
    fun_prop
  simpa [wholeLineCauchyHeatHessOp, J] using
    hexp.aestronglyMeasurable.mul hint

theorem wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable
    {F : ℝ → WholeLineBUC} (hF : Continuous F) (t x : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) volume := by
  let J : ℝ × ℝ → ℝ := fun q =>
    deriv
      (fun z : ℝ => deriv
        (fun u : ℝ => deriv (fun w : ℝ => heatKernel (t - q.1) w) u) z)
      (x - q.2) * (F q.1).1 q.2
  have hsource : Continuous (fun q : ℝ × ℝ => (F q.1).1 q.2) := by
    fun_prop
  have hJ : AEStronglyMeasurable J (volume.prod volume) := by
    exact (measurable_thirdDeriv_heatKernel_comp (by fun_prop) (by fun_prop)).aestronglyMeasurable.mul
      hsource.aestronglyMeasurable
  have hint : AEStronglyMeasurable (fun s : ℝ => ∫ y : ℝ, J (s, y)) volume :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := volume) (f := J) hJ
  have hexp : StronglyMeasurable (fun s : ℝ => Real.exp (-(t - s))) := by
    fun_prop
  simpa [wholeLineCauchyHeatThirdOp, J] using
    hexp.aestronglyMeasurable.mul hint

theorem wholeLineCauchyHeatOp_s_dependent_aestronglyMeasurable
    {F : ℝ → WholeLineBUC} (hF : Continuous F) (t x : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => wholeLineCauchyHeatOp (t - s) (F s).1 x) volume := by
  let J : ℝ × ℝ → ℝ := fun q =>
    heatKernel (t - q.1) (x - q.2) * (F q.1).1 q.2
  have hsource : Continuous (fun q : ℝ × ℝ => (F q.1).1 q.2) := by
    fun_prop
  have hJ : AEStronglyMeasurable J (volume.prod volume) := by
    exact (measurable_heatKernel_comp (by fun_prop) t).aestronglyMeasurable.mul
      hsource.aestronglyMeasurable
  have hint : AEStronglyMeasurable (fun s : ℝ => ∫ y : ℝ, J (s, y)) volume :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := volume) (f := J) hJ
  have hexp : StronglyMeasurable (fun s : ℝ => Real.exp (-(t - s))) := by
    fun_prop
  simpa [wholeLineCauchyHeatOp, modifiedSemigroup, heatSemigroup, J] using
    hexp.aestronglyMeasurable.mul hint

theorem wholeLineCauchyHeatGradOp_s_dependent_aestronglyMeasurable
    {F : ℝ → WholeLineBUC} (hF : Continuous F) (t x : ℝ) :
    AEStronglyMeasurable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (t - s) (F s).1 x) volume := by
  let J : ℝ × ℝ → ℝ := fun q =>
    deriv (fun z : ℝ => heatKernel (t - q.1) (z - q.2)) x *
      (F q.1).1 q.2
  have hsource : Continuous (fun q : ℝ × ℝ => (F q.1).1 q.2) := by
    fun_prop
  have hJ : AEStronglyMeasurable J (volume.prod volume) := by
    have heq : J = fun q : ℝ × ℝ =>
        deriv (fun z : ℝ => heatKernel (t - q.1) z) (x - q.2) *
          (F q.1).1 q.2 := by
      funext q
      unfold J
      rw [deriv_heatKernel_translated_left_global]
    rw [heq]
    exact (measurable_deriv_heatKernel_comp (by fun_prop) t).aestronglyMeasurable.mul
      hsource.aestronglyMeasurable
  have hint : AEStronglyMeasurable (fun s : ℝ => ∫ y : ℝ, J (s, y)) volume :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := volume) (ν := volume) (f := J) hJ
  have hexp : StronglyMeasurable (fun s : ℝ => Real.exp (-(t - s))) := by
    fun_prop
  have heq : (fun s : ℝ => wholeLineCauchyHeatGradOp (t - s) (F s).1 x) =
      fun s : ℝ => Real.exp (-(t - s)) * ∫ y : ℝ, J (s, y) := by
    funext s
    unfold wholeLineCauchyHeatGradOp
    rw [integral_const_mul]
  rw [heq]
  exact hexp.aestronglyMeasurable.mul hint

def wholeLineCauchyValueHistory
    (F : ℝ → WholeLineBUC) (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, wholeLineCauchyHeatOp (t - s) (F s).1 x

def wholeLineCauchyGradientHistory
    (F : ℝ → WholeLineBUC) (t x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, wholeLineCauchyHeatGradOp (t - s) (F s).1 x

/-- Finite-interval integrability from an a.e.-measurable uniform bound. -/
theorem intervalIntegrable_of_aestronglyMeasurable_of_norm_le
    {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable f volume)
    (hbound : ∀ s ∈ Set.Icc a b, ‖f s‖ ≤ C) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply Measure.integrableOn_of_bounded (μ := volume)
    (s := Set.Icc a b) (by simp [Real.volume_Icc]) hmeas
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact hbound s hs

/-- The uniformly bounded Hessian history is interval-integrable, including
the harmless zero-lag endpoint. -/
theorem wholeLineCauchyHeatHessOp_history_intervalIntegrable
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M delta r x : ℝ} (ht : 0 < t)
    (hM : 0 ≤ M) (hdelta : 0 < delta) (hr : 0 < r)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hzero : ∀ s, 0 ≤ s → s < t → t - delta < s →
      ∀ y, dist y x < r → (F s).1 y = 0) :
    ∃ C ≥ 0,
      IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (F s).1 x)
        volume 0 t ∧
      ∀ s, 0 ≤ s → s < t →
        ∀ z ∈ Metric.ball x (r / 2),
          ‖wholeLineCauchyHeatHessOp (t - s) (F s).1 z‖ ≤ C := by
  rcases wholeLineCauchyHeatHessOp_history_uniform_bound
      hM hdelta hr hFnorm hzero with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_, ?_⟩
  · apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le ht.le
      (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable hF t x)
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hst | rfl
    · have hxball : x ∈ Metric.ball x (r / 2) := by
        simp [Metric.mem_ball, half_pos hr]
      simpa [Real.norm_eq_abs] using hbound s hs.1 hst x hxball
    · rw [sub_self, wholeLineCauchyHeatHessOp_eq_zero_of_nonpos (le_refl 0)]
      simpa using hC
  · intro s hs0 hst z hz
    simpa [Real.norm_eq_abs] using hbound s hs0 hst z hz

/-- The uniformly bounded third-derivative history is interval-integrable,
again with the zero-lag endpoint filled by zero. -/
theorem wholeLineCauchyHeatThirdOp_history_intervalIntegrable
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M delta r x : ℝ} (ht : 0 < t)
    (hM : 0 ≤ M) (hdelta : 0 < delta) (hr : 0 < r)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hzero : ∀ s, 0 ≤ s → s < t → t - delta < s →
      ∀ y, dist y x < r → (F s).1 y = 0) :
    ∃ C ≥ 0,
      IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatThirdOp (t - s) (F s).1 x)
        volume 0 t ∧
      ∀ s, 0 ≤ s → s < t →
        ∀ z ∈ Metric.ball x (r / 2),
          ‖wholeLineCauchyHeatThirdOp (t - s) (F s).1 z‖ ≤ C := by
  rcases wholeLineCauchyHeatThirdOp_history_uniform_bound
      hM hdelta hr hFnorm hzero with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_, ?_⟩
  · apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le ht.le
      (wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable hF t x)
    intro s hs
    rcases lt_or_eq_of_le hs.2 with hst | rfl
    · have hxball : x ∈ Metric.ball x (r / 2) := by
        simp [Metric.mem_ball, half_pos hr]
      simpa [Real.norm_eq_abs] using hbound s hs.1 hst x hxball
    · rw [sub_self, wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos (le_refl 0)]
      simpa using hC
  · intro s hs0 hst z hz
    simpa [Real.norm_eq_abs] using hbound s hs0 hst z hz

/-- The product neighborhood supplied by strict negativity can be rewritten
in the terminal-history form consumed by the off-support estimates. -/
theorem wholeLineCauchy_sourceTrajectories_terminal_zero_near_negative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) (hneg : (U z).1 x < 0) :
    ∃ delta > 0, ∃ r > 0,
      (∀ s, 0 ≤ s → s < z.1 → z.1 - delta < s →
        ∀ y, dist y x < r →
          (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 y = 0) ∧
      (∀ s, 0 ≤ s → s < z.1 → z.1 - delta < s →
        ∀ y, dist y x < r →
          (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 y = 0) := by
  rcases wholeLineCauchy_sourceTrajectories_zero_near_negative
      p hM hT U z x hneg with ⟨eps, heps, hlocal⟩
  refine ⟨eps / 2, half_pos heps, eps, heps, ?_⟩
  constructor
  · intro s hs0 hst hnear y hy
    let w : Set.Icc (0 : ℝ) T :=
      ⟨s, hs0, le_trans hst.le z.2.2⟩
    have hw : dist w z < eps := by
      change dist s z.1 < eps
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst.le)]
      linarith
    exact (hlocal w y hw hy).1
  · intro s hs0 hst hnear y hy
    let w : Set.Icc (0 : ℝ) T :=
      ⟨s, hs0, le_trans hst.le z.2.2⟩
    have hw : dist w z < eps := by
      change dist s z.1 < eps
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst.le)]
      linarith
    exact (hlocal w y hw hy).2

/-- Every continuous bounded BUC source has an integrable first-gradient
Duhamel history. -/
theorem wholeLineCauchyGradientHistory_intervalIntegrable
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hFnorm : ∀ s, ‖F s‖ ≤ M) (x : ℝ) :
    IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (t - s) (F s).1 x)
      volume 0 t := by
  have hjoint : Continuous (fun q : ℝ × ℝ => (F q.1).1 q.2) := by
    fun_prop
  let G : ℝ → ℝ → ℝ := fun s y => (F s).1 y
  have hGmeas : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod volume) := by
    simpa [G, Function.uncurry] using hjoint.aestronglyMeasurable
  apply wholeLineHeatGradOp_intervalIntegrable_of_jointMeasurable
    (F := G) ht hM hGmeas _ x
  intro s hs y
  exact (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)

/-- First spatial derivative of a gradient Duhamel history under an explicit
integrable Hessian majorant. -/
theorem wholeLineCauchyGradientHistory_hasDerivAt
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t x M ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hgrad_int : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (t - s) (F s).1 x) volume 0 t)
    {bound : ℝ → ℝ} (hbound_int : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ s, 0 ≤ s → s < t → ∀ z ∈ Metric.ball x ρ,
      ‖wholeLineCauchyHeatHessOp (t - s) (F s).1 z‖ ≤ bound s) :
    HasDerivAt (fun z : ℝ => wholeLineCauchyGradientHistory F t z)
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (F s).1 x) x := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := t)
    (F := fun z s => wholeLineCauchyHeatGradOp (t - s) (F s).1 z)
    (F' := fun z s => wholeLineCauchyHeatHessOp (t - s) (F s).1 z)
    (x₀ := x) (s := Metric.ball x ρ) (bound := bound)
    (Metric.ball_mem_nhds x hρ)
    ?hF_meas hgrad_int
    ?hF'_meas ?h_bound hbound_int ?h_diff).2
  · filter_upwards with z
    exact (wholeLineCauchyHeatGradOp_s_dependent_aestronglyMeasurable hF t z).restrict
  · exact (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable hF t x).restrict
  · filter_upwards [hne] with s hst hsI z hz
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
    exact hbound s hsI.1.le (lt_of_le_of_ne hsI.2 hst) z hz
  · filter_upwards [hne] with s hst hsI z hz
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
    have hstlt : s < t := lt_of_le_of_ne hsI.2 hst
    apply wholeLineCauchyHeatGradOp_hasDerivAt (sub_pos.mpr hstlt)
      (F s).1.continuous.aestronglyMeasurable
    intro y
    exact (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)

/-- Second spatial derivative of a gradient Duhamel history under an explicit
integrable third-kernel majorant. -/
theorem wholeLineCauchyGradientHistory_second_hasDerivAt
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t x M ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hfirst : ∀ z, deriv (fun w : ℝ => wholeLineCauchyGradientHistory F t w) z =
      ∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (F s).1 z)
    (hhess_int : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (F s).1 x) volume 0 t)
    {bound : ℝ → ℝ} (hbound_int : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ s, 0 ≤ s → s < t → ∀ z ∈ Metric.ball x ρ,
      ‖wholeLineCauchyHeatThirdOp (t - s) (F s).1 z‖ ≤ bound s) :
    HasDerivAt
      (fun z : ℝ => deriv (fun w : ℝ => wholeLineCauchyGradientHistory F t w) z)
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) x := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hderiv_eq :
      (fun z : ℝ => deriv (fun w : ℝ => wholeLineCauchyGradientHistory F t w) z) =
      fun z : ℝ => ∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (F s).1 z := by
    funext z
    exact hfirst z
  rw [hderiv_eq]
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := t)
    (F := fun z s => wholeLineCauchyHeatHessOp (t - s) (F s).1 z)
    (F' := fun z s => wholeLineCauchyHeatThirdOp (t - s) (F s).1 z)
    (x₀ := x) (s := Metric.ball x ρ) (bound := bound)
    (Metric.ball_mem_nhds x hρ)
    ?hF_meas hhess_int
    ?hF'_meas ?h_bound hbound_int ?h_diff).2
  · filter_upwards with z
    exact (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable hF t z).restrict
  · exact (wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable hF t x).restrict
  · filter_upwards [hne] with s hst hsI z hz
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
    exact hbound s hsI.1.le (lt_of_le_of_ne hsI.2 hst) z hz
  · filter_upwards [hne] with s hst hsI z hz
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
    have hstlt : s < t := lt_of_le_of_ne hsI.2 hst
    apply wholeLineCauchyHeatHessOp_hasDerivAt (sub_pos.mpr hstlt)
      (F s).1.continuous.aestronglyMeasurable
    intro y
    exact (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)

/-- Local form of the preceding theorem.  Only a neighborhood of the target
point needs the first-derivative identity; this is the form naturally supplied
by a source that vanishes near one negative point. -/
theorem wholeLineCauchyGradientHistory_second_hasDerivAt_local
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t x M rho : ℝ} (ht : 0 < t) (hrho : 0 < rho)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hfirst : ∀ z ∈ Metric.ball x rho,
      HasDerivAt (fun w : ℝ => wholeLineCauchyGradientHistory F t w)
        (∫ s in (0 : ℝ)..t,
          wholeLineCauchyHeatHessOp (t - s) (F s).1 z) z)
    (hhess_int : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatHessOp (t - s) (F s).1 x) volume 0 t)
    {bound : ℝ → ℝ} (hbound_int : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ s, 0 ≤ s → s < t → ∀ z ∈ Metric.ball x rho,
      ‖wholeLineCauchyHeatThirdOp (t - s) (F s).1 z‖ ≤ bound s) :
    HasDerivAt
      (fun z : ℝ => deriv (fun w : ℝ => wholeLineCauchyGradientHistory F t w) z)
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatThirdOp (t - s) (F s).1 x) x := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hG := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := t)
    (F := fun z s => wholeLineCauchyHeatHessOp (t - s) (F s).1 z)
    (F' := fun z s => wholeLineCauchyHeatThirdOp (t - s) (F s).1 z)
    (x₀ := x) (s := Metric.ball x rho) (bound := bound)
    (Metric.ball_mem_nhds x hrho)
    (by
      filter_upwards with z
      exact (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable hF t z).restrict)
    hhess_int
    (wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable hF t x).restrict
    (by
      filter_upwards [hne] with s hst hsI z hz
      rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
      exact hbound s hsI.1.le (lt_of_le_of_ne hsI.2 hst) z hz)
    hbound_int
    (by
      filter_upwards [hne] with s hst hsI z hz
      rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
      have hstlt : s < t := lt_of_le_of_ne hsI.2 hst
      apply wholeLineCauchyHeatHessOp_hasDerivAt (sub_pos.mpr hstlt)
        (F s).1.continuous.aestronglyMeasurable
      intro y
      exact (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s))).2
  apply hG.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds x hrho] with z hz
  exact (hfirst z hz).deriv

/-- At a strictly negative trajectory point, the chemotaxis Duhamel history
has the two spatial derivatives needed for the local homogeneous PDE. -/
theorem wholeLineCauchyFluxGradientHistory_second_hasDerivAt_at_negative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) (ht : 0 < z.1)
    (hneg : (U z).1 x < 0) :
    HasDerivAt
      (fun xi : ℝ => deriv
        (fun w : ℝ => wholeLineCauchyGradientHistory
          (wholeLineCauchyFluxSourceTrajectory p hM hT U) z.1 w) xi)
      (∫ s in (0 : ℝ)..z.1,
        wholeLineCauchyHeatThirdOp (z.1 - s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 x) x := by
  let F : ℝ → WholeLineBUC :=
    wholeLineCauchyFluxSourceTrajectory p hM hT U
  let MF : ℝ := M ^ p.m * M ^ p.γ
  have hMF : 0 ≤ MF := by
    dsimp [MF]
    exact mul_nonneg (Real.rpow_nonneg hM _) (Real.rpow_nonneg hM _)
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyFluxSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MF := by
    intro s
    simpa [F, MF, wholeLineCauchyFluxSourceTrajectory] using
      wholeLineCauchyTruncatedFluxBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  rcases wholeLineCauchy_sourceTrajectories_terminal_zero_near_negative
      p hM hT U z x hneg with
    ⟨delta, hdelta, r, hr, hzeroFlux, _hzeroReaction⟩
  have hzeroF : ∀ s, 0 ≤ s → s < z.1 → z.1 - delta < s →
      ∀ y, dist y x < r → (F s).1 y = 0 := by
    simpa [F] using hzeroFlux
  have hgrad : ∀ q : ℝ,
      IntervalIntegrable
        (fun s : ℝ => wholeLineCauchyHeatGradOp (z.1 - s) (F s).1 q)
        volume 0 z.1 := fun q =>
    wholeLineCauchyGradientHistory_intervalIntegrable hFcont ht hMF hFnorm q
  rcases wholeLineCauchyHeatHessOp_history_intervalIntegrable
      hFcont ht hMF hdelta hr hFnorm hzeroF with
    ⟨CH, hCH, hHessInt, hHessBound⟩
  rcases wholeLineCauchyHeatThirdOp_history_intervalIntegrable
      hFcont ht hMF hdelta hr hFnorm hzeroF with
    ⟨CT, hCT, _hThirdInt, hThirdBound⟩
  have hr4 : 0 < r / 4 := by positivity
  have hfirst : ∀ q ∈ Metric.ball x (r / 4),
      HasDerivAt (fun w : ℝ => wholeLineCauchyGradientHistory F z.1 w)
        (∫ s in (0 : ℝ)..z.1,
          wholeLineCauchyHeatHessOp (z.1 - s) (F s).1 q) q := by
    intro q hq
    apply wholeLineCauchyGradientHistory_hasDerivAt
      (bound := fun _ : ℝ => CH)
      hFcont ht hr4 hFnorm (hgrad q) intervalIntegrable_const
    intro s hs0 hst w hw
    apply hHessBound s hs0 hst w
    have hqx : dist q x < r / 4 := by
      simpa [Metric.mem_ball] using hq
    have hwq : dist w q < r / 4 := by
      simpa [Metric.mem_ball] using hw
    calc
      dist w x ≤ dist w q + dist q x := dist_triangle _ _ _
      _ < r / 4 + r / 4 := add_lt_add hwq hqx
      _ = r / 2 := by ring
  change HasDerivAt
    (fun xi : ℝ => deriv
      (fun w : ℝ => wholeLineCauchyGradientHistory F z.1 w) xi)
    (∫ s in (0 : ℝ)..z.1,
      wholeLineCauchyHeatThirdOp (z.1 - s) (F s).1 x) x
  apply wholeLineCauchyGradientHistory_second_hasDerivAt_local
    (bound := fun _ : ℝ => CT)
    hFcont ht hr4 hFnorm hfirst hHessInt intervalIntegrable_const
  intro s hs0 hst q hq
  apply hThirdBound s hs0 hst q
  have hqx : dist q x < r / 4 := by
    simpa [Metric.mem_ball] using hq
  have : dist q x < r / 2 := hqx.trans (by linarith [hr])
  simpa [Metric.mem_ball] using this

/-- First spatial derivative of a value Duhamel history. -/
theorem wholeLineCauchyValueHistory_hasDerivAt
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t x M ρ : ℝ} (ht : 0 < t) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hvalue_int : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatOp (t - s) (F s).1 x) volume 0 t) :
    HasDerivAt (fun z : ℝ => wholeLineCauchyValueHistory F t z)
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatGradOp (t - s) (F s).1 x) x := by
  let bound : ℝ → ℝ := fun s =>
    ((2 / Real.sqrt (4 * Real.pi)) * M) *
      (t - s) ^ (-(1 / 2 : ℝ))
  have hbound_int : IntervalIntegrable bound volume 0 t :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul _
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := t)
    (F := fun z s => wholeLineCauchyHeatOp (t - s) (F s).1 z)
    (F' := fun z s => wholeLineCauchyHeatGradOp (t - s) (F s).1 z)
    (x₀ := x) (s := Metric.ball x ρ) (bound := bound)
    (Metric.ball_mem_nhds x hρ)
    ?hF_meas hvalue_int
    ?hF'_meas ?h_bound hbound_int ?h_diff).2
  · filter_upwards with z
    exact (wholeLineCauchyHeatOp_s_dependent_aestronglyMeasurable hF t z).restrict
  · exact (wholeLineCauchyHeatGradOp_s_dependent_aestronglyMeasurable hF t x).restrict
  · filter_upwards [hne] with s hst hsI z hz
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
    have hstlt : s < t := lt_of_le_of_ne hsI.2 hst
    exact wholeLineCauchyHeatGradOp_norm_le_rpow
      (sub_pos.mpr hstlt) hM
      (fun y => (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)) z
  · filter_upwards [hne] with s hst hsI z hz
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
    have hstlt : s < t := lt_of_le_of_ne hsI.2 hst
    apply wholeLineCauchyHeatOp_hasDerivAt (sub_pos.mpr hstlt)
      (F s).1.continuous.aestronglyMeasurable
    intro y
    exact (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)

/-- Second spatial derivative of a value Duhamel history under an explicit
integrable Hessian majorant. -/
theorem wholeLineCauchyValueHistory_second_hasDerivAt
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t x M ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hfirst : ∀ z, deriv (fun w : ℝ => wholeLineCauchyValueHistory F t w) z =
      ∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatGradOp (t - s) (F s).1 z)
    (hgrad_int : IntervalIntegrable
      (fun s : ℝ => wholeLineCauchyHeatGradOp (t - s) (F s).1 x) volume 0 t)
    {bound : ℝ → ℝ} (hbound_int : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ s, 0 ≤ s → s < t → ∀ z ∈ Metric.ball x ρ,
      ‖wholeLineCauchyHeatHessOp (t - s) (F s).1 z‖ ≤ bound s) :
    HasDerivAt
      (fun z : ℝ => deriv (fun w : ℝ => wholeLineCauchyValueHistory F t w) z)
      (∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatHessOp (t - s) (F s).1 x) x := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
  have hderiv_eq :
      (fun z : ℝ => deriv (fun w : ℝ => wholeLineCauchyValueHistory F t w) z) =
      fun z : ℝ => ∫ s in (0 : ℝ)..t,
        wholeLineCauchyHeatGradOp (t - s) (F s).1 z := by
    funext z
    exact hfirst z
  rw [hderiv_eq]
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := t)
    (F := fun z s => wholeLineCauchyHeatGradOp (t - s) (F s).1 z)
    (F' := fun z s => wholeLineCauchyHeatHessOp (t - s) (F s).1 z)
    (x₀ := x) (s := Metric.ball x ρ) (bound := bound)
    (Metric.ball_mem_nhds x hρ)
    ?hF_meas hgrad_int
    ?hF'_meas ?h_bound hbound_int ?h_diff).2
  · filter_upwards with z
    exact (wholeLineCauchyHeatGradOp_s_dependent_aestronglyMeasurable hF t z).restrict
  · exact (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable hF t x).restrict
  · filter_upwards [hne] with s hst hsI z hz
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
    exact hbound s hsI.1.le (lt_of_le_of_ne hsI.2 hst) z hz
  · filter_upwards [hne] with s hst hsI z hz
    rw [Set.uIoc_of_le ht.le, Set.mem_Ioc] at hsI
    have hstlt : s < t := lt_of_le_of_ne hsI.2 hst
    apply wholeLineCauchyHeatGradOp_hasDerivAt (sub_pos.mpr hstlt)
      (F s).1.continuous.aestronglyMeasurable
    intro y
    exact (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)

section WholeLineCauchyBUCOffSupportAxiomAudit

#print axioms wholeLineCauchyHeatOp_hasDerivAt
#print axioms wholeLineCauchyHeatGradOp_hasDerivAt
#print axioms wholeLineCauchyHeatHessOp_hasDerivAt
#print axioms wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable
#print axioms wholeLineCauchyFluxGradientHistory_second_hasDerivAt_at_negative

end WholeLineCauchyBUCOffSupportAxiomAudit

end ShenWork.Paper1
