/-
  ShenWork/PDE/HeatSemigroup.lean

  The heat semigroup e^{tΔ} on ℝ and its basic properties.
  This is the fundamental tool for studying parabolic equations.

  The heat kernel: G(t,x) = (4πt)^{-1/2} exp(-x²/(4t))
  The semigroup: (e^{tΔ} f)(x) = ∫ G(t,x-y) f(y) dy

  Properties needed:
  1. ∫ G(t,x) dx = 1 (conservation of mass)
  2. e^{tΔ} maps C^b_unif to itself
  3. L^p → L^q smoothing estimates (Lemma 2.1)
  4. Gradient estimates
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSq
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Filter Topology Real

noncomputable section

/-- The heat kernel on ℝ at time t > 0. -/
def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))

/-- The heat semigroup acting on a function f. -/
def heatSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, heatKernel t (x - y) * f y

/-- The modified semigroup e^{(Δ-I)t} = e^{-t} e^{tΔ} used in the paper. -/
def modifiedSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-t) * heatSemigroup t f x

/-! ## Basic properties of the heat kernel -/

/-- The heat kernel is nonneg for t > 0. -/
lemma heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ heatKernel t x := by
  unfold heatKernel
  have hcoeff : 0 ≤ 1 / Real.sqrt (4 * Real.pi * t) := by positivity
  exact mul_nonneg hcoeff (Real.exp_nonneg _)

/-- The heat kernel is strictly positive for positive time. -/
lemma heatKernel_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel t x := by
  unfold heatKernel
  have hden : 0 < Real.sqrt (4 * Real.pi * t) := by
    exact Real.sqrt_pos.2 (by positivity)
  exact mul_pos (div_pos zero_lt_one hden) (Real.exp_pos _)

/-- The heat kernel pointwise bound: `G(t,x) ≤ 1 / sqrt(4πt)`. -/
theorem heatKernel_pointwise_bound {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatKernel t x ≤ 1 / Real.sqrt (4 * Real.pi * t) := by
  unfold heatKernel
  exact mul_le_of_le_one_right
    (div_nonneg one_pos.le (Real.sqrt_nonneg _))
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg x)) (by linarith)))

/-- The heat kernel integrates to 1: ∫ G(t,x) dx = 1 for t > 0.
    This is the Gaussian integral. -/
theorem heatKernel_integral_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, heatKernel t x = 1 := by
  unfold heatKernel
  rw [show (fun x : ℝ => 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))) =
    (fun x => 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-(1/(4*t)) * x ^ 2)) from by
      ext x; congr 1; ring]
  rw [MeasureTheory.integral_const_mul, integral_gaussian (1/(4*t))]
  have h4pt : 0 < 4 * Real.pi * t := by positivity
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := Real.sqrt_ne_zero'.mpr h4pt
  field_simp [hsqrt_ne]

theorem heatKernel_integral_abs_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, |heatKernel t x| = 1 := by
  rw [show (fun x : ℝ => |heatKernel t x|) =
      (fun x : ℝ => heatKernel t x) from by
        ext x
        exact abs_of_nonneg (heatKernel_nonneg ht x)]
  exact heatKernel_integral_eq_one ht

/-- The heat kernel is even: G(t, -x) = G(t, x). -/
lemma heatKernel_neg (t x : ℝ) : heatKernel t (-x) = heatKernel t x := by
  unfold heatKernel; congr 1; congr 1; ring

/-- The heat kernel is symmetric: G(t, x-y) = G(t, y-x). -/
lemma heatKernel_sub_comm (t x y : ℝ) :
    heatKernel t (x - y) = heatKernel t (y - x) := by
  rw [show y - x = -(x - y) from by ring, heatKernel_neg]

/-- The heat kernel integrates to 1 after translation: ∫ G(t, x-y) dy = 1. -/
theorem heatKernel_integral_translated {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y : ℝ, heatKernel t (x - y) = 1 := by
  have key : (fun y : ℝ => heatKernel t (x - y)) =
      (fun y => (fun z => heatKernel t z) (y + (-x))) := by
    ext y; simp only; rw [show x - y = -(y + (-x)) from by ring, heatKernel_neg]
  rw [key, integral_add_right_eq_self, heatKernel_integral_eq_one ht]

theorem heatKernel_integral_abs_translated {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y : ℝ, |heatKernel t (x - y)| = 1 := by
  rw [show (fun y : ℝ => |heatKernel t (x - y)|) =
      (fun y : ℝ => heatKernel t (x - y)) from by
        ext y
        exact abs_of_nonneg (heatKernel_nonneg ht (x - y))]
  exact heatKernel_integral_translated ht x

/-- The heat kernel is integrable. -/
lemma heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable (fun x => heatKernel t x) := by
  unfold heatKernel
  have hb : 0 < 1 / (4 * t) := by positivity
  rw [show (fun x : ℝ => 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))) =
    (fun x => 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-(1/(4*t)) * x ^ 2)) from by
      ext x; congr 1; ring]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

lemma heatKernel_hasDerivAt {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun z : ℝ => heatKernel t z)
      (-(x / (2 * t)) * heatKernel t x) x := by
  have hden : 4 * t ≠ 0 := by nlinarith [ht]
  have harg :
      HasDerivAt (fun z : ℝ => -z ^ 2 / (4 * t))
        (-(x / (2 * t))) x := by
    have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
      simpa [pow_two, two_mul] using
        ((hasDerivAt_id x).mul (hasDerivAt_id x))
    have hdiv := hsq.div_const (4 * t)
    have harg0 :
        HasDerivAt (fun z : ℝ => -(z ^ 2 / (4 * t)))
          (-(2 * x / (4 * t))) x :=
      hdiv.neg
    convert harg0 using 1
    · ext z
      field_simp [hden]
    · field_simp [hden]
      ring
  unfold heatKernel
  convert harg.exp.const_mul (1 / Real.sqrt (4 * Real.pi * t)) using 1
  ring

lemma deriv_heatKernel {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv (fun z : ℝ => heatKernel t z) x =
      -(x / (2 * t)) * heatKernel t x :=
  (heatKernel_hasDerivAt ht x).deriv

/-- Pointwise bound for the spatial derivative of the heat kernel. -/
theorem heatKernel_deriv_pointwise_bound {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |deriv (fun z : ℝ => heatKernel t z) x| ≤
      ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
        (Real.sqrt (1 / (4 * t)))⁻¹ := by
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) := by positivity
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt hsqrt_pos
  have hcoeff_nonneg :
      0 ≤ (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) := by
    positivity
  rw [deriv_heatKernel ht]
  unfold heatKernel
  have hrepr :
      -(x / (2 * t)) *
          (1 / Real.sqrt (4 * Real.pi * t) *
            Real.exp (-x ^ 2 / (4 * t))) =
        -(((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
          Real.mulExpNegMulSq (1 / (4 * t)) x) := by
    unfold Real.mulExpNegMulSq
    rw [show -(1 / (4 * t) * x * x) = -x ^ 2 / (4 * t) by ring]
    field_simp [ht_ne, hsqrt_ne]
  rw [hrepr, abs_neg, abs_mul, abs_of_nonneg hcoeff_nonneg]
  exact mul_le_mul_of_nonneg_left
    (Real.abs_mulExpNegMulSq_le (by positivity : 0 < 1 / (4 * t)))
    hcoeff_nonneg

lemma heatKernel_deriv_integrable {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun x : ℝ => deriv (fun z : ℝ => heatKernel t z) x) := by
  have hb : 0 < 1 / (4 * t) := by positivity
  have hbase :
      MeasureTheory.Integrable
        (fun x : ℝ => x * Real.exp (-(1 / (4 * t)) * x ^ 2)) :=
    integrable_mul_exp_neg_mul_sq hb
  convert
    hbase.const_mul (-(1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)))
    using 1
  ext x
  rw [deriv_heatKernel ht]
  unfold heatKernel
  rw [show -x ^ 2 / (4 * t) = -(1 / (4 * t)) * x ^ 2 by ring]
  ring

lemma heatKernel_deriv_abs_integrable {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun x : ℝ => |deriv (fun z : ℝ => heatKernel t z) x|) := by
  simpa [Real.norm_eq_abs] using (heatKernel_deriv_integrable ht).norm

lemma integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) =
      1 / (2 * b) := by
  have h :=
    integral_rpow_mul_exp_neg_mul_rpow
      (p := 2) (q := 1) (b := b)
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (-1 : ℝ) < 1) hb
  rw [show
      ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) =
        ∫ x in Set.Ioi (0 : ℝ), x ^ (1 : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) by
        congr 1
        ext x
        rw [Real.rpow_one]
        congr 1
        rw [Real.rpow_two]]
  rw [h]
  have hpow : b ^ (-(1 + 1) / 2 : ℝ) = b⁻¹ := by
    rw [show (-(1 + 1) / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  rw [hpow, show (((1 : ℝ) + 1) / 2) = 1 by norm_num, Real.Gamma_one]
  field_simp [ne_of_gt hb]

lemma integral_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, |x| * Real.exp (-b * x ^ 2) = 1 / b := by
  have hcomp :=
    integral_comp_abs
      (f := fun x : ℝ => x * Real.exp (-b * x ^ 2))
  have hfun :
      (fun x : ℝ => |x| * Real.exp (-b * x ^ 2)) =
        fun x : ℝ => (fun z : ℝ => z * Real.exp (-b * z ^ 2)) |x| := by
    ext x
    simp [sq_abs]
  rw [hfun, hcomp, integral_Ioi_mul_exp_neg_mul_sq hb]
  field_simp [ne_of_gt hb]

theorem heatKernel_deriv_abs_integral {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, |deriv (fun z : ℝ => heatKernel t z) x| =
      2 / Real.sqrt (4 * Real.pi * t) := by
  have hsqrt_pos : 0 < Real.sqrt (4 * Real.pi * t) := by positivity
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := ne_of_gt hsqrt_pos
  have hcoeff :
      0 < (1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t)) := by
    positivity
  have hfun :
      (fun x : ℝ => |deriv (fun z : ℝ => heatKernel t z) x|) =
        fun x : ℝ =>
          ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
            (|x| * Real.exp (-(1 / (4 * t)) * x ^ 2)) := by
    ext x
    rw [deriv_heatKernel ht]
    unfold heatKernel
    rw [show -x ^ 2 / (4 * t) = -(1 / (4 * t)) * x ^ 2 by ring]
    rw [show
        -(x / (2 * t)) *
            (1 / Real.sqrt (4 * Real.pi * t) *
              Real.exp (-(1 / (4 * t)) * x ^ 2)) =
          -((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
            (x * Real.exp (-(1 / (4 * t)) * x ^ 2)) by
          field_simp [ht_ne, hsqrt_ne]
          ]
    rw [abs_mul, abs_neg, abs_of_pos hcoeff, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_abs_mul_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * t))]
  field_simp [ht_ne, hsqrt_ne]
  ring

lemma modifiedHeatKernel_deriv_abs_integrable {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun x : ℝ => |Real.exp (-t) * deriv (fun z : ℝ => heatKernel t z) x|) := by
  have hfun :
      (fun x : ℝ =>
        |Real.exp (-t) * deriv (fun z : ℝ => heatKernel t z) x|) =
        fun x : ℝ =>
          Real.exp (-t) * |deriv (fun z : ℝ => heatKernel t z) x| := by
    ext x
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun]
  exact (heatKernel_deriv_abs_integrable ht).const_mul (Real.exp (-t))

theorem modifiedHeatKernel_deriv_abs_integral {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, |Real.exp (-t) * deriv (fun z : ℝ => heatKernel t z) x| =
      Real.exp (-t) * (2 / Real.sqrt (4 * Real.pi * t)) := by
  have hfun :
      (fun x : ℝ =>
        |Real.exp (-t) * deriv (fun z : ℝ => heatKernel t z) x|) =
        fun x : ℝ =>
          Real.exp (-t) * |deriv (fun z : ℝ => heatKernel t z) x| := by
    ext x
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun, MeasureTheory.integral_const_mul, heatKernel_deriv_abs_integral ht]

lemma heatKernel_deriv_abs_neg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |deriv (fun z : ℝ => heatKernel t z) (-x)| =
      |deriv (fun z : ℝ => heatKernel t z) x| := by
  rw [deriv_heatKernel ht (-x), deriv_heatKernel ht x, heatKernel_neg]
  rw [show -((-x) / (2 * t)) * heatKernel t x =
      - (-(x / (2 * t) * heatKernel t x)) by ring]
  rw [abs_neg]
  congr 1
  ring

lemma heatKernel_translated_hasDerivAt_left {t : ℝ} (ht : 0 < t)
    (x y : ℝ) :
    HasDerivAt (fun z : ℝ => heatKernel t (z - y))
      (-((x - y) / (2 * t)) * heatKernel t (x - y)) x := by
  simpa using
    (heatKernel_hasDerivAt ht (x - y)).comp x
      ((hasDerivAt_id x).sub (hasDerivAt_const x y))

lemma deriv_heatKernel_translated_left {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun z : ℝ => heatKernel t (z - y)) x =
      -((x - y) / (2 * t)) * heatKernel t (x - y) :=
  (heatKernel_translated_hasDerivAt_left ht x y).deriv

/-- Pointwise bound for translated spatial derivative kernels. -/
theorem heatKernel_deriv_translated_pointwise_bound {t : ℝ} (ht : 0 < t)
    (x y : ℝ) :
    |deriv (fun z : ℝ => heatKernel t (z - y)) x| ≤
      ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
        (Real.sqrt (1 / (4 * t)))⁻¹ := by
  rw [deriv_heatKernel_translated_left ht x y]
  simpa [deriv_heatKernel ht (x - y)] using
    heatKernel_deriv_pointwise_bound ht (x - y)

theorem heatKernel_deriv_abs_integral_translated {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    ∫ y : ℝ, |deriv (fun z : ℝ => heatKernel t (z - y)) x| =
      2 / Real.sqrt (4 * Real.pi * t) := by
  have hleft :
      (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t (z - y)) x|) =
        fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x - y)| := by
    ext y
    rw [deriv_heatKernel_translated_left ht x y, deriv_heatKernel ht (x - y)]
  rw [hleft]
  have hshift :
      (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x - y)|) =
        fun y : ℝ =>
          (fun w : ℝ => |deriv (fun z : ℝ => heatKernel t z) w|)
            (-(y + (-x))) := by
    ext y
    congr 1
    ring
  rw [hshift]
  rw [show
      (fun y : ℝ =>
          (fun w : ℝ => |deriv (fun z : ℝ => heatKernel t z) w|)
            (-(y + (-x)))) =
        (fun y : ℝ =>
          (fun w : ℝ => |deriv (fun z : ℝ => heatKernel t z) (-w)|)
            (y + (-x))) by
        rfl]
  simp_rw [heatKernel_deriv_abs_neg ht]
  rw [show
      (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (y + -x)|) =
        (fun y : ℝ =>
          (fun w : ℝ => |deriv (fun z : ℝ => heatKernel t z) w|)
            (y + (-x))) by
        rfl]
  rw [integral_add_right_eq_self
    (fun w : ℝ => |deriv (fun z : ℝ => heatKernel t z) w|) (-x)]
  exact heatKernel_deriv_abs_integral ht

theorem modifiedHeatKernel_deriv_abs_integral_translated {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    ∫ y : ℝ,
        |Real.exp (-t) * deriv (fun z : ℝ => heatKernel t (z - y)) x| =
      Real.exp (-t) * (2 / Real.sqrt (4 * Real.pi * t)) := by
  have hfun :
      (fun y : ℝ =>
        |Real.exp (-t) * deriv (fun z : ℝ => heatKernel t (z - y)) x|) =
        fun y : ℝ =>
          Real.exp (-t) *
            |deriv (fun z : ℝ => heatKernel t (z - y)) x| := by
    ext y
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun, MeasureTheory.integral_const_mul,
    heatKernel_deriv_abs_integral_translated ht x]

lemma heatKernel_translated_hasDerivAt_right {t : ℝ} (ht : 0 < t)
    (x y : ℝ) :
    HasDerivAt (fun z : ℝ => heatKernel t (x - z))
      (((x - y) / (2 * t)) * heatKernel t (x - y)) y := by
  have hinner : HasDerivAt (fun z : ℝ => x - z) (-1) y := by
    simpa using (hasDerivAt_const y x).sub (hasDerivAt_id y)
  have h := (heatKernel_hasDerivAt ht (x - y)).comp y hinner
  convert h using 1
  ring

lemma deriv_heatKernel_translated_right {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun z : ℝ => heatKernel t (x - z)) y =
      ((x - y) / (2 * t)) * heatKernel t (x - y) :=
  (heatKernel_translated_hasDerivAt_right ht x y).deriv

lemma heatKernel_deriv_abs_translated_integrable {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t (z - y)) x|) := by
  have hshift :
      MeasureTheory.Integrable
        (fun y : ℝ => |deriv (fun z : ℝ => heatKernel t z) (x - y)|) := by
    simpa [sub_eq_add_neg, add_comm] using
      ((heatKernel_deriv_abs_integrable ht).comp_neg.comp_add_right (-x))
  convert hshift using 1
  ext y
  rw [deriv_heatKernel_translated_left ht x y, deriv_heatKernel ht (x - y)]

lemma modifiedHeatKernel_deriv_abs_translated_integrable {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ =>
        |Real.exp (-t) * deriv (fun z : ℝ => heatKernel t (z - y)) x|) := by
  have hfun :
      (fun y : ℝ =>
        |Real.exp (-t) * deriv (fun z : ℝ => heatKernel t (z - y)) x|) =
        fun y : ℝ =>
          Real.exp (-t) *
            |deriv (fun z : ℝ => heatKernel t (z - y)) x| := by
    ext y
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun]
  exact (heatKernel_deriv_abs_translated_integrable ht x).const_mul
    (Real.exp (-t))

lemma heatKernel_deriv_translated_integrable {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x) := by
  have hshift :
      MeasureTheory.Integrable
        (fun y : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - y)) := by
    simpa [sub_eq_add_neg, add_comm] using
      ((heatKernel_deriv_integrable ht).comp_neg.comp_add_right (-x))
  convert hshift using 1
  ext y
  rw [deriv_heatKernel_translated_left ht x y, deriv_heatKernel ht (x - y)]

lemma modifiedHeatKernel_deriv_translated_integrable {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ =>
        Real.exp (-t) * deriv (fun z : ℝ => heatKernel t (z - y)) x) :=
  (heatKernel_deriv_translated_integrable ht x).const_mul (Real.exp (-t))

lemma heatKernel_deriv_mul_bounded_integrable {t M : ℝ}
    (ht : 0 < t) {f : ℝ → ℝ} (x : ℝ)
    (hf : ∀ y, |f y| ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.Integrable
      (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x * f y) :=
  (heatKernel_deriv_translated_integrable ht x).mul_bdd hf_meas
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hf y)

lemma modifiedHeatKernel_deriv_mul_bounded_integrable {t M : ℝ}
    (ht : 0 < t) {f : ℝ → ℝ} (x : ℝ)
    (hf : ∀ y, |f y| ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.Integrable
      (fun y : ℝ =>
        Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)) := by
  simpa using
    (heatKernel_deriv_mul_bounded_integrable ht x hf hf_meas).const_mul
      (Real.exp (-t))

theorem heatKernel_deriv_mul_bounded_integral_abs_le {t M : ℝ}
    (ht : 0 < t) (_hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    ∫ y : ℝ, |deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| ≤
      (2 / Real.sqrt (4 * Real.pi * t)) * M := by
  have hmajor_int :
      MeasureTheory.Integrable
        (fun y : ℝ =>
          |deriv (fun z : ℝ => heatKernel t (z - y)) x| * M) :=
    (heatKernel_deriv_abs_translated_integrable ht x).mul_const M
  calc
    ∫ y : ℝ, |deriv (fun z : ℝ => heatKernel t (z - y)) x * f y|
        ≤ ∫ y : ℝ,
            |deriv (fun z : ℝ => heatKernel t (z - y)) x| * M := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun y => abs_nonneg _
          · exact hmajor_int
          · exact Filter.Eventually.of_forall fun y => by
              simpa [abs_mul] using
                mul_le_mul_of_nonneg_left (hf y)
                  (abs_nonneg
                    (deriv (fun z : ℝ => heatKernel t (z - y)) x))
    _ = (2 / Real.sqrt (4 * Real.pi * t)) * M := by
          rw [MeasureTheory.integral_mul_const,
            heatKernel_deriv_abs_integral_translated ht x]

theorem heatKernel_deriv_convolution_bounded_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| ≤
      (2 / Real.sqrt (4 * Real.pi * t)) * M := by
  calc
    |∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y|
        ≤ ∫ y : ℝ,
            ‖deriv (fun z : ℝ => heatKernel t (z - y)) x * f y‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ = ∫ y : ℝ,
            |deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| := by
          simp [Real.norm_eq_abs]
    _ ≤ (2 / Real.sqrt (4 * Real.pi * t)) * M :=
          heatKernel_deriv_mul_bounded_integral_abs_le ht hM hf x

theorem heatKernel_deriv_convolution_diff_bounded_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f g : ℝ → ℝ}
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ) :
    |∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel t (z - y)) x * (f y - g y)| ≤
      (2 / Real.sqrt (4 * Real.pi * t)) * M :=
  heatKernel_deriv_convolution_bounded_abs_le
    (f := fun y => f y - g y) ht hM hfg x

theorem modifiedHeatKernel_deriv_mul_bounded_integral_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    ∫ y : ℝ,
        |Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)| ≤
      Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) := by
  have hfun :
      (fun y : ℝ =>
        |Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)|) =
        fun y : ℝ =>
          Real.exp (-t) *
            |deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| := by
    ext y
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  rw [hfun, MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (heatKernel_deriv_mul_bounded_integral_abs_le ht hM hf x)
    (Real.exp_nonneg _)

theorem modifiedHeatKernel_deriv_convolution_bounded_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |∫ y : ℝ,
        Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)| ≤
      Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) := by
  calc
    |∫ y : ℝ,
        Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)|
        ≤ ∫ y : ℝ,
            ‖Real.exp (-t) *
              (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ = ∫ y : ℝ,
            |Real.exp (-t) *
              (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)| := by
          simp [Real.norm_eq_abs]
    _ ≤ Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) :=
          modifiedHeatKernel_deriv_mul_bounded_integral_abs_le ht hM hf x

theorem modifiedHeatKernel_deriv_convolution_diff_bounded_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f g : ℝ → ℝ}
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ) :
    |∫ y : ℝ,
        Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * (f y - g y))| ≤
      Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) :=
  modifiedHeatKernel_deriv_convolution_bounded_abs_le
    (f := fun y => f y - g y) ht hM hfg x

/-- The derivative kernel times an `L¹` input is integrable. -/
lemma heatKernel_deriv_mul_integrable_of_integrable
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    MeasureTheory.Integrable
      (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x * f y) := by
  let C : ℝ :=
    ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
      (Real.sqrt (1 / (4 * t)))⁻¹
  have hderiv_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x)
        MeasureTheory.volume :=
    (heatKernel_deriv_translated_integrable ht x).aestronglyMeasurable
  have hderiv_bound :
      ∀ y : ℝ, ‖deriv (fun z : ℝ => heatKernel t (z - y)) x‖ ≤ C := by
    intro y
    simpa [Real.norm_eq_abs, C] using
      heatKernel_deriv_translated_pointwise_bound ht x y
  simpa [mul_comm] using
    hf_int.mul_bdd hderiv_meas
      (Filter.Eventually.of_forall hderiv_bound)

/-- The modified derivative kernel times an `L¹` input is integrable. -/
lemma modifiedHeatKernel_deriv_mul_integrable_of_integrable
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    MeasureTheory.Integrable
      (fun y : ℝ =>
        Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)) :=
  (heatKernel_deriv_mul_integrable_of_integrable ht x hf_int).const_mul
    (Real.exp (-t))

/-- `L¹ → L∞` smoothing for the heat-kernel derivative convolution. -/
theorem heatKernel_deriv_convolution_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| ≤
      (((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
        (Real.sqrt (1 / (4 * t)))⁻¹) * ∫ y : ℝ, |f y| := by
  let C : ℝ :=
    ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
      (Real.sqrt (1 / (4 * t)))⁻¹
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  calc
    |∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y|
        ≤ ∫ y : ℝ,
            ‖deriv (fun z : ℝ => heatKernel t (z - y)) x * f y‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ = ∫ y : ℝ,
            |deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| := by
          simp [Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ, C * |f y| := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun y => abs_nonneg _
          · exact (hf_int.norm).const_mul C
          · exact Filter.Eventually.of_forall fun y => by
              change
                |deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| ≤
                  C * |f y|
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right
                (heatKernel_deriv_translated_pointwise_bound ht x y)
                (abs_nonneg _)
    _ = C * ∫ y : ℝ, |f y| := by
          rw [MeasureTheory.integral_const_mul]

/-- `L¹ → L∞` smoothing for the modified heat-kernel derivative convolution. -/
theorem modifiedHeatKernel_deriv_convolution_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |∫ y : ℝ,
        Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)| ≤
      Real.exp (-t) *
        ((((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
          (Real.sqrt (1 / (4 * t)))⁻¹) * ∫ y : ℝ, |f y|) := by
  let C : ℝ :=
    ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
      (Real.sqrt (1 / (4 * t)))⁻¹
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  calc
    |∫ y : ℝ,
        Real.exp (-t) *
          (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)|
        ≤ ∫ y : ℝ,
            ‖Real.exp (-t) *
              (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ = ∫ y : ℝ,
            Real.exp (-t) *
              |deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| := by
          congr 1
          ext y
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ ∫ y : ℝ, Real.exp (-t) * (C * |f y|) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun y =>
              mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
          · exact ((hf_int.norm).const_mul C).const_mul (Real.exp (-t))
          · exact Filter.Eventually.of_forall fun y => by
              exact mul_le_mul_of_nonneg_left
                (by
                  rw [abs_mul]
                  exact mul_le_mul_of_nonneg_right
                    (heatKernel_deriv_translated_pointwise_bound ht x y)
                    (abs_nonneg _))
                (Real.exp_nonneg _)
    _ = Real.exp (-t) * (C * ∫ y : ℝ, |f y|) := by
          rw [show (fun y : ℝ => Real.exp (-t) * (C * |f y|)) =
              fun y : ℝ => (Real.exp (-t) * C) * |f y| by
              ext y
              ring]
          rw [MeasureTheory.integral_const_mul]
          ring

/-- The translated heat kernel is integrable. -/
lemma heatKernel_translated_integrable {t : ℝ} (ht : 0 < t) (x : ℝ) :
    MeasureTheory.Integrable (fun y => heatKernel t (x - y)) := by
  have h := heatKernel_integrable ht
  have key : (fun y : ℝ => heatKernel t (x - y)) =
      (fun y => (fun z => heatKernel t z) (-(y + (-x)))) := by
    ext y; congr 1; ring
  rw [key, show (fun y : ℝ => (fun z => heatKernel t z) (-(y + -x))) =
    (fun y => (fun z => heatKernel t (-z)) (y + (-x))) from rfl]
  simp_rw [heatKernel_neg]
  rw [show (fun y : ℝ => heatKernel t (y + -x)) =
    (fun y => (fun z => heatKernel t z) (y + (-x))) from rfl]
  exact h.comp_add_right (-x)

/-- The heat kernel (translated) times a bounded function is integrable. -/
lemma heatKernel_mul_bounded_integrable {t : ℝ} (ht : 0 < t) (x : ℝ)
    {f : ℝ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y) :=
  (heatKernel_translated_integrable ht x).mul_bdd hf_meas
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)

/-- The translated heat kernel times an `L¹` input is integrable. -/
lemma heatKernel_mul_integrable_of_integrable
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    MeasureTheory.Integrable (fun y : ℝ => heatKernel t (x - y) * f y) := by
  have hkernel_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => heatKernel t (x - y)) MeasureTheory.volume :=
    (heatKernel_translated_integrable ht x).aestronglyMeasurable
  have hkernel_bound :
      ∀ y : ℝ, ‖heatKernel t (x - y)‖ ≤ 1 / Real.sqrt (4 * Real.pi * t) := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht (x - y))]
    exact heatKernel_pointwise_bound ht (x - y)
  simpa [mul_comm] using
    hf_int.mul_bdd hkernel_meas
      (Filter.Eventually.of_forall hkernel_bound)

/-- Spatial derivative formula for the heat semigroup on `L¹` inputs. -/
theorem heatSemigroup_hasDerivAt
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    HasDerivAt (fun z : ℝ => heatSemigroup t f z)
      (∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y) x := by
  let F : ℝ → ℝ → ℝ := fun z y => heatKernel t (z - y) * f y
  let F' : ℝ → ℝ → ℝ :=
    fun z y => deriv (fun w : ℝ => heatKernel t (w - y)) z * f y
  let C : ℝ :=
    ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
      (Real.sqrt (1 / (4 * t)))⁻¹
  let bound : ℝ → ℝ := fun y => C * |f y|
  have hs : Set.univ ∈ 𝓝 x := by simp
  have hF_meas :
      ∀ᶠ z in 𝓝 x,
        MeasureTheory.AEStronglyMeasurable (F z) MeasureTheory.volume := by
    filter_upwards with z
    exact (heatKernel_mul_integrable_of_integrable ht z hf_int).aestronglyMeasurable
  have hF_int : MeasureTheory.Integrable (F x) MeasureTheory.volume := by
    exact heatKernel_mul_integrable_of_integrable ht x hf_int
  have hF'_meas :
      MeasureTheory.AEStronglyMeasurable (F' x) MeasureTheory.volume := by
    exact (heatKernel_deriv_mul_integrable_of_integrable ht x hf_int).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂MeasureTheory.volume,
      ∀ z ∈ (Set.univ : Set ℝ), ‖F' z y‖ ≤ bound y := by
    filter_upwards with y z _hz
    have hpoint := heatKernel_deriv_translated_pointwise_bound ht z y
    change ‖deriv (fun w : ℝ => heatKernel t (w - y)) z * f y‖ ≤ C * |f y|
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (by simpa [Real.norm_eq_abs, C] using hpoint)
      (abs_nonneg _)
  have hbound_int : MeasureTheory.Integrable bound MeasureTheory.volume := by
    dsimp [bound]
    exact (hf_int.norm).const_mul C
  have h_diff : ∀ᵐ y ∂MeasureTheory.volume,
      ∀ z ∈ (Set.univ : Set ℝ), HasDerivAt (fun z' : ℝ => F z' y) (F' z y) z := by
    filter_upwards with y z _hz
    dsimp [F, F']
    simpa [deriv_heatKernel_translated_left ht z y] using
      (heatKernel_translated_hasDerivAt_left ht z y).mul_const (f y)
  simpa [heatSemigroup, F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := MeasureTheory.volume) (bound := bound) (F := F) (F' := F')
      (x₀ := x) (s := Set.univ)
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-- Derivative formula for the heat semigroup on `L¹` inputs. -/
theorem deriv_heatSemigroup
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    deriv (fun z : ℝ => heatSemigroup t f z) x =
      ∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y :=
  (heatSemigroup_hasDerivAt ht x hf_int).deriv

/-- Spatial derivative formula for the modified heat semigroup on `L¹` inputs. -/
theorem modifiedSemigroup_hasDerivAt
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    HasDerivAt (fun z : ℝ => modifiedSemigroup t f z)
      (Real.exp (-t) *
        ∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y) x := by
  unfold modifiedSemigroup
  exact (heatSemigroup_hasDerivAt ht x hf_int).const_mul (Real.exp (-t))

/-- Derivative formula for the modified heat semigroup on `L¹` inputs. -/
theorem deriv_modifiedSemigroup
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    deriv (fun z : ℝ => modifiedSemigroup t f z) x =
      Real.exp (-t) *
        ∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y :=
  (modifiedSemigroup_hasDerivAt ht x hf_int).deriv

/-- Pointwise gradient bound for the heat semigroup with bounded input. -/
theorem deriv_heatSemigroup_bounded_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : ∀ y, |f y| ≤ M) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |deriv (fun z : ℝ => heatSemigroup t f z) x| ≤
      (2 / Real.sqrt (4 * Real.pi * t)) * M := by
  rw [deriv_heatSemigroup ht x hf_int]
  exact heatKernel_deriv_convolution_bounded_abs_le ht hM hf x

/-- Pointwise gradient bound for the modified heat semigroup with bounded input. -/
theorem deriv_modifiedSemigroup_bounded_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : ∀ y, |f y| ≤ M) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |deriv (fun z : ℝ => modifiedSemigroup t f z) x| ≤
      Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) := by
  rw [deriv_modifiedSemigroup ht x hf_int]
  rw [← MeasureTheory.integral_const_mul]
  exact modifiedHeatKernel_deriv_convolution_bounded_abs_le ht hM hf x

/-- `L¹ → L∞` gradient smoothing for the heat semigroup. -/
theorem deriv_heatSemigroup_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |deriv (fun z : ℝ => heatSemigroup t f z) x| ≤
      (((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
        (Real.sqrt (1 / (4 * t)))⁻¹) * ∫ y : ℝ, |f y| := by
  rw [deriv_heatSemigroup ht x hf_int]
  exact heatKernel_deriv_convolution_L1_Linfty_smoothing_abs ht x hf_int

/-- `L¹ → L∞` gradient smoothing for the modified heat semigroup. -/
theorem deriv_modifiedSemigroup_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |deriv (fun z : ℝ => modifiedSemigroup t f z) x| ≤
      Real.exp (-t) *
        ((((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
          (Real.sqrt (1 / (4 * t)))⁻¹) * ∫ y : ℝ, |f y|) := by
  rw [deriv_modifiedSemigroup ht x hf_int]
  rw [← MeasureTheory.integral_const_mul]
  exact modifiedHeatKernel_deriv_convolution_L1_Linfty_smoothing_abs ht x hf_int

/-- Difference gradient bound for the heat semigroup with bounded pointwise difference. -/
theorem deriv_heatSemigroup_diff_bounded_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f g : ℝ → ℝ}
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f)
    (hg_int : MeasureTheory.Integrable g) :
    |deriv (fun z : ℝ => heatSemigroup t f z) x -
        deriv (fun z : ℝ => heatSemigroup t g z) x| ≤
      (2 / Real.sqrt (4 * Real.pi * t)) * M := by
  rw [deriv_heatSemigroup ht x hf_int, deriv_heatSemigroup ht x hg_int]
  have hf_kernel :
      MeasureTheory.Integrable
        (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x * f y) :=
    heatKernel_deriv_mul_integrable_of_integrable ht x hf_int
  have hg_kernel :
      MeasureTheory.Integrable
        (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x * g y) :=
    heatKernel_deriv_mul_integrable_of_integrable ht x hg_int
  rw [← MeasureTheory.integral_sub hf_kernel hg_kernel]
  simpa [mul_sub] using
    heatKernel_deriv_convolution_diff_bounded_abs_le ht hM hfg x

/-- Difference gradient bound for the modified heat semigroup with bounded pointwise difference. -/
theorem deriv_modifiedSemigroup_diff_bounded_abs_le {t M : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) {f g : ℝ → ℝ}
    (hfg : ∀ y, |f y - g y| ≤ M) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f)
    (hg_int : MeasureTheory.Integrable g) :
    |deriv (fun z : ℝ => modifiedSemigroup t f z) x -
        deriv (fun z : ℝ => modifiedSemigroup t g z) x| ≤
      Real.exp (-t) * ((2 / Real.sqrt (4 * Real.pi * t)) * M) := by
  rw [deriv_modifiedSemigroup ht x hf_int,
    deriv_modifiedSemigroup ht x hg_int, ← mul_sub, abs_mul,
    abs_of_nonneg (Real.exp_nonneg _)]
  have hheat :=
    deriv_heatSemigroup_diff_bounded_abs_le ht hM hfg x hf_int hg_int
  rw [deriv_heatSemigroup ht x hf_int, deriv_heatSemigroup ht x hg_int] at hheat
  exact mul_le_mul_of_nonneg_left hheat (Real.exp_nonneg _)

/-- `L¹ → L∞` gradient-difference smoothing for the heat semigroup. -/
theorem deriv_heatSemigroup_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f)
    (hg_int : MeasureTheory.Integrable g) :
    |deriv (fun z : ℝ => heatSemigroup t f z) x -
        deriv (fun z : ℝ => heatSemigroup t g z) x| ≤
      (((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
        (Real.sqrt (1 / (4 * t)))⁻¹) *
        ∫ y : ℝ, |f y - g y| := by
  rw [deriv_heatSemigroup ht x hf_int, deriv_heatSemigroup ht x hg_int]
  have hf_kernel :
      MeasureTheory.Integrable
        (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x * f y) :=
    heatKernel_deriv_mul_integrable_of_integrable ht x hf_int
  have hg_kernel :
      MeasureTheory.Integrable
        (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x * g y) :=
    heatKernel_deriv_mul_integrable_of_integrable ht x hg_int
  have hdiff_int : MeasureTheory.Integrable (fun y : ℝ => f y - g y) :=
    hf_int.sub hg_int
  rw [← MeasureTheory.integral_sub hf_kernel hg_kernel]
  simpa [mul_sub] using
    heatKernel_deriv_convolution_L1_Linfty_smoothing_abs
      (f := fun y : ℝ => f y - g y) ht x hdiff_int

/-- `L¹ → L∞` gradient-difference smoothing for the modified heat semigroup. -/
theorem deriv_modifiedSemigroup_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f)
    (hg_int : MeasureTheory.Integrable g) :
    |deriv (fun z : ℝ => modifiedSemigroup t f z) x -
        deriv (fun z : ℝ => modifiedSemigroup t g z) x| ≤
      Real.exp (-t) *
        ((((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
          (Real.sqrt (1 / (4 * t)))⁻¹) *
          ∫ y : ℝ, |f y - g y|) := by
  rw [deriv_modifiedSemigroup ht x hf_int,
    deriv_modifiedSemigroup ht x hg_int, ← mul_sub, abs_mul,
    abs_of_nonneg (Real.exp_nonneg _)]
  have hheat :=
    deriv_heatSemigroup_diff_L1_Linfty_smoothing_abs ht x hf_int hg_int
  rw [deriv_heatSemigroup ht x hf_int, deriv_heatSemigroup ht x hg_int] at hheat
  exact mul_le_mul_of_nonneg_left hheat (Real.exp_nonneg _)

/-! ## Semigroup estimates (Lemma 2.1 of the paper) -/

/-- The comparison principle for the heat equation:
    If f ≤ g pointwise, then e^{tΔ} f ≤ e^{tΔ} g. -/
theorem heatSemigroup_mono {f g : ℝ → ℝ} (hfg : ∀ x, f x ≤ g x)
    {t : ℝ} (ht : 0 < t)
    (hf_int : MeasureTheory.Integrable (fun y => heatKernel t (x₀ - y) * f y))
    (hg_int : MeasureTheory.Integrable (fun y => heatKernel t (x₀ - y) * g y)) :
    heatSemigroup t f x₀ ≤ heatSemigroup t g x₀ := by
  unfold heatSemigroup
  exact MeasureTheory.integral_mono hf_int hg_int
    (fun y => mul_le_mul_of_nonneg_left (hfg y) (heatKernel_nonneg ht _))

theorem heatSemigroup_mono_bounded {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ x, f x ≤ g x)
    (hf_bound : ∀ x, |f x| ≤ Mf) (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, heatSemigroup t f x ≤ heatSemigroup t g x := by
  intro x
  exact heatSemigroup_mono hfg ht
    (heatKernel_mul_bounded_integrable ht x hf_bound hf_meas)
    (heatKernel_mul_bounded_integrable ht x hg_bound hg_meas)

theorem heatSemigroup_nonneg {f : ℝ → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 < t) :
    ∀ x, 0 ≤ heatSemigroup t f x := by
  intro x
  unfold heatSemigroup
  exact MeasureTheory.integral_nonneg
    (fun y => mul_nonneg (heatKernel_nonneg ht _) (hf_nn y))

theorem heatSemigroup_ge_const {m : ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ) :
    m ≤ heatSemigroup t (fun _ => m) x := by
  unfold heatSemigroup
  rw [show (fun y => heatKernel t (x - y) * m) =
      (fun y => m * heatKernel t (x - y)) from by ext y; ring]
  rw [MeasureTheory.integral_const_mul, heatKernel_integral_translated ht x, mul_one]

theorem heatSemigroup_lower_bound {f : ℝ → ℝ} {m Mf : ℝ}
    (hf_ge : ∀ x, m ≤ f x) (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, m ≤ heatSemigroup t f x := by
  intro x
  have hconst_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * m) :=
    (heatKernel_translated_integrable ht x).mul_const m
  have hf_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y) :=
    heatKernel_mul_bounded_integrable ht x hf_bound hf_meas
  exact le_trans (heatSemigroup_ge_const ht x)
    (heatSemigroup_mono (f := fun _ : ℝ => m) (g := f)
      hf_ge ht hconst_int hf_int)

/-- If f ≥ 0 and f ≤ M, then e^{tΔ} f ≤ M (conservation + positivity). -/
theorem heatSemigroup_upper_bound {f : ℝ → ℝ} {M : ℝ}
    (_hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ M)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, heatSemigroup t f x ≤ M := by
  intro x
  unfold heatSemigroup
  calc ∫ y, heatKernel t (x - y) * f y
      ≤ ∫ y, heatKernel t (x - y) * M := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun y =>
            mul_nonneg (heatKernel_nonneg ht _) (_hf_nn y))
        · exact (heatKernel_translated_integrable ht x).mul_const M
        · exact Filter.Eventually.of_forall (fun y =>
            mul_le_mul_of_nonneg_left (hf_le y) (heatKernel_nonneg ht _))
    _ = M * ∫ y, heatKernel t (x - y) := by
        rw [show (fun y => heatKernel t (x - y) * M) = (fun y => M * heatKernel t (x - y)) from by
          ext y; ring]
        exact MeasureTheory.integral_const_mul _ _
    _ = M * 1 := by rw [heatKernel_integral_translated ht x]
    _ = M := by ring

/-- Positivity of the heat kernel gives the pointwise lattice bound
`|e^{tΔ} f| ≤ e^{tΔ} |f|`. -/
theorem heatSemigroup_abs_le_semigroup_abs {f : ℝ → ℝ}
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |heatSemigroup t f x| ≤ heatSemigroup t (fun y => |f y|) x := by
  unfold heatSemigroup
  calc |∫ y, heatKernel t (x - y) * f y|
      ≤ ∫ y, ‖heatKernel t (x - y) * f y‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
    _ = ∫ y, heatKernel t (x - y) * |f y| := by
        congr 1
        ext y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg ht _)]

theorem modifiedSemigroup_abs_le_semigroup_abs {f : ℝ → ℝ}
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |modifiedSemigroup t f x| ≤ modifiedSemigroup t (fun y => |f y|) x := by
  unfold modifiedSemigroup
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (heatSemigroup_abs_le_semigroup_abs ht x) (Real.exp_nonneg _)

theorem heatSemigroup_abs_le_of_abs_le {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hfg : ∀ y, |f y| ≤ g y) (ht : 0 < t)
    (hf_abs_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * |f y|))
    (hg_int : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y)) :
    |heatSemigroup t f x| ≤ heatSemigroup t g x := by
  exact le_trans (heatSemigroup_abs_le_semigroup_abs ht x)
    (heatSemigroup_mono (f := fun y : ℝ => |f y|) (g := g)
      hfg ht hf_abs_int hg_int)

theorem modifiedSemigroup_abs_le_of_abs_le {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hfg : ∀ y, |f y| ≤ g y) (ht : 0 < t)
    (hf_abs_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * |f y|))
    (hg_int : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y)) :
    |modifiedSemigroup t f x| ≤ modifiedSemigroup t g x := by
  unfold modifiedSemigroup
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (heatSemigroup_abs_le_of_abs_le x hfg ht hf_abs_int hg_int)
    (Real.exp_nonneg _)

theorem heatSemigroup_abs_le_of_abs_le_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ y, |f y| ≤ g y)
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, |heatSemigroup t f x| ≤ heatSemigroup t g x := by
  intro x
  have hf_abs_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => |f y|) MeasureTheory.volume := by
    simpa [Real.norm_eq_abs] using hf_meas.norm
  have hf_abs_bound :
      ∀ y : ℝ, |(fun z : ℝ => |f z|) y| ≤ Mf := by
    intro y
    simpa [abs_abs] using hf_bound y
  exact heatSemigroup_abs_le_of_abs_le x hfg ht
    (heatKernel_mul_bounded_integrable ht x hf_abs_bound hf_abs_meas)
    (heatKernel_mul_bounded_integrable ht x hg_bound hg_meas)

theorem modifiedSemigroup_abs_le_of_abs_le_bounded
    {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ y, |f y| ≤ g y)
    (hf_bound : ∀ y, |f y| ≤ Mf) (hg_bound : ∀ y, |g y| ≤ Mg)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, |modifiedSemigroup t f x| ≤ modifiedSemigroup t g x := by
  intro x
  have hf_abs_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => |f y|) MeasureTheory.volume := by
    simpa [Real.norm_eq_abs] using hf_meas.norm
  have hf_abs_bound :
      ∀ y : ℝ, |(fun z : ℝ => |f z|) y| ≤ Mf := by
    intro y
    simpa [abs_abs] using hf_bound y
  exact modifiedSemigroup_abs_le_of_abs_le x hfg ht
    (heatKernel_mul_bounded_integrable ht x hf_abs_bound hf_abs_meas)
    (heatKernel_mul_bounded_integrable ht x hg_bound hg_meas)

/-- L^∞ bound: ‖e^{(Δ-I)t} f‖_∞ ≤ e^{-t} ‖f‖_∞. -/
theorem heatSemigroup_abs_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (_hM : 0 ≤ M)
    (_hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    ∀ x, |heatSemigroup t f x| ≤ M := by
  intro x; unfold heatSemigroup
  calc |∫ y, heatKernel t (x - y) * f y|
      ≤ ∫ y, ‖heatKernel t (x - y) * f y‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ = ∫ y, heatKernel t (x - y) * |f y| := by
        congr 1; ext y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg ht _)]
    _ ≤ ∫ y, heatKernel t (x - y) * M := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun y =>
            mul_nonneg (heatKernel_nonneg ht _) (abs_nonneg _))
        · exact (heatKernel_translated_integrable ht x).mul_const M
        · exact Filter.Eventually.of_forall (fun y =>
            mul_le_mul_of_nonneg_left (hf y) (heatKernel_nonneg ht _))
    _ = M := by
        rw [show (fun y => heatKernel t (x - y) * M) = (fun y => M * heatKernel t (x - y)) from by
          ext y; ring]
        rw [MeasureTheory.integral_const_mul, heatKernel_integral_translated ht x, mul_one]

theorem modifiedSemigroup_Linfty_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    ∀ x, |modifiedSemigroup t f x| ≤ Real.exp (-t) * M := by
  intro x; unfold modifiedSemigroup
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left (heatSemigroup_abs_bound hf ht hM hf_meas x) (Real.exp_nonneg _)

/-- Whole-line `L¹ → L∞` smoothing for the heat semigroup. -/
theorem heatSemigroup_L1_Linfty_smoothing
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    ‖heatSemigroup t f x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, ‖f y‖ := by
  unfold heatSemigroup
  calc ‖∫ y : ℝ, heatKernel t (x - y) * f y‖
      ≤ ∫ y : ℝ, ‖heatKernel t (x - y) * f y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, (1 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖ := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y => norm_nonneg _
        · exact (hf_int.norm).smul (1 / Real.sqrt (4 * Real.pi * t))
        · exact Filter.Eventually.of_forall fun y => by
            change ‖heatKernel t (x - y) * f y‖ ≤
              (1 / Real.sqrt (4 * Real.pi * t)) * ‖f y‖
            rw [norm_mul, Real.norm_eq_abs,
              abs_of_nonneg (heatKernel_nonneg ht (x - y))]
            exact mul_le_mul_of_nonneg_right
              (heatKernel_pointwise_bound ht (x - y))
              (norm_nonneg _)
    _ = (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y : ℝ, ‖f y‖ :=
        MeasureTheory.integral_const_mul _ _

/-- Absolute-value form of whole-line `L¹ → L∞` smoothing for the heat semigroup. -/
theorem heatSemigroup_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |heatSemigroup t f x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, |f y| := by
  simpa [Real.norm_eq_abs] using
    heatSemigroup_L1_Linfty_smoothing ht x hf_int

/-- Whole-line `L¹ → L∞` smoothing for the modified heat semigroup. -/
theorem modifiedSemigroup_L1_Linfty_smoothing
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    ‖modifiedSemigroup t f x‖ ≤
      Real.exp (-t) *
        ((1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, ‖f y‖) := by
  unfold modifiedSemigroup
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (heatSemigroup_L1_Linfty_smoothing ht x hf_int)
    (Real.exp_nonneg _)

/-- Absolute-value form of whole-line `L¹ → L∞` smoothing for the modified semigroup. -/
theorem modifiedSemigroup_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |modifiedSemigroup t f x| ≤
      Real.exp (-t) *
        ((1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, |f y|) := by
  simpa [Real.norm_eq_abs] using
    modifiedSemigroup_L1_Linfty_smoothing ht x hf_int

theorem heatSemigroup_const {c : ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSemigroup t (fun _ => c) x = c := by
  unfold heatSemigroup
  rw [show (fun y => heatKernel t (x - y) * c) =
      (fun y => c * heatKernel t (x - y)) from by ext y; ring]
  rw [MeasureTheory.integral_const_mul, heatKernel_integral_translated ht x, mul_one]

theorem heatSemigroup_zero_fun (t x : ℝ) :
    heatSemigroup t (fun _ => 0) x = 0 := by
  simp [heatSemigroup]

theorem modifiedSemigroup_zero_fun (t x : ℝ) :
    modifiedSemigroup t (fun _ => 0) x = 0 := by
  simp [modifiedSemigroup, heatSemigroup_zero_fun]

theorem modifiedSemigroup_const {c : ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ) :
    modifiedSemigroup t (fun _ => c) x = Real.exp (-t) * c := by
  simp [modifiedSemigroup, heatSemigroup_const ht x]

theorem heatSemigroup_upper_bound_of_bound {f : ℝ → ℝ} {M Mf : ℝ}
    (hf_le : ∀ x, f x ≤ M) (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, heatSemigroup t f x ≤ M := by
  intro x
  have hf_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y) :=
    heatKernel_mul_bounded_integrable ht x hf_bound hf_meas
  have hconst_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * M) :=
    (heatKernel_translated_integrable ht x).mul_const M
  have hmono :
      heatSemigroup t f x ≤ heatSemigroup t (fun _ : ℝ => M) x :=
    heatSemigroup_mono (f := f) (g := fun _ : ℝ => M)
      hf_le ht hf_int hconst_int
  simpa [heatSemigroup_const ht x] using hmono

theorem heatSemigroup_interval_bound {f : ℝ → ℝ} {m M Mf : ℝ}
    (hf_ge : ∀ x, m ≤ f x) (hf_le : ∀ x, f x ≤ M)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, m ≤ heatSemigroup t f x ∧ heatSemigroup t f x ≤ M := by
  intro x
  exact
    ⟨heatSemigroup_lower_bound hf_ge hf_bound hf_meas ht x,
      heatSemigroup_upper_bound_of_bound hf_le hf_bound hf_meas ht x⟩

theorem modifiedSemigroup_nonneg {f : ℝ → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 < t) :
    ∀ x, 0 ≤ modifiedSemigroup t f x := by
  intro x; unfold modifiedSemigroup
  exact mul_nonneg (Real.exp_nonneg _) (heatSemigroup_nonneg hf_nn ht x)

theorem modifiedSemigroup_mono_bounded {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hfg : ∀ x, f x ≤ g x)
    (hf_bound : ∀ x, |f x| ≤ Mf) (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, modifiedSemigroup t f x ≤ modifiedSemigroup t g x := by
  intro x
  unfold modifiedSemigroup
  exact mul_le_mul_of_nonneg_left
    (heatSemigroup_mono_bounded hfg hf_bound hg_bound hf_meas hg_meas ht x)
    (Real.exp_nonneg _)

theorem modifiedSemigroup_Linfty_decay {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (x : ℝ) :
    |modifiedSemigroup t f x| ≤ M * Real.exp (-t) :=
  (modifiedSemigroup_Linfty_bound hf ht hM hf_meas x).trans
    (by rw [mul_comm])

theorem modifiedSemigroup_lower_bound {f : ℝ → ℝ} {m Mf t : ℝ}
    (hf_ge : ∀ x, m ≤ f x) (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, Real.exp (-t) * m ≤ modifiedSemigroup t f x := by
  intro x
  unfold modifiedSemigroup
  exact mul_le_mul_of_nonneg_left
    (heatSemigroup_lower_bound hf_ge hf_bound hf_meas ht x)
    (Real.exp_nonneg _)

theorem modifiedSemigroup_upper_bound {f : ℝ → ℝ} {M Mf t : ℝ}
    (hf_le : ∀ x, f x ≤ M) (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, modifiedSemigroup t f x ≤ Real.exp (-t) * M := by
  intro x
  unfold modifiedSemigroup
  exact mul_le_mul_of_nonneg_left
    (heatSemigroup_upper_bound_of_bound hf_le hf_bound hf_meas ht x)
    (Real.exp_nonneg _)

theorem modifiedSemigroup_interval_bound {f : ℝ → ℝ} {m M Mf t : ℝ}
    (hf_ge : ∀ x, m ≤ f x) (hf_le : ∀ x, f x ≤ M)
    (hf_bound : ∀ x, |f x| ≤ Mf)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x,
      Real.exp (-t) * m ≤ modifiedSemigroup t f x ∧
        modifiedSemigroup t f x ≤ Real.exp (-t) * M := by
  intro x
  exact
    ⟨modifiedSemigroup_lower_bound hf_ge hf_bound hf_meas ht x,
      modifiedSemigroup_upper_bound hf_le hf_bound hf_meas ht x⟩

lemma heatKernel_zero (x : ℝ) : heatKernel 0 x = 0 := by
  unfold heatKernel
  simp [mul_zero, Real.sqrt_zero, div_zero]

lemma heatSemigroup_zero (f : ℝ → ℝ) (x : ℝ) : heatSemigroup 0 f x = 0 := by
  unfold heatSemigroup
  simp [heatKernel_zero, zero_mul]

theorem heatSemigroup_add {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y))
    (hg : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y)) :
    heatSemigroup t (fun y => f y + g y) x =
    heatSemigroup t f x + heatSemigroup t g x := by
  simpa [heatSemigroup, mul_add] using MeasureTheory.integral_add hf hg

theorem modifiedSemigroup_add {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y))
    (hg : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y)) :
    modifiedSemigroup t (fun y => f y + g y) x =
    modifiedSemigroup t f x + modifiedSemigroup t g x := by
  unfold modifiedSemigroup
  rw [heatSemigroup_add x hf hg]
  ring

theorem heatSemigroup_add_bounded {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ x, |f x| ≤ Mf) (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, heatSemigroup t (fun y => f y + g y) x =
      heatSemigroup t f x + heatSemigroup t g x := by
  intro x
  exact heatSemigroup_add x
    (heatKernel_mul_bounded_integrable ht x hf_bound hf_meas)
    (heatKernel_mul_bounded_integrable ht x hg_bound hg_meas)

theorem modifiedSemigroup_add_bounded {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ x, |f x| ≤ Mf) (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, modifiedSemigroup t (fun y => f y + g y) x =
      modifiedSemigroup t f x + modifiedSemigroup t g x := by
  intro x
  exact modifiedSemigroup_add x
    (heatKernel_mul_bounded_integrable ht x hf_bound hf_meas)
    (heatKernel_mul_bounded_integrable ht x hg_bound hg_meas)

theorem heatSemigroup_neg (f : ℝ → ℝ) (t x : ℝ) :
    heatSemigroup t (fun y => -f y) x = -heatSemigroup t f x := by
  simpa [heatSemigroup] using
    (MeasureTheory.integral_neg (fun y => heatKernel t (x - y) * f y))

theorem modifiedSemigroup_neg (f : ℝ → ℝ) (t x : ℝ) :
    modifiedSemigroup t (fun y => -f y) x = -modifiedSemigroup t f x := by
  unfold modifiedSemigroup
  rw [heatSemigroup_neg]
  ring

theorem heatSemigroup_const_mul (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) :
    heatSemigroup t (fun y => a * f y) x = a * heatSemigroup t f x := by
  unfold heatSemigroup
  rw [show (fun y => heatKernel t (x - y) * (a * f y)) =
      (fun y => a * (heatKernel t (x - y) * f y)) from by
        ext y
        ring]
  exact MeasureTheory.integral_const_mul _ _

theorem modifiedSemigroup_const_mul (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) :
    modifiedSemigroup t (fun y => a * f y) x =
    a * modifiedSemigroup t f x := by
  unfold modifiedSemigroup
  rw [heatSemigroup_const_mul]
  ring

theorem heatSemigroup_sub {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y))
    (hg : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y)) :
    heatSemigroup t (fun y => f y - g y) x =
    heatSemigroup t f x - heatSemigroup t g x := by
  simpa [heatSemigroup, mul_sub] using MeasureTheory.integral_sub hf hg

theorem modifiedSemigroup_sub {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y))
    (hg : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y)) :
    modifiedSemigroup t (fun y => f y - g y) x =
    modifiedSemigroup t f x - modifiedSemigroup t g x := by
  unfold modifiedSemigroup
  rw [heatSemigroup_sub x hf hg]
  ring

/-- Whole-line `L¹ → L∞` smoothing for heat-semigroup differences. -/
theorem heatSemigroup_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f)
    (hg_int : MeasureTheory.Integrable g) :
    |heatSemigroup t f x - heatSemigroup t g x| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, |f y - g y| := by
  have hf_kernel :
      MeasureTheory.Integrable (fun y : ℝ => heatKernel t (x - y) * f y) :=
    heatKernel_mul_integrable_of_integrable ht x hf_int
  have hg_kernel :
      MeasureTheory.Integrable (fun y : ℝ => heatKernel t (x - y) * g y) :=
    heatKernel_mul_integrable_of_integrable ht x hg_int
  have hdiff_int : MeasureTheory.Integrable (fun y : ℝ => f y - g y) :=
    hf_int.sub hg_int
  have h :=
    heatSemigroup_L1_Linfty_smoothing_abs
      (f := fun y : ℝ => f y - g y) ht x hdiff_int
  rwa [heatSemigroup_sub x hf_kernel hg_kernel] at h

/-- Whole-line `L¹ → L∞` smoothing for modified-semigroup differences. -/
theorem modifiedSemigroup_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f)
    (hg_int : MeasureTheory.Integrable g) :
    |modifiedSemigroup t f x - modifiedSemigroup t g x| ≤
      Real.exp (-t) *
        ((1 / Real.sqrt (4 * Real.pi * t)) * ∫ y, |f y - g y|) := by
  have hf_kernel :
      MeasureTheory.Integrable (fun y : ℝ => heatKernel t (x - y) * f y) :=
    heatKernel_mul_integrable_of_integrable ht x hf_int
  have hg_kernel :
      MeasureTheory.Integrable (fun y : ℝ => heatKernel t (x - y) * g y) :=
    heatKernel_mul_integrable_of_integrable ht x hg_int
  have hdiff_int : MeasureTheory.Integrable (fun y : ℝ => f y - g y) :=
    hf_int.sub hg_int
  have h :=
    modifiedSemigroup_L1_Linfty_smoothing_abs
      (f := fun y : ℝ => f y - g y) ht x hdiff_int
  rwa [modifiedSemigroup_sub x hf_kernel hg_kernel] at h

theorem heatSemigroup_sub_bounded {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ x, |f x| ≤ Mf) (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, heatSemigroup t (fun y => f y - g y) x =
      heatSemigroup t f x - heatSemigroup t g x := by
  intro x
  exact heatSemigroup_sub x
    (heatKernel_mul_bounded_integrable ht x hf_bound hf_meas)
    (heatKernel_mul_bounded_integrable ht x hg_bound hg_meas)

theorem modifiedSemigroup_sub_bounded {f g : ℝ → ℝ} {Mf Mg t : ℝ}
    (hf_bound : ∀ x, |f x| ≤ Mf) (hg_bound : ∀ x, |g x| ≤ Mg)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    (ht : 0 < t) :
    ∀ x, modifiedSemigroup t (fun y => f y - g y) x =
      modifiedSemigroup t f x - modifiedSemigroup t g x := by
  intro x
  exact modifiedSemigroup_sub x
    (heatKernel_mul_bounded_integrable ht x hf_bound hf_meas)
    (heatKernel_mul_bounded_integrable ht x hg_bound hg_meas)

theorem heatSemigroup_contraction {f g : ℝ → ℝ} {M t : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ M) (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    {Mf Mg : ℝ} (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg) :
    ∀ x, |heatSemigroup t f x - heatSemigroup t g x| ≤ M := by
  intro x
  have hf_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y) :=
    heatKernel_mul_bounded_integrable ht x hf_bound hf_meas
  have hg_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y) :=
    heatKernel_mul_bounded_integrable ht x hg_bound hg_meas
  have hsub_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => f y - g y) MeasureTheory.volume :=
    hf_meas.sub hg_meas
  have hbound :=
    heatSemigroup_abs_bound
      (f := fun y : ℝ => f y - g y) (M := M) hfg ht hM hsub_meas x
  rwa [heatSemigroup_sub x hf_int hg_int] at hbound

theorem modifiedSemigroup_contraction {f g : ℝ → ℝ} {M t : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ M) (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume)
    {Mf Mg : ℝ} (hf_bound : ∀ x, |f x| ≤ Mf)
    (hg_bound : ∀ x, |g x| ≤ Mg) :
    ∀ x, |modifiedSemigroup t f x - modifiedSemigroup t g x| ≤
      Real.exp (-t) * M := by
  intro x
  have hf_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y) :=
    heatKernel_mul_bounded_integrable ht x hf_bound hf_meas
  have hg_int :
      MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y) :=
    heatKernel_mul_bounded_integrable ht x hg_bound hg_meas
  have hsub_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => f y - g y) MeasureTheory.volume :=
    hf_meas.sub hg_meas
  have hbound :=
    modifiedSemigroup_Linfty_bound
      (f := fun y : ℝ => f y - g y) (M := M) hfg ht hM hsub_meas x
  rwa [modifiedSemigroup_sub x hf_int hg_int] at hbound

/-! ## Cosine-basis interval smoothing constants -/

/-- Neumann cosine eigenvalues on the unit interval, `λ_n = (nπ)^2`. -/
def unitIntervalCosineEigenvalue (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.pi) ^ 2

/-- Spectral multiplier for the squared `L²` norm of the gradient after heat flow. -/
def unitIntervalCosineHeatGradientMultiplier (t : ℝ) (n : ℕ) : ℝ :=
  unitIntervalCosineEigenvalue n *
    Real.exp (-2 * t * unitIntervalCosineEigenvalue n)

/-- The explicit interval cosine heat-gradient `L²` smoothing constant. -/
def unitIntervalCosineHeatGradientL2Constant (t : ℝ) : ℝ :=
  Real.sqrt (1 / (2 * t))

/-- Elementary exponential bound used for the spectral heat multiplier. -/
lemma real_mul_exp_neg_le_one {x : ℝ} (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 1 := by
  have hx_le_exp : x ≤ Real.exp x := by
    calc
      x ≤ x + 1 := by linarith
      _ ≤ Real.exp x := Real.add_one_le_exp x
  calc
    x * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) := by
      exact mul_le_mul_of_nonneg_right hx_le_exp (Real.exp_nonneg _)
    _ = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- Pointwise spectral multiplier bound for the interval cosine heat flow. -/
lemma unitIntervalCosineHeatGradientMultiplier_le {t : ℝ} (ht : 0 < t) (n : ℕ) :
    unitIntervalCosineHeatGradientMultiplier t n ≤ 1 / (2 * t) := by
  let lambda := unitIntervalCosineEigenvalue n
  have hlambda : 0 ≤ lambda := by
    dsimp [lambda, unitIntervalCosineEigenvalue]
    positivity
  have ht2 : 0 < 2 * t := by positivity
  have hx : 0 ≤ 2 * t * lambda := by positivity
  have hbasic :
      (2 * t * lambda) * Real.exp (-(2 * t * lambda)) ≤ 1 :=
    real_mul_exp_neg_le_one hx
  have hscaled :
      (1 / (2 * t)) * ((2 * t * lambda) * Real.exp (-(2 * t * lambda))) ≤
        (1 / (2 * t)) * 1 := by
    exact mul_le_mul_of_nonneg_left hbasic (by positivity)
  calc
    unitIntervalCosineHeatGradientMultiplier t n
        = (1 / (2 * t)) *
            ((2 * t * lambda) * Real.exp (-(2 * t * lambda))) := by
          dsimp [unitIntervalCosineHeatGradientMultiplier, lambda]
          field_simp [ne_of_gt ht2]
    _ ≤ (1 / (2 * t)) * 1 := hscaled
    _ = 1 / (2 * t) := by ring

/-- Finite cosine-coefficient `L²` energy on the unit interval. -/
def unitIntervalCosineL2Energy (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ s, (a n) ^ 2

/-- Finite cosine-coefficient gradient energy after heat flow on the unit interval. -/
def unitIntervalCosineHeatGradientEnergy
    (t : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ s, unitIntervalCosineHeatGradientMultiplier t n * (a n) ^ 2

/-- Finite-expansion `L²` gradient smoothing for the interval cosine heat flow. -/
lemma unitIntervalCosineHeatGradientEnergy_le {t : ℝ} (ht : 0 < t)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    unitIntervalCosineHeatGradientEnergy t s a ≤
      (1 / (2 * t)) * unitIntervalCosineL2Energy s a := by
  unfold unitIntervalCosineHeatGradientEnergy unitIntervalCosineL2Energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _hn
  exact mul_le_mul_of_nonneg_right
    (unitIntervalCosineHeatGradientMultiplier_le ht n) (sq_nonneg (a n))

/-- Finite cosine-coefficient `L²` norm on the unit interval. -/
def unitIntervalCosineL2Norm (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  Real.sqrt (unitIntervalCosineL2Energy s a)

/-- Finite cosine-coefficient gradient `L²` norm after heat flow. -/
def unitIntervalCosineHeatGradientL2Norm
    (t : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  Real.sqrt (unitIntervalCosineHeatGradientEnergy t s a)

/-- Finite-expansion `L²` heat-gradient smoothing with explicit constant `sqrt(1/(2t))`. -/
lemma unitIntervalCosineHeatGradientL2Norm_le {t : ℝ} (ht : 0 < t)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    unitIntervalCosineHeatGradientL2Norm t s a ≤
      unitIntervalCosineHeatGradientL2Constant t *
        unitIntervalCosineL2Norm s a := by
  have henergy := unitIntervalCosineHeatGradientEnergy_le ht s a
  have hconst : 0 ≤ 1 / (2 * t) := by positivity
  calc
    unitIntervalCosineHeatGradientL2Norm t s a
        = Real.sqrt (unitIntervalCosineHeatGradientEnergy t s a) := rfl
    _ ≤ Real.sqrt ((1 / (2 * t)) * unitIntervalCosineL2Energy s a) :=
        Real.sqrt_le_sqrt henergy
    _ = Real.sqrt (1 / (2 * t)) *
          Real.sqrt (unitIntervalCosineL2Energy s a) := by
        rw [Real.sqrt_mul hconst]
    _ = unitIntervalCosineHeatGradientL2Constant t *
          unitIntervalCosineL2Norm s a := rfl

/-- Infinite cosine-coefficient `L²` energy on the unit interval. -/
def unitIntervalCosineL2TsumEnergy (a : ℕ → ℝ) : ℝ :=
  ∑' n, (a n) ^ 2

/-- Infinite cosine-coefficient gradient energy after heat flow on the unit interval. -/
def unitIntervalCosineHeatGradientTsumEnergy (t : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑' n, unitIntervalCosineHeatGradientMultiplier t n * (a n) ^ 2

/-- `tsum` cosine-coefficient `L²` gradient smoothing on the unit interval. -/
lemma unitIntervalCosineHeatGradientTsumEnergy_le {t : ℝ} (ht : 0 < t)
    {a : ℕ → ℝ} (ha : Summable fun n => (a n) ^ 2) :
    unitIntervalCosineHeatGradientTsumEnergy t a ≤
      (1 / (2 * t)) * unitIntervalCosineL2TsumEnergy a := by
  have hnonneg :
      ∀ n, 0 ≤ unitIntervalCosineHeatGradientMultiplier t n * (a n) ^ 2 := by
    intro n
    exact mul_nonneg (by
      dsimp [unitIntervalCosineHeatGradientMultiplier,
        unitIntervalCosineEigenvalue]
      positivity) (sq_nonneg (a n))
  have hdom :
      ∀ n, unitIntervalCosineHeatGradientMultiplier t n * (a n) ^ 2 ≤
        (1 / (2 * t)) * (a n) ^ 2 := by
    intro n
    exact mul_le_mul_of_nonneg_right
      (unitIntervalCosineHeatGradientMultiplier_le ht n) (sq_nonneg (a n))
  have hweighted :
      Summable fun n => unitIntervalCosineHeatGradientMultiplier t n * (a n) ^ 2 :=
    Summable.of_nonneg_of_le hnonneg hdom (ha.mul_left (1 / (2 * t)))
  calc
    unitIntervalCosineHeatGradientTsumEnergy t a
        = ∑' n, unitIntervalCosineHeatGradientMultiplier t n * (a n) ^ 2 := rfl
    _ ≤ ∑' n, (1 / (2 * t)) * (a n) ^ 2 :=
        hweighted.tsum_le_tsum hdom (ha.mul_left (1 / (2 * t)))
    _ = (1 / (2 * t)) * ∑' n, (a n) ^ 2 :=
        Summable.tsum_mul_left (1 / (2 * t)) ha
    _ = (1 / (2 * t)) * unitIntervalCosineL2TsumEnergy a := rfl

/-- Infinite cosine-coefficient `L²` norm on the unit interval. -/
def unitIntervalCosineL2TsumNorm (a : ℕ → ℝ) : ℝ :=
  Real.sqrt (unitIntervalCosineL2TsumEnergy a)

/-- Infinite cosine-coefficient gradient `L²` norm after heat flow. -/
def unitIntervalCosineHeatGradientTsumL2Norm (t : ℝ) (a : ℕ → ℝ) : ℝ :=
  Real.sqrt (unitIntervalCosineHeatGradientTsumEnergy t a)

/-- `tsum` cosine-coefficient `L²` heat-gradient smoothing with explicit constant. -/
lemma unitIntervalCosineHeatGradientTsumL2Norm_le {t : ℝ} (ht : 0 < t)
    {a : ℕ → ℝ} (ha : Summable fun n => (a n) ^ 2) :
    unitIntervalCosineHeatGradientTsumL2Norm t a ≤
      unitIntervalCosineHeatGradientL2Constant t *
        unitIntervalCosineL2TsumNorm a := by
  have henergy := unitIntervalCosineHeatGradientTsumEnergy_le ht ha
  have hconst : 0 ≤ 1 / (2 * t) := by positivity
  calc
    unitIntervalCosineHeatGradientTsumL2Norm t a
        = Real.sqrt (unitIntervalCosineHeatGradientTsumEnergy t a) := rfl
    _ ≤ Real.sqrt ((1 / (2 * t)) * unitIntervalCosineL2TsumEnergy a) :=
        Real.sqrt_le_sqrt henergy
    _ = Real.sqrt (1 / (2 * t)) *
          Real.sqrt (unitIntervalCosineL2TsumEnergy a) := by
        rw [Real.sqrt_mul hconst]
    _ = unitIntervalCosineHeatGradientL2Constant t *
          unitIntervalCosineL2TsumNorm a := rfl

/-- `tsum` interval cosine heat-gradient smoothing in the standard `1 / sqrt(t)` form. -/
lemma unitIntervalCosineHeatGradientTsumL2Norm_le_inv_sqrt {t : ℝ} (ht : 0 < t)
    {a : ℕ → ℝ} (ha : Summable fun n => (a n) ^ 2) :
    unitIntervalCosineHeatGradientTsumL2Norm t a ≤
      (1 / Real.sqrt t) * unitIntervalCosineL2TsumNorm a := by
  have hbase := unitIntervalCosineHeatGradientTsumL2Norm_le ht ha
  have hden : t ≤ 2 * t := by nlinarith [ht]
  have hfrac : 1 / (2 * t) ≤ 1 / t := by
    simpa using one_div_le_one_div_of_le ht hden
  have hconst :
      unitIntervalCosineHeatGradientL2Constant t ≤ 1 / Real.sqrt t := by
    calc
      unitIntervalCosineHeatGradientL2Constant t = Real.sqrt (1 / (2 * t)) := rfl
      _ ≤ Real.sqrt (1 / t) := Real.sqrt_le_sqrt hfrac
      _ = 1 / Real.sqrt t := by
        rw [Real.sqrt_div (zero_le_one : (0 : ℝ) ≤ 1), Real.sqrt_one]
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _))

/-- Neumann cosine mode on the unit interval. -/
def unitIntervalCosineMode (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos ((n : ℝ) * Real.pi * x)

/-- Pointwise coefficient multiplying the `n`-th cosine coefficient after heat flow. -/
def unitIntervalCosineHeatPointWeight (t x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * unitIntervalCosineEigenvalue n) *
    unitIntervalCosineMode n x

/-- Cosine-coefficient model for the interval heat semigroup value at `x`. -/
def unitIntervalCosineHeatValue (t : ℝ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, unitIntervalCosineHeatPointWeight t x n * a n

/-- Pointwise heat trace controlling evaluation at `x`. -/
def unitIntervalCosineHeatPointEnergy (t x : ℝ) : ℝ :=
  ∑' n, (unitIntervalCosineHeatPointWeight t x n) ^ 2

/-- The cosine heat trace without the pointwise cosine factor. -/
def unitIntervalCosineHeatTrace (t : ℝ) : ℝ :=
  ∑' n, Real.exp (-2 * t * unitIntervalCosineEigenvalue n)

/-- The squared point-evaluation weight is bounded by the heat-trace summand. -/
lemma unitIntervalCosineHeatPointWeight_sq_le_traceTerm (t x : ℝ) (n : ℕ) :
    (unitIntervalCosineHeatPointWeight t x n) ^ 2 ≤
      Real.exp (-2 * t * unitIntervalCosineEigenvalue n) := by
  have hcos : (unitIntervalCosineMode n x) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    exact abs_cos_le_one _
  have hexp_sq_nonneg :
      0 ≤ (Real.exp (-t * unitIntervalCosineEigenvalue n)) ^ 2 :=
    sq_nonneg _
  calc
    (unitIntervalCosineHeatPointWeight t x n) ^ 2
        = (Real.exp (-t * unitIntervalCosineEigenvalue n)) ^ 2 *
            (unitIntervalCosineMode n x) ^ 2 := by
          dsimp [unitIntervalCosineHeatPointWeight]
          ring
    _ ≤ (Real.exp (-t * unitIntervalCosineEigenvalue n)) ^ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left hcos hexp_sq_nonneg
    _ = Real.exp (-2 * t * unitIntervalCosineEigenvalue n) := by
          rw [mul_one, sq, ← Real.exp_add]
          congr 1
          ring

/-- Pointwise evaluation energy is bounded by the cosine heat trace. -/
lemma unitIntervalCosineHeatPointEnergy_le_trace {t x : ℝ}
    (htrace : Summable fun n =>
      Real.exp (-2 * t * unitIntervalCosineEigenvalue n)) :
    unitIntervalCosineHeatPointEnergy t x ≤ unitIntervalCosineHeatTrace t := by
  have hpoint :
      Summable fun n => (unitIntervalCosineHeatPointWeight t x n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => unitIntervalCosineHeatPointWeight_sq_le_traceTerm t x n) htrace
  calc
    unitIntervalCosineHeatPointEnergy t x
        = ∑' n, (unitIntervalCosineHeatPointWeight t x n) ^ 2 := rfl
    _ ≤ ∑' n, Real.exp (-2 * t * unitIntervalCosineEigenvalue n) :=
        hpoint.tsum_le_tsum
          (fun n => unitIntervalCosineHeatPointWeight_sq_le_traceTerm t x n) htrace
    _ = unitIntervalCosineHeatTrace t := rfl

/-- Cauchy-Schwarz for real `tsum`s, in square-root `L²` form. -/
lemma real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq
    {u v : ℕ → ℝ} (hu : Summable fun n => (u n) ^ 2)
    (hv : Summable fun n => (v n) ^ 2) :
    |∑' n, u n * v n| ≤
      Real.sqrt (∑' n, (u n) ^ 2) *
        Real.sqrt (∑' n, (v n) ^ 2) := by
  have hprod :
      Summable fun n => |u n * v n| := by
    have hdom :
        ∀ n, |u n * v n| ≤
          (1 / 2) * (u n) ^ 2 + (1 / 2) * (v n) ^ 2 := by
      intro n
      rw [abs_mul]
      have hsq := sq_nonneg (|u n| - |v n|)
      nlinarith [sq_abs (u n), sq_abs (v n), hsq]
    exact Summable.of_nonneg_of_le (fun n => abs_nonneg _)
      hdom ((hu.mul_left (1 / 2)).add (hv.mul_left (1 / 2)))
  have hprod_norm :
      Summable fun n => ‖u n * v n‖ := by
    simpa [Real.norm_eq_abs] using hprod
  have habs_tsum :
      (∑' n, |u n * v n|) ≤
        Real.sqrt (∑' n, (u n) ^ 2) *
          Real.sqrt (∑' n, (v n) ^ 2) := by
    apply Real.tsum_le_of_sum_le (fun n => abs_nonneg _)
    intro s
    have hu_sum :
        ∑ n ∈ s, (u n) ^ 2 ≤ ∑' n, (u n) ^ 2 :=
      hu.sum_le_tsum s (fun n _hn => sq_nonneg (u n))
    have hv_sum :
        ∑ n ∈ s, (v n) ^ 2 ≤ ∑' n, (v n) ^ 2 :=
      hv.sum_le_tsum s (fun n _hn => sq_nonneg (v n))
    calc
      ∑ n ∈ s, |u n * v n|
          = ∑ n ∈ s, |u n| * |v n| := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [abs_mul]
      _ ≤ Real.sqrt (∑ n ∈ s, |u n| ^ 2) *
            Real.sqrt (∑ n ∈ s, |v n| ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt s (fun n => |u n|) (fun n => |v n|)
      _ = Real.sqrt (∑ n ∈ s, (u n) ^ 2) *
            Real.sqrt (∑ n ∈ s, (v n) ^ 2) := by
          simp [sq_abs]
      _ ≤ Real.sqrt (∑' n, (u n) ^ 2) *
            Real.sqrt (∑' n, (v n) ^ 2) := by
          exact mul_le_mul (Real.sqrt_le_sqrt hu_sum)
            (Real.sqrt_le_sqrt hv_sum) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
  calc
    |∑' n, u n * v n| = ‖∑' n, u n * v n‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑' n, ‖u n * v n‖ := norm_tsum_le_tsum_norm hprod_norm
    _ = ∑' n, |u n * v n| := by simp [Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑' n, (u n) ^ 2) *
          Real.sqrt (∑' n, (v n) ^ 2) := habs_tsum

/-- Pointwise cosine heat value controlled by point-evaluation energy and coefficient `L²`. -/
lemma unitIntervalCosineHeatValue_abs_le_pointEnergy {t x : ℝ} {a : ℕ → ℝ}
    (hpoint : Summable fun n => (unitIntervalCosineHeatPointWeight t x n) ^ 2)
    (ha : Summable fun n => (a n) ^ 2) :
    |unitIntervalCosineHeatValue t a x| ≤
      Real.sqrt (unitIntervalCosineHeatPointEnergy t x) *
        unitIntervalCosineL2TsumNorm a := by
  simpa [unitIntervalCosineHeatValue, unitIntervalCosineHeatPointEnergy,
    unitIntervalCosineL2TsumNorm]
    using
      real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq
        (u := fun n => unitIntervalCosineHeatPointWeight t x n)
        (v := a) hpoint ha

/-- Pointwise interval heat value controlled by the cosine heat trace and coefficient `L²`. -/
lemma unitIntervalCosineHeatValue_abs_le_trace {t x : ℝ} {a : ℕ → ℝ}
    (htrace : Summable fun n =>
      Real.exp (-2 * t * unitIntervalCosineEigenvalue n))
    (ha : Summable fun n => (a n) ^ 2) :
    |unitIntervalCosineHeatValue t a x| ≤
      Real.sqrt (unitIntervalCosineHeatTrace t) *
        unitIntervalCosineL2TsumNorm a := by
  have hpoint :
      Summable fun n => (unitIntervalCosineHeatPointWeight t x n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => unitIntervalCosineHeatPointWeight_sq_le_traceTerm t x n) htrace
  have hbase :=
    unitIntervalCosineHeatValue_abs_le_pointEnergy (t := t) (x := x)
      (a := a) hpoint ha
  have henergy := unitIntervalCosineHeatPointEnergy_le_trace (t := t) (x := x) htrace
  exact hbase.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt henergy) (Real.sqrt_nonneg _))

/-- Nonzero heat-trace summands are controlled by reciprocal eigenvalues. -/
lemma unitIntervalCosineHeatTraceTerm_le_recipEigen {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-2 * t * unitIntervalCosineEigenvalue n) ≤
      (1 / (2 * t)) * (1 / unitIntervalCosineEigenvalue n) := by
  let lambda := unitIntervalCosineEigenvalue n
  have hnpos_real : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda, unitIntervalCosineEigenvalue]
    exact sq_pos_of_pos (mul_pos hnpos_real Real.pi_pos)
  have hmult :
      lambda * Real.exp (-2 * t * lambda) ≤ 1 / (2 * t) := by
    simpa [unitIntervalCosineHeatGradientMultiplier, lambda]
      using unitIntervalCosineHeatGradientMultiplier_le ht n
  calc
    Real.exp (-2 * t * unitIntervalCosineEigenvalue n)
        = (1 / lambda) * (lambda * Real.exp (-2 * t * lambda)) := by
          change Real.exp (-2 * t * lambda) =
            (1 / lambda) * (lambda * Real.exp (-2 * t * lambda))
          field_simp [ne_of_gt hlambda_pos]
    _ ≤ (1 / lambda) * (1 / (2 * t)) := by
          exact mul_le_mul_of_nonneg_left hmult (by positivity)
    _ = (1 / (2 * t)) * (1 / unitIntervalCosineEigenvalue n) := by
          dsimp [lambda]
          ring

/-- The heat semigroup is symmetric in the sense that swapping x and y
    in the kernel gives the same integrand. -/
theorem heatSemigroup_kernel_symm (t x y : ℝ) :
    heatKernel t (x - y) = heatKernel t (y - x) :=
  heatKernel_sub_comm t x y

/-- The heat kernel at translated argument satisfies the exponential
    decay estimate: G(t, x) ≤ (1/√(4πt)) · exp(-x²/(4t)).
    This is the definition itself, but stated as a bound. -/
theorem heatKernel_exponential_decay {t : ℝ} (_ht : 0 < t) (x : ℝ) :
    heatKernel t x ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        Real.exp (-(x ^ 2) / (4 * t)) := le_refl _

/-- The heat kernel at distance R from origin decays as exp(-R²/(4t))/√(4πt). -/
theorem heatKernel_at_distance {t R : ℝ} (_ht : 0 < t) (_hR : 0 ≤ R) :
    heatKernel t R ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        Real.exp (-(R ^ 2) / (4 * t)) := le_refl _

/-- The heat kernel decays monotonically away from the origin:
    for |x| ≥ R ≥ 0, G(t,x) ≤ G(t,R). -/
theorem heatKernel_mono_away {t x R : ℝ} (ht : 0 < t)
    (hR : 0 ≤ R) (hxR : R ≤ |x|) :
    heatKernel t x ≤ heatKernel t R := by
  unfold heatKernel
  apply mul_le_mul_of_nonneg_left _ (div_nonneg one_pos.le (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  have hsq : R ^ 2 ≤ x ^ 2 :=
    calc R ^ 2 ≤ |x| ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg x]) hxR
      _ = x ^ 2 := sq_abs x
  exact div_le_div_of_nonneg_right (neg_le_neg hsq)
    (show (0 : ℝ) ≤ 4 * t by nlinarith [ht])

end
