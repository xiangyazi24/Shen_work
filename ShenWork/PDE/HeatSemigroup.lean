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
    (hf : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
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

end
