import ShenWork.PDE.HeatKernelLpEstimates
import ShenWork.PDE.IntervalFullKernelGradientLinfty

/-!
# Whole-line `L^p` smoothing for the heat-kernel derivative

The large-sensitivity critical bootstrap in Paper 1 uses the whole-line
estimate

`‖∂ₓ e^{tΔ} f‖∞ ≤ C(t,r) ‖f‖ₚ`,  `1 / r + 1 / p = 1`.

The repository already contains the corresponding value estimate for every
finite exponent and the endpoint derivative estimates.  This file supplies
the missing finite-exponent derivative bridge.  We interpolate the exact
`L¹` mass of the derivative kernel with its pointwise bound; no interval
Neumann estimate is used.
-/

open Filter MeasureTheory Real
open scoped ENNReal

noncomputable section

namespace ShenWork.Paper1

/-- The existing pointwise bound for the derivative of the Gaussian kernel. -/
def wholeLineHeatKernelDerivLinfBound (t : ℝ) : ℝ :=
  ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
    (Real.sqrt (1 / (4 * t)))⁻¹

/-- The interpolation bound for the finite `L^r` norm of the derivative
kernel. -/
def wholeLineHeatKernelDerivLpBound (t r : ℝ) : ℝ :=
  ((wholeLineHeatKernelDerivLinfBound t) ^ (r - 1) *
      (2 / Real.sqrt (4 * Real.pi * t))) ^ (1 / r)

theorem wholeLineHeatKernelDerivLinfBound_nonneg
    {t : ℝ} (ht : 0 < t) :
    0 ≤ wholeLineHeatKernelDerivLinfBound t := by
  unfold wholeLineHeatKernelDerivLinfBound
  positivity

/-- An integrable, uniformly bounded scalar function belongs to every finite
`L^r`, `1 ≤ r`.  This is the elementary `L¹ ∩ L∞ → L^r` interpolation step
used for the Gaussian derivative. -/
theorem memLp_of_integrable_of_uniform_bound
    {f : ℝ → ℝ} {M r : ℝ}
    (hr : 1 ≤ r)
    (hf_cont : Continuous f) (hf_int : Integrable f volume)
    (hf_bound : ∀ x, |f x| ≤ M) :
    MemLp f (ENNReal.ofReal r) volume := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hrm1 : 0 ≤ r - 1 := sub_nonneg.mpr hr
  have hdom : Integrable (fun x : ℝ => M ^ (r - 1) * |f x|) volume :=
    hf_int.norm.const_mul (M ^ (r - 1))
  have hpow : Integrable (fun x : ℝ => ‖f x‖ ^ r) volume := by
    refine hdom.mono' ?_ ?_
    · exact ((hf_cont.norm.rpow_const
        (fun _ => Or.inr hr0.le))).aestronglyMeasurable
    · filter_upwards with x
      have hfx0 : 0 ≤ |f x| := abs_nonneg _
      have hpow_le : |f x| ^ (r - 1) ≤ M ^ (r - 1) :=
        Real.rpow_le_rpow hfx0 (hf_bound x) hrm1
      simp only [Real.norm_eq_abs]
      calc
        |(|f x| ^ r)| = |f x| ^ r :=
          abs_of_nonneg (Real.rpow_nonneg hfx0 r)
        _ = |f x| ^ ((r - 1) + 1) := by
          congr 1
          ring
        _ = |f x| ^ (r - 1) * |f x| ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg hfx0 hrm1 zero_le_one
        _ = |f x| ^ (r - 1) * |f x| := by rw [Real.rpow_one]
        _ ≤ M ^ (r - 1) * |f x| :=
          mul_le_mul_of_nonneg_right hpow_le hfx0
  have hr_ne_zero : ENNReal.ofReal r ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hr0
  have hr_ne_top : ENNReal.ofReal r ≠ ⊤ := by simp
  apply (integrable_norm_rpow_iff hf_cont.aestronglyMeasurable
    hr_ne_zero hr_ne_top).mp
  simpa [ENNReal.toReal_ofReal hr0.le] using hpow

/-- The derivative of the one-dimensional Gaussian belongs to every finite
`L^r`, with `r ≥ 1`. -/
theorem heatKernel_deriv_memLp
    {t r : ℝ} (ht : 0 < t) (hr : 1 ≤ r) :
    MemLp (fun x : ℝ => deriv (fun z : ℝ => heatKernel t z) x)
      (ENNReal.ofReal r) volume := by
  apply memLp_of_integrable_of_uniform_bound hr
    (ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht)
    (heatKernel_deriv_integrable ht)
  intro x
  simpa [wholeLineHeatKernelDerivLinfBound] using
    heatKernel_deriv_pointwise_bound ht x

/-- The finite `L^r` norm of the Gaussian derivative is bounded by the
`L¹`--`L∞` interpolation constant above. -/
theorem heatKernel_deriv_Lp_norm_le
    {t r : ℝ} (ht : 0 < t) (hr : 1 ≤ r) :
    (∫ x : ℝ, ‖deriv (fun z : ℝ => heatKernel t z) x‖ ^ r) ^ (1 / r) ≤
      wholeLineHeatKernelDerivLpBound t r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hrm1 : 0 ≤ r - 1 := sub_nonneg.mpr hr
  let C := wholeLineHeatKernelDerivLinfBound t
  have hC : 0 ≤ C := wholeLineHeatKernelDerivLinfBound_nonneg ht
  have hpoint : ∀ x : ℝ,
      ‖deriv (fun z : ℝ => heatKernel t z) x‖ ^ r ≤
        C ^ (r - 1) *
          |deriv (fun z : ℝ => heatKernel t z) x| := by
    intro x
    have hx0 : 0 ≤ |deriv (fun z : ℝ => heatKernel t z) x| := abs_nonneg _
    have hxC : |deriv (fun z : ℝ => heatKernel t z) x| ≤ C := by
      simpa [C, wholeLineHeatKernelDerivLinfBound] using
        heatKernel_deriv_pointwise_bound ht x
    have hpow_le : |deriv (fun z : ℝ => heatKernel t z) x| ^ (r - 1) ≤
        C ^ (r - 1) := Real.rpow_le_rpow hx0 hxC hrm1
    rw [Real.norm_eq_abs]
    calc
      |deriv (fun z : ℝ => heatKernel t z) x| ^ r =
          |deriv (fun z : ℝ => heatKernel t z) x| ^ ((r - 1) + 1) := by
        congr 1
        ring
      _ = |deriv (fun z : ℝ => heatKernel t z) x| ^ (r - 1) *
          |deriv (fun z : ℝ => heatKernel t z) x| ^ (1 : ℝ) :=
        Real.rpow_add_of_nonneg hx0 hrm1 zero_le_one
      _ = |deriv (fun z : ℝ => heatKernel t z) x| ^ (r - 1) *
          |deriv (fun z : ℝ => heatKernel t z) x| := by
        rw [Real.rpow_one]
      _ ≤ C ^ (r - 1) *
          |deriv (fun z : ℝ => heatKernel t z) x| :=
        mul_le_mul_of_nonneg_right hpow_le hx0
  have hleft_int : Integrable
      (fun x : ℝ => ‖deriv (fun z : ℝ => heatKernel t z) x‖ ^ r) volume :=
    by
      have hraw := (heatKernel_deriv_memLp ht hr).integrable_norm_rpow
        (by simp [hr0]) (by simp)
      simpa [ENNReal.toReal_ofReal hr0.le] using hraw
  have hright_int : Integrable
      (fun x : ℝ => C ^ (r - 1) *
        |deriv (fun z : ℝ => heatKernel t z) x|) volume :=
    (heatKernel_deriv_abs_integrable ht).const_mul (C ^ (r - 1))
  have hintegral :
      (∫ x : ℝ, ‖deriv (fun z : ℝ => heatKernel t z) x‖ ^ r) ≤
        C ^ (r - 1) * (2 / Real.sqrt (4 * Real.pi * t)) := by
    calc
      (∫ x : ℝ, ‖deriv (fun z : ℝ => heatKernel t z) x‖ ^ r) ≤
          ∫ x : ℝ, C ^ (r - 1) *
            |deriv (fun z : ℝ => heatKernel t z) x| := by
        exact integral_mono hleft_int hright_int hpoint
      _ = C ^ (r - 1) *
          (∫ x : ℝ, |deriv (fun z : ℝ => heatKernel t z) x|) := by
        rw [integral_const_mul]
      _ = C ^ (r - 1) * (2 / Real.sqrt (4 * Real.pi * t)) := by
        rw [heatKernel_deriv_abs_integral ht]
  have hleft0 : 0 ≤
      ∫ x : ℝ, ‖deriv (fun z : ℝ => heatKernel t z) x‖ ^ r :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) r
  have hroot := Real.rpow_le_rpow hleft0 hintegral
    (one_div_nonneg.mpr hr0.le)
  simpa [wholeLineHeatKernelDerivLpBound, C] using hroot

/-- Translation and reflection preserve the finite `L^r` norm of a Gaussian
derivative row. -/
theorem heatKernel_deriv_translated_Lp_norm_eq
    {t r : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y : ℝ,
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x‖ ^ r) ^ (1 / r) =
      (∫ z : ℝ,
        ‖deriv (fun w : ℝ => heatKernel t w) z‖ ^ r) ^ (1 / r) := by
  have hkey :
      (fun y : ℝ =>
          ‖deriv (fun z : ℝ => heatKernel t (z - y)) x‖ ^ r) =
        fun y : ℝ =>
          (fun z : ℝ => ‖deriv (fun w : ℝ => heatKernel t w) z‖ ^ r)
            (y + (-x)) := by
    funext y
    rw [deriv_heatKernel_translated_left ht x y]
    change
      ‖-((x - y) / (2 * t)) * heatKernel t (x - y)‖ ^ r =
        ‖deriv (fun w : ℝ => heatKernel t w) (y + (-x))‖ ^ r
    rw [deriv_heatKernel ht (y + (-x))]
    rw [show x - y = -(y + (-x)) by ring, heatKernel_neg]
    have hneg :
        -(-(y + -x) / (2 * t)) * heatKernel t (y + -x) =
          -(-((y + -x) / (2 * t)) * heatKernel t (y + -x)) := by
      ring
    rw [hneg, norm_neg]
  rw [hkey]
  have hshift :
      (∫ y : ℝ,
          (fun z : ℝ => ‖deriv (fun w : ℝ => heatKernel t w) z‖ ^ r)
            (y + (-x))) =
        ∫ z : ℝ, ‖deriv (fun w : ℝ => heatKernel t w) z‖ ^ r := by
    simpa using integral_add_right_eq_self
      (fun z : ℝ => ‖deriv (fun w : ℝ => heatKernel t w) z‖ ^ r) (-x)
  rw [hshift]

/-- A translated Gaussian derivative row belongs to finite `L^r`. -/
theorem heatKernel_deriv_translated_memLp
    {t r : ℝ} (ht : 0 < t) (hr : 1 ≤ r) (x : ℝ) :
    MemLp (fun y : ℝ => deriv (fun z : ℝ => heatKernel t (z - y)) x)
      (ENNReal.ofReal r) volume := by
  let a : ℝ := x
  have hmpNeg : MeasurePreserving (fun y : ℝ => -y) volume volume :=
    Measure.measurePreserving_neg volume
  have hmpAdd : MeasurePreserving (fun y : ℝ => a + y) volume volume :=
    measurePreserving_add_left volume a
  have hcomp := (heatKernel_deriv_memLp ht hr).comp_measurePreserving
    (hmpAdd.comp hmpNeg)
  convert hcomp using 1
  funext y
  rw [deriv_heatKernel_translated_left ht x y]
  dsimp [a, Function.comp_apply]
  simpa using (deriv_heatKernel ht (x - y)).symm

/-- Whole-line `L^p → L∞` smoothing for convolution with the first spatial
derivative of the heat kernel.  Its time singularity is contained explicitly
in `wholeLineHeatKernelDerivLpBound`. -/
theorem heatKernel_deriv_convolution_Lp_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t p r : ℝ} (ht : 0 < t)
    (hrp : r.HolderConjugate p) (x : ℝ)
    (hf_mem : MemLp f (ENNReal.ofReal p) volume) :
    |∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| ≤
      wholeLineHeatKernelDerivLpBound t r *
        (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) := by
  have hr : 1 ≤ r := hrp.lt.le
  have hkernel_mem := heatKernel_deriv_translated_memLp ht hr x
  have hholder :
      (∫ y : ℝ,
          ‖deriv (fun z : ℝ => heatKernel t (z - y)) x‖ * ‖f y‖) ≤
        (∫ y : ℝ,
          ‖deriv (fun z : ℝ => heatKernel t (z - y)) x‖ ^ r) ^ (1 / r) *
          (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) :=
    integral_mul_norm_le_Lp_mul_Lq hrp hkernel_mem hf_mem
  have hkernel_norm :
      (∫ y : ℝ,
          ‖deriv (fun z : ℝ => heatKernel t (z - y)) x‖ ^ r) ^ (1 / r) ≤
        wholeLineHeatKernelDerivLpBound t r := by
    rw [heatKernel_deriv_translated_Lp_norm_eq ht x]
    exact heatKernel_deriv_Lp_norm_le ht hr
  have hfroot0 : 0 ≤ (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) :=
    Real.rpow_nonneg (integral_nonneg fun y =>
      Real.rpow_nonneg (norm_nonneg (f y)) p) _
  calc
    |∫ y : ℝ,
        deriv (fun z : ℝ => heatKernel t (z - y)) x * f y| =
        ‖∫ y : ℝ,
          deriv (fun z : ℝ => heatKernel t (z - y)) x * f y‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ,
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x * f y‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y : ℝ,
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x‖ * ‖f y‖ := by
      congr 1
      funext y
      rw [norm_mul]
    _ ≤ (∫ y : ℝ,
        ‖deriv (fun z : ℝ => heatKernel t (z - y)) x‖ ^ r) ^ (1 / r) *
          (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) := hholder
    _ ≤ wholeLineHeatKernelDerivLpBound t r *
          (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) :=
      mul_le_mul_of_nonneg_right hkernel_norm hfroot0

/-- The damped whole-line semigroup version used in the localized Duhamel
formula of Proposition 1.1. -/
theorem modifiedHeatKernel_deriv_convolution_Lp_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t p r : ℝ} (ht : 0 < t)
    (hrp : r.HolderConjugate p) (x : ℝ)
    (hf_mem : MemLp f (ENNReal.ofReal p) volume) :
    |∫ y : ℝ, Real.exp (-t) *
        (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)| ≤
      Real.exp (-t) *
        (wholeLineHeatKernelDerivLpBound t r *
          (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p)) := by
  have heq :
      (∫ y : ℝ, Real.exp (-t) *
        (deriv (fun z : ℝ => heatKernel t (z - y)) x * f y)) =
        Real.exp (-t) *
          ∫ y : ℝ, deriv (fun z : ℝ => heatKernel t (z - y)) x * f y := by
    rw [integral_const_mul]
  rw [heq, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (heatKernel_deriv_convolution_Lp_Linfty_smoothing_abs
      ht hrp x hf_mem) (Real.exp_nonneg _)

section AxiomAudit

#print axioms memLp_of_integrable_of_uniform_bound
#print axioms heatKernel_deriv_memLp
#print axioms heatKernel_deriv_Lp_norm_le
#print axioms heatKernel_deriv_convolution_Lp_Linfty_smoothing_abs
#print axioms modifiedHeatKernel_deriv_convolution_Lp_Linfty_smoothing_abs

end AxiomAudit

end ShenWork.Paper1
