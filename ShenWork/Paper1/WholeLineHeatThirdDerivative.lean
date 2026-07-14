import ShenWork.PaperOne.WholeLineConvolutionDifferentiation
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

open Filter Topology MeasureTheory Real Set
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.Paper1

/-!
# Third spatial derivative of the whole-line Gaussian

The divergence-form Duhamel term needs one more spatial derivative at points
whose recent source is supported away from the evaluation point.  This file
keeps that analytic input explicit: a closed formula and a Gaussian-tail
majorant for the third derivative.
-/

/-- Closed formula for the third spatial derivative of the heat kernel. -/
theorem heatKernel_thirdDeriv_hasDerivAt
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt
      (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
      ((3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)) * heatKernel t x) x := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hrepr :
      (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z) =
        fun z : ℝ =>
          (1 / (2 * t)) * (z ^ 2 / (2 * t) - 1) * heatKernel t z := by
    funext z
    exact deriv_deriv_heatKernel ht z
  rw [hrepr]
  have hquad : HasDerivAt
      (fun z : ℝ => (1 / (2 * t)) * (z ^ 2 / (2 * t) - 1))
      (x / (2 * t ^ 2)) x := by
    have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
      simpa [two_mul] using (hasDerivAt_id x).pow 2
    convert
      (hasDerivAt_const x (1 / (2 * t))).mul
        ((hsq.div_const (2 * t)).sub_const 1)
      using 1 <;> field_simp [ht0] <;> ring
  have hprod := hquad.mul (heatKernel_hasDerivAt ht x)
  convert hprod using 1
  field_simp [ht0]
  ring

/-- Evaluation form of the third spatial derivative. -/
theorem deriv_deriv_deriv_heatKernel
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        x =
      (3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)) * heatKernel t x :=
  (heatKernel_thirdDeriv_hasDerivAt ht x).deriv

theorem deriv_deriv_heatKernel_global (t x : ℝ) :
    deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) x =
      (1 / (2 * t)) * (x ^ 2 / (2 * t) - 1) * heatKernel t x := by
  rcases lt_or_ge 0 t with ht | ht
  · exact deriv_deriv_heatKernel ht x
  · have hzero : (fun z : ℝ => heatKernel t z) = fun _ : ℝ => (0 : ℝ) := by
      funext z
      exact heatKernel_of_nonpos ht z
    simp [hzero, deriv_const, heatKernel_of_nonpos ht x]

theorem deriv_deriv_deriv_heatKernel_global (t x : ℝ) :
    deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        x =
      (3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)) * heatKernel t x := by
  rcases lt_or_ge 0 t with ht | ht
  · exact deriv_deriv_deriv_heatKernel ht x
  · have hzero : (fun z : ℝ => heatKernel t z) = fun _ : ℝ => (0 : ℝ) := by
      funext z
      exact heatKernel_of_nonpos ht z
    simp [hzero, deriv_const, heatKernel_of_nonpos ht x]

theorem measurable_secondDeriv_heatKernel_comp
    {τ p : ℝ × ℝ → ℝ} (hτ : Measurable τ) (hp : Measurable p) :
    Measurable (fun q : ℝ × ℝ =>
      deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (τ q) z) u) (p q)) := by
  have heq :
      (fun q : ℝ × ℝ =>
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel (τ q) z) u) (p q)) =
      fun q : ℝ × ℝ =>
        (1 / (2 * τ q)) * ((p q) ^ 2 / (2 * τ q) - 1) *
          heatKernel (τ q) (p q) := by
    funext q
    exact deriv_deriv_heatKernel_global (τ q) (p q)
  rw [heq]
  unfold heatKernel
  fun_prop

theorem measurable_thirdDeriv_heatKernel_comp
    {τ p : ℝ × ℝ → ℝ} (hτ : Measurable τ) (hp : Measurable p) :
    Measurable (fun q : ℝ × ℝ =>
      deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel (τ q) w) u) z)
        (p q)) := by
  have heq :
      (fun q : ℝ × ℝ =>
        deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel (τ q) w) u) z)
          (p q)) =
      fun q : ℝ × ℝ =>
        (3 * p q / (4 * (τ q) ^ 2) - (p q) ^ 3 / (8 * (τ q) ^ 3)) *
          heatKernel (τ q) (p q) := by
    funext q
    exact deriv_deriv_deriv_heatKernel_global (τ q) (p q)
  rw [heq]
  unfold heatKernel
  fun_prop

/-- A convenient positive coefficient for the third-kernel Gaussian bound. -/
noncomputable def heatThirdPointwiseBound (t : ℝ) : ℝ :=
  ((3 / (4 * t ^ 2)) * Real.sqrt (8 * t) +
      (1 / (8 * t ^ 3)) * (Real.sqrt (24 * t)) ^ 3) *
    (1 / Real.sqrt (4 * Real.pi * t))

theorem heatThirdPointwiseBound_nonneg
    {t : ℝ} (ht : 0 < t) :
    0 ≤ heatThirdPointwiseBound t := by
  unfold heatThirdPointwiseBound
  positivity

theorem heatHessPointwiseBound_mul_tailGaussianScale
    {t : ℝ} (ht : 0 < t) :
    heatHessPointwiseBound t *
        Real.sqrt (Real.pi / (1 / (16 * t))) = 5 / t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hst : Real.sqrt t ≠ 0 := by positivity
  have hscale : Real.sqrt (Real.pi / (1 / (16 * t))) =
      4 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show Real.pi / (1 / (16 * t)) = 16 * (Real.pi * t) by
      field_simp [ht0]]
    rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul Real.pi_pos.le]
    ring
  have hden : Real.sqrt (4 * Real.pi * t) =
      2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show (4 * Real.pi * t : ℝ) = (2 : ℝ) ^ 2 * (Real.pi * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul Real.pi_pos.le]
    ring
  rw [hscale]
  unfold heatHessPointwiseBound
  rw [hden]
  field_simp [ht0, hsπ, hst]
  ring

noncomputable def heatThirdTailConstant : ℝ :=
  3 * Real.sqrt 2 + 2 * (Real.sqrt 6) ^ 3

theorem heatThirdTailConstant_nonneg : 0 ≤ heatThirdTailConstant := by
  unfold heatThirdTailConstant
  positivity

theorem heatThirdPointwiseBound_mul_tailGaussianScale
    {t : ℝ} (ht : 0 < t) :
    heatThirdPointwiseBound t *
        Real.sqrt (Real.pi / (1 / (16 * t))) =
      heatThirdTailConstant / (t * Real.sqrt t) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hst : Real.sqrt t ≠ 0 := by positivity
  have hscale : Real.sqrt (Real.pi / (1 / (16 * t))) =
      4 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show Real.pi / (1 / (16 * t)) = 16 * (Real.pi * t) by
      field_simp [ht0]]
    rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul Real.pi_pos.le]
    ring
  have hden : Real.sqrt (4 * Real.pi * t) =
      2 * Real.sqrt Real.pi * Real.sqrt t := by
    rw [show (4 * Real.pi * t : ℝ) = (2 : ℝ) ^ 2 * (Real.pi * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul Real.pi_pos.le]
    ring
  have h8 : Real.sqrt (8 * t) = 2 * Real.sqrt 2 * Real.sqrt t := by
    rw [show (8 * t : ℝ) = (2 : ℝ) ^ 2 * (2 * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have h24 : Real.sqrt (24 * t) = 2 * Real.sqrt 6 * Real.sqrt t := by
    rw [show (24 * t : ℝ) = (2 : ℝ) ^ 2 * (6 * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6)]
    ring
  have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hpow4 : (Real.sqrt t) ^ 4 = t ^ 2 := by
    calc
      (Real.sqrt t) ^ 4 = ((Real.sqrt t) ^ 2) ^ 2 := by ring
      _ = t ^ 2 := by rw [hsq]
  rw [hscale]
  unfold heatThirdPointwiseBound heatThirdTailConstant
  rw [hden, h8, h24]
  field_simp [ht0, hsπ, hst]
  ring_nf at *
  rw [hsq, hpow4]
  ring

private theorem abs_mul_exp_eighth_le_sqrt
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |x| * Real.exp (-x ^ 2 / (8 * t)) ≤ Real.sqrt (8 * t) := by
  have hε : 0 < 1 / (8 * t) := by positivity
  have h := Real.abs_mulExpNegMulSq_le hε (x := x)
  unfold Real.mulExpNegMulSq at h
  rw [show -(1 / (8 * t) * x * x) = -x ^ 2 / (8 * t) by ring] at h
  have hsqrt : Real.sqrt (1 / (8 * t))⁻¹ = Real.sqrt (8 * t) := by
    congr 1
    field_simp
  simpa [abs_mul, abs_of_pos (Real.exp_pos _), hsqrt] using h

private theorem abs_cube_mul_exp_eighth_le
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |x| ^ 3 * Real.exp (-x ^ 2 / (8 * t)) ≤
      (Real.sqrt (24 * t)) ^ 3 := by
  have hε : 0 < 1 / (24 * t) := by positivity
  have h := Real.abs_mulExpNegMulSq_le hε (x := x)
  unfold Real.mulExpNegMulSq at h
  rw [show -(1 / (24 * t) * x * x) = -x ^ 2 / (24 * t) by ring] at h
  have hsqrt : Real.sqrt (1 / (24 * t))⁻¹ = Real.sqrt (24 * t) := by
    congr 1
    field_simp
  have hbase : |x| * Real.exp (-x ^ 2 / (24 * t)) ≤
      Real.sqrt (24 * t) := by
    simpa [abs_mul, abs_of_pos (Real.exp_pos _), hsqrt] using h
  have hnonneg : 0 ≤ |x| * Real.exp (-x ^ 2 / (24 * t)) := by positivity
  have hpow := pow_le_pow_left₀ hnonneg hbase 3
  convert hpow using 1
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

/-- Third-derivative Gaussian bound retaining half of the heat exponential.
The retained factor is the one used for off-support time integrability. -/
theorem abs_thirdDeriv_heatKernel_le
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        x| ≤
      heatThirdPointwiseBound t * Real.exp (-x ^ 2 / (8 * t)) := by
  rw [deriv_deriv_deriv_heatKernel ht x]
  unfold heatKernel heatThirdPointwiseBound
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hsqrt0 : 0 < Real.sqrt (4 * Real.pi * t) := by positivity
  have hsplit : Real.exp (-x ^ 2 / (4 * t)) =
      Real.exp (-x ^ 2 / (8 * t)) * Real.exp (-x ^ 2 / (8 * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [ht0]
    ring
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (one_div_pos.mpr hsqrt0), hsplit]
  have htri :
      |3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)| ≤
        (3 / (4 * t ^ 2)) * |x| + (1 / (8 * t ^ 3)) * |x| ^ 3 := by
    calc
      |3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)|
          ≤ |3 * x / (4 * t ^ 2)| + |x ^ 3 / (8 * t ^ 3)| := abs_sub _ _
      _ = (3 / (4 * t ^ 2)) * |x| +
          (1 / (8 * t ^ 3)) * |x| ^ 3 := by
        rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3),
          abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2),
          abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < 8 * t ^ 3)]
        ring
  have hfirst := abs_mul_exp_eighth_le_sqrt ht x
  have hthird := abs_cube_mul_exp_eighth_le ht x
  have hcoeff1 : 0 ≤ 3 / (4 * t ^ 2) := by positivity
  have hcoeff3 : 0 ≤ 1 / (8 * t ^ 3) := by positivity
  have hconsume :
      ((3 / (4 * t ^ 2)) * |x| + (1 / (8 * t ^ 3)) * |x| ^ 3) *
          Real.exp (-x ^ 2 / (8 * t)) ≤
        (3 / (4 * t ^ 2)) * Real.sqrt (8 * t) +
          (1 / (8 * t ^ 3)) * (Real.sqrt (24 * t)) ^ 3 := by
    rw [add_mul]
    exact add_le_add
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hfirst hcoeff1)
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hthird hcoeff3)
  have hexp0 : 0 ≤ Real.exp (-x ^ 2 / (8 * t)) := Real.exp_nonneg _
  have hden0 : 0 ≤ 1 / Real.sqrt (4 * Real.pi * t) := by positivity
  have hAE :
      |3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)| *
          Real.exp (-x ^ 2 / (8 * t)) ≤
        ((3 / (4 * t ^ 2)) * |x| +
          (1 / (8 * t ^ 3)) * |x| ^ 3) *
            Real.exp (-x ^ 2 / (8 * t)) :=
    mul_le_mul_of_nonneg_right htri hexp0
  have hright0 :
      0 ≤ (1 / Real.sqrt (4 * Real.pi * t)) *
        Real.exp (-x ^ 2 / (8 * t)) :=
    mul_nonneg hden0 hexp0
  calc
    |3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)| *
          (1 / Real.sqrt (4 * Real.pi * t) *
            (Real.exp (-x ^ 2 / (8 * t)) *
              Real.exp (-x ^ 2 / (8 * t))))
        = (|3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)| *
            Real.exp (-x ^ 2 / (8 * t))) *
          (1 / Real.sqrt (4 * Real.pi * t) *
            Real.exp (-x ^ 2 / (8 * t))) := by ring
    _ ≤ (((3 / (4 * t ^ 2)) * |x| +
              (1 / (8 * t ^ 3)) * |x| ^ 3) *
            Real.exp (-x ^ 2 / (8 * t))) *
          (1 / Real.sqrt (4 * Real.pi * t) *
            Real.exp (-x ^ 2 / (8 * t))) :=
      mul_le_mul_of_nonneg_right hAE hright0
    _ ≤ ((3 / (4 * t ^ 2)) * Real.sqrt (8 * t) +
            (1 / (8 * t ^ 3)) * (Real.sqrt (24 * t)) ^ 3) *
          (1 / Real.sqrt (4 * Real.pi * t) *
            Real.exp (-x ^ 2 / (8 * t))) :=
      mul_le_mul_of_nonneg_right hconsume (mul_nonneg hden0 hexp0)
    _ = (((3 / (4 * t ^ 2)) * Real.sqrt (8 * t) +
            (1 / (8 * t ^ 3)) * (Real.sqrt (24 * t)) ^ 3) *
          (1 / Real.sqrt (4 * Real.pi * t))) *
            Real.exp (-x ^ 2 / (8 * t)) := by ring

theorem continuous_thirdDeriv_heatKernel
    {t : ℝ} (ht : 0 < t) :
    Continuous
      (fun x : ℝ => deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        x) := by
  have heq :
      (fun x : ℝ => deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        x) =
      fun x : ℝ =>
        (3 * x / (4 * t ^ 2) - x ^ 3 / (8 * t ^ 3)) * heatKernel t x := by
    funext x
    exact deriv_deriv_deriv_heatKernel ht x
  rw [heq]
  unfold heatKernel
  fun_prop

theorem thirdDeriv_heatKernel_abs_integrable
    {t : ℝ} (ht : 0 < t) :
    Integrable
      (fun x : ℝ =>
        |deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
          x|) volume := by
  have hb : 0 < 1 / (8 * t) := by positivity
  have hgauss : Integrable (fun x : ℝ => Real.exp (-(1 / (8 * t)) * x ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hmajor : Integrable
      (fun x : ℝ => heatThirdPointwiseBound t *
        Real.exp (-(1 / (8 * t)) * x ^ 2)) :=
    hgauss.const_mul _
  refine hmajor.mono' ?_ ?_
  · exact (continuous_thirdDeriv_heatKernel ht).abs.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    convert abs_thirdDeriv_heatKernel_le ht x using 1 <;> ring

/-- A convenient global `L¹` mass bound for the third Gaussian derivative.
The half-rate majorant is weakened once more so that the same explicit scale
used by the off-support estimate applies. -/
theorem thirdDeriv_heatKernel_abs_integral_le
    {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ,
      |deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        x|) ≤ heatThirdTailConstant / (t * Real.sqrt t) := by
  have hb : 0 < 1 / (16 * t) := by positivity
  have hmajor : Integrable
      (fun x : ℝ => heatThirdPointwiseBound t *
        Real.exp (-(1 / (16 * t)) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  calc
    (∫ x : ℝ,
        |deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
          x|) ≤
        ∫ x : ℝ, heatThirdPointwiseBound t *
          Real.exp (-(1 / (16 * t)) * x ^ 2) := by
      refine integral_mono (thirdDeriv_heatKernel_abs_integrable ht) hmajor (fun x => ?_)
      calc
        |deriv
            (fun z : ℝ => deriv
              (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
            x| ≤ heatThirdPointwiseBound t * Real.exp (-x ^ 2 / (8 * t)) :=
          abs_thirdDeriv_heatKernel_le ht x
        _ ≤ heatThirdPointwiseBound t *
            Real.exp (-(1 / (16 * t)) * x ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (heatThirdPointwiseBound_nonneg ht)
          apply Real.exp_le_exp.mpr
          have ht0 : t ≠ 0 := ne_of_gt ht
          field_simp [ht0]
          nlinarith [sq_nonneg x]
    _ = heatThirdPointwiseBound t *
          Real.sqrt (Real.pi / (1 / (16 * t))) := by
      rw [integral_const_mul, integral_gaussian (1 / (16 * t))]
    _ = heatThirdTailConstant / (t * Real.sqrt t) :=
      heatThirdPointwiseBound_mul_tailGaussianScale ht

theorem thirdDeriv_heatKernel_translated_integrable
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable
      (fun y : ℝ =>
        deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
          (x - y)) volume := by
  have habs : Integrable
      (fun y : ℝ =>
        |deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
          (x - y)|) volume := by
    simpa [sub_eq_add_neg, add_comm] using
      ((thirdDeriv_heatKernel_abs_integrable ht).comp_neg.comp_add_right (-x))
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ =>
        deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
          (x - y)) volume :=
    ((continuous_thirdDeriv_heatKernel ht).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact (integrable_norm_iff hmeas).mp (by
    simpa [Real.norm_eq_abs] using habs)

theorem thirdDeriv_heatKernel_mul_bounded_integrable
    {t M : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (x : ℝ)
    (hf : ∀ y, |f y| ≤ M) (hf_meas : AEStronglyMeasurable f volume) :
    Integrable
      (fun y : ℝ =>
        deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
          (x - y) * f y) volume :=
  (thirdDeriv_heatKernel_translated_integrable ht x).mul_bdd hf_meas
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hf y)

noncomputable def heatThirdWindowBound (t x r : ℝ) : ℝ :=
  heatThirdPointwiseBound t * Real.exp (r ^ 2 / (8 * t)) *
    Real.exp (-x ^ 2 / (16 * t))

theorem abs_thirdDeriv_heatKernel_le_window
    {t : ℝ} (ht : 0 < t) (x r : ℝ) {w : ℝ}
    (hw : |w - x| ≤ r) :
    |deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun q : ℝ => heatKernel t q) u) z)
        w| ≤ heatThirdWindowBound t x r := by
  refine (abs_thirdDeriv_heatKernel_le ht w).trans ?_
  rw [heatThirdWindowBound]
  have hr : 0 ≤ r := le_trans (abs_nonneg _) hw
  have hP : (1 / 2) * x ^ 2 - r ^ 2 ≤ w ^ 2 := by
    have hB : (w - x) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs]
      nlinarith [hw, abs_nonneg (w - x)]
    nlinarith [sq_nonneg (2 * w - x), hB]
  have hexp : Real.exp (-w ^ 2 / (8 * t)) ≤
      Real.exp (r ^ 2 / (8 * t)) * Real.exp (-x ^ 2 / (16 * t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht0 : t ≠ 0 := ne_of_gt ht
    rw [show -w ^ 2 / (8 * t) = (-2 * w ^ 2) / (16 * t) by
      field_simp [ht0]; ring]
    rw [show r ^ 2 / (8 * t) + -x ^ 2 / (16 * t) =
        (2 * r ^ 2 - x ^ 2) / (16 * t) by
      field_simp [ht0]; ring]
    apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 16 * t)).mpr
    nlinarith [hP]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hexp (heatThirdPointwiseBound_nonneg ht)

theorem integrable_heatThirdWindowBound_shift
    {t : ℝ} (ht : 0 < t) (x r : ℝ) :
    Integrable (fun y : ℝ => heatThirdWindowBound t (x - y) r) volume := by
  have hb : 0 < 1 / (16 * t) := by positivity
  have hbase : Integrable
      (fun y : ℝ => Real.exp (-(1 / (16 * t)) * (x - y) ^ 2)) :=
    ShenWork.PaperOne.ConvLeibniz.integrable_exp_neg_mul_sq_shift hb x
  convert hbase.const_mul
    (heatThirdPointwiseBound t * Real.exp (r ^ 2 / (8 * t))) using 1
  ext y
  unfold heatThirdWindowBound
  rw [show -((x - y) ^ 2) / (16 * t) =
      -(1 / (16 * t)) * (x - y) ^ 2 by ring]

/-- A bounded source has a third spatial heat-convolution derivative at every
positive time. -/
theorem heatConvolution_space_third_deriv
    {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt
      (fun z : ℝ => deriv
        (fun u : ℝ => deriv (fun w : ℝ => heatSemigroup t f w) u) z)
      (∫ y : ℝ,
        deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
          (x - y) * f y) x := by
  have hFeq :
      (fun z : ℝ => deriv
        (fun u : ℝ => deriv (fun w : ℝ => heatSemigroup t f w) u) z) =
      fun z : ℝ => ∫ y : ℝ,
        deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (z - y) * f y := by
    funext z
    exact (ShenWork.PaperOne.ConvLeibniz.heatConvolution_space_second_deriv
      (f := f) (t := t) (x := z) (M := M) ht hf_meas hf).deriv
  rw [hFeq]
  let F : ℝ → ℝ → ℝ := fun z y =>
    deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (z - y) * f y
  let F' : ℝ → ℝ → ℝ := fun z y =>
    deriv
      (fun q : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) q)
      (z - y) * f y
  let bound : ℝ → ℝ := fun y => heatThirdWindowBound t (x - y) 1 * M
  have hs : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x one_pos
  have hF_meas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) volume := by
    filter_upwards with z
    exact (ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
      ht z hf hf_meas).aestronglyMeasurable
  have hF_int : Integrable (F x) volume :=
    ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
      ht x hf hf_meas
  have hF'_meas : AEStronglyMeasurable (F' x) volume :=
    (thirdDeriv_heatKernel_mul_bounded_integrable ht x hf hf_meas).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball x 1,
      ‖F' z y‖ ≤ bound y := by
    filter_upwards with y z hz
    have harg : |(z - y) - (x - y)| ≤ 1 := by
      rw [show (z - y) - (x - y) = z - x by ring, ← Real.dist_eq]
      exact le_of_lt (Metric.mem_ball.mp hz)
    have hker := abs_thirdDeriv_heatKernel_le_window ht (x - y) 1 harg
    have hbound0 : 0 ≤ heatThirdWindowBound t (x - y) 1 := by
      unfold heatThirdWindowBound
      exact mul_nonneg
        (mul_nonneg (heatThirdPointwiseBound_nonneg ht) (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hker (hf y) (abs_nonneg _)
      hbound0
  have hbound_int : Integrable bound volume := by
    dsimp [bound]
    exact (integrable_heatThirdWindowBound_shift ht x 1).mul_const M
  have h_diff : ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun z' : ℝ => F z' y) (F' z y) z := by
    filter_upwards with y z _hz
    dsimp [F, F']
    have hinner : HasDerivAt (fun z' : ℝ => z' - y) 1 z := by
      simpa [sub_eq_add_neg] using (hasDerivAt_id z).add_const (-y)
    simpa [Function.comp_apply, deriv_deriv_deriv_heatKernel ht] using
      ((heatKernel_thirdDeriv_hasDerivAt ht (z - y)).comp z hinner).mul_const (f y)
  simpa [F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := bound) (F := F) (F' := F')
      (x₀ := x) (s := Metric.ball x 1)
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-- A Gaussian convolution gains an exponentially small factor when the
bounded source vanishes on a ball around the evaluation point. -/
theorem gaussianTailConvolution_abs_le
    {K f : ℝ → ℝ} {t C M r x : ℝ}
    (ht : 0 < t) (hC : 0 ≤ C) (hM : 0 ≤ M) (hr : 0 < r)
    (hK : ∀ z, |K z| ≤ C * Real.exp (-z ^ 2 / (8 * t)))
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0)
    (hint : Integrable (fun y : ℝ => K (x - y) * f y)) :
    |∫ y : ℝ, K (x - y) * f y| ≤
      (C * Real.exp (-r ^ 2 / (16 * t)) * M) *
        Real.sqrt (Real.pi / (1 / (16 * t))) := by
  have hb : 0 < 1 / (16 * t) := by positivity
  let G : ℝ → ℝ := fun y =>
    (C * Real.exp (-r ^ 2 / (16 * t)) * M) *
      Real.exp (-(1 / (16 * t)) * (x - y) ^ 2)
  have hGint : Integrable G := by
    exact (ShenWork.PaperOne.ConvLeibniz.integrable_exp_neg_mul_sq_shift hb x).const_mul _
  have hgauss :
      (∫ y : ℝ, Real.exp (-(1 / (16 * t)) * (x - y) ^ 2)) =
        Real.sqrt (Real.pi / (1 / (16 * t))) := by
    have heq :
        (fun y : ℝ => Real.exp (-(1 / (16 * t)) * (x - y) ^ 2)) =
          fun y : ℝ => Real.exp (-(1 / (16 * t)) * (y + -x) ^ 2) := by
      funext y
      congr 1
      ring
    rw [heq]
    calc
      (∫ y : ℝ,
          (fun q : ℝ => Real.exp (-(1 / (16 * t)) * q ^ 2)) (y + -x)) =
          ∫ q : ℝ, Real.exp (-(1 / (16 * t)) * q ^ 2) :=
        MeasureTheory.integral_add_right_eq_self (μ := volume)
          (fun q : ℝ => Real.exp (-(1 / (16 * t)) * q ^ 2)) (-x)
      _ = Real.sqrt (Real.pi / (1 / (16 * t))) :=
        integral_gaussian (1 / (16 * t))
  have hpoint : ∀ y, |K (x - y) * f y| ≤ G y := by
    intro y
    by_cases hy : dist y x < r
    · rw [hzero y hy, mul_zero, abs_zero]
      dsimp [G]
      positivity
    · have hyr : r ≤ |x - y| := by
        rw [Real.dist_eq] at hy
        rw [abs_sub_comm]
        exact le_of_not_gt hy
      have hsq : r ^ 2 ≤ (x - y) ^ 2 := by
        nlinarith [sq_abs (x - y), sq_nonneg r, abs_nonneg (x - y)]
      have hsplit : Real.exp (-(x - y) ^ 2 / (8 * t)) ≤
          Real.exp (-r ^ 2 / (16 * t)) *
            Real.exp (-(1 / (16 * t)) * (x - y) ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have ht0 : t ≠ 0 := ne_of_gt ht
        rw [show -(x - y) ^ 2 / (8 * t) =
            (-2 * (x - y) ^ 2) / (16 * t) by field_simp [ht0]; ring]
        rw [show -r ^ 2 / (16 * t) + -(1 / (16 * t)) * (x - y) ^ 2 =
            (-r ^ 2 - (x - y) ^ 2) / (16 * t) by field_simp [ht0]; ring]
        exact (div_le_div_iff_of_pos_right
          (by positivity : (0 : ℝ) < 16 * t)).2 (by linarith)
      rw [abs_mul]
      calc
        |K (x - y)| * |f y| ≤
            (C * Real.exp (-(x - y) ^ 2 / (8 * t))) * M :=
          mul_le_mul (hK _) (hf y) (abs_nonneg _)
            (mul_nonneg hC (Real.exp_nonneg _))
        _ ≤ (C *
              (Real.exp (-r ^ 2 / (16 * t)) *
                Real.exp (-(1 / (16 * t)) * (x - y) ^ 2))) * M := by
          gcongr
        _ = G y := by
          dsimp [G]
          ring
  calc
    |∫ y : ℝ, K (x - y) * f y| ≤ ∫ y : ℝ, |K (x - y) * f y| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ, G y := integral_mono hint.abs hGint hpoint
    _ = (C * Real.exp (-r ^ 2 / (16 * t)) * M) *
          Real.sqrt (Real.pi / (1 / (16 * t))) := by
      dsimp [G]
      rw [integral_const_mul, hgauss]

/-- Off-support bound for the second heat-kernel convolution. -/
theorem secondDeriv_heatKernel_convolution_zero_ball_abs_le
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |∫ y : ℝ,
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y) * f y| ≤
      (heatHessPointwiseBound t * Real.exp (-r ^ 2 / (16 * t)) * M) *
        Real.sqrt (Real.pi / (1 / (16 * t))) := by
  apply gaussianTailConvolution_abs_le ht
    (heatHessPointwiseBound_nonneg ht) hM hr
  · intro z
    simpa [show 4 * (2 * t) = 8 * t by ring] using
      abs_secondDeriv_heatKernel_le ht z
  · exact hf
  · exact hzero
  · exact ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
      ht x hf hf_meas

/-- Off-support bound for the third heat-kernel convolution. -/
theorem thirdDeriv_heatKernel_convolution_zero_ball_abs_le
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |∫ y : ℝ,
        deriv
          (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
          (x - y) * f y| ≤
      (heatThirdPointwiseBound t * Real.exp (-r ^ 2 / (16 * t)) * M) *
        Real.sqrt (Real.pi / (1 / (16 * t))) := by
  apply gaussianTailConvolution_abs_le ht
    (heatThirdPointwiseBound_nonneg ht) hM hr
  · intro z
    exact abs_thirdDeriv_heatKernel_le ht z
  · exact hf
  · exact hzero
  · exact thirdDeriv_heatKernel_mul_bounded_integrable ht x hf hf_meas

section WholeLineHeatThirdDerivativeAxiomAudit

#print axioms deriv_deriv_deriv_heatKernel
#print axioms abs_thirdDeriv_heatKernel_le
#print axioms heatConvolution_space_third_deriv
#print axioms thirdDeriv_heatKernel_convolution_zero_ball_abs_le

end WholeLineHeatThirdDerivativeAxiomAudit

end ShenWork.Paper1
