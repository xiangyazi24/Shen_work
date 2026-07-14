import ShenWork.Paper1.WholeLineCauchyBUCOffSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter Topology MeasureTheory Real Set
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.Paper1

open ShenWork.PDE.F1ProbeFractionalMultiplier

/-!
# The homogeneous equation on the negative set of the BUC fixed point

The truncated coupled sources vanish in a space-time neighborhood of every
strictly negative point.  This file supplies the remaining time-regularity
identities and assembles the local equation there.
-/

/-- The whole-line heat kernel satisfies the heat equation at positive time. -/
theorem heatKernel_time_hasDerivAt
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun τ : ℝ => heatKernel τ x)
      (deriv (fun z : ℝ => deriv (fun w : ℝ => heatKernel t w) z) x) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hlin : HasDerivAt (fun τ : ℝ => 4 * Real.pi * τ) (4 * Real.pi) t := by
    convert (hasDerivAt_id t).const_mul (4 * Real.pi) using 1 <;> ring
  have hlin0 : 4 * Real.pi * t ≠ 0 := by positivity
  have hsqrt0 : Real.sqrt (4 * Real.pi * t) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by positivity)
  have hsqrt : HasDerivAt (fun τ : ℝ => Real.sqrt (4 * Real.pi * τ))
      ((4 * Real.pi) / (2 * Real.sqrt (4 * Real.pi * t))) t := by
    simpa using hlin.sqrt hlin0
  have hcoef : HasDerivAt
      (fun τ : ℝ => 1 / Real.sqrt (4 * Real.pi * τ))
      (-(1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) t := by
    have hraw := (hasDerivAt_const t (1 : ℝ)).div hsqrt hsqrt0
    convert hraw using 1
    have hsquare : Real.sqrt (4 * Real.pi * t) ^ 2 = 4 * Real.pi * t :=
      Real.sq_sqrt (show 0 ≤ 4 * Real.pi * t by positivity)
    have hsquare' : Real.sqrt (t * 4 * Real.pi) ^ 2 = 4 * Real.pi * t := by
      rw [show t * 4 * Real.pi = 4 * Real.pi * t by ring]
      exact hsquare
    field_simp [ht0, hpi, hsqrt0]
    rw [hsquare']
    ring
  have hden : HasDerivAt (fun τ : ℝ => 4 * τ) 4 t := by
    convert (hasDerivAt_id t).const_mul 4 using 1 <;> ring
  have harg : HasDerivAt (fun τ : ℝ => -x ^ 2 / (4 * τ))
      (x ^ 2 / (4 * t ^ 2)) t := by
    have hraw := (hasDerivAt_const t (-x ^ 2)).div hden (by positivity : 4 * t ≠ 0)
    convert hraw using 1 <;> field_simp [ht0] <;> ring
  have hformula : HasDerivAt (fun τ : ℝ => heatKernel τ x)
      ((1 / (2 * t)) * (x ^ 2 / (2 * t) - 1) * heatKernel t x) t := by
    unfold heatKernel
    convert hcoef.mul harg.exp using 1 <;> field_simp [ht0] <;> ring
  simpa [ShenWork.IntervalNeumannFullKernel.deriv_deriv_heatKernel ht x] using hformula

/-- The modified value kernel has generator `∂xx - 1` at positive time. -/
theorem wholeLineModifiedHeatKernel_time_hasDerivAt
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun τ : ℝ => wholeLineModifiedHeatKernel τ x)
      (Real.exp (-t) *
          deriv (fun z : ℝ => deriv (fun w : ℝ => heatKernel t w) z) x -
        wholeLineModifiedHeatKernel t x) t := by
  have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-τ)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  unfold wholeLineModifiedHeatKernel
  convert hexp.mul (heatKernel_time_hasDerivAt ht x) using 1 <;> ring

/-- The spatial-gradient heat kernel also satisfies the heat equation in its
time parameter. -/
theorem heatKernelGradient_time_hasDerivAt
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt
      (fun τ : ℝ => deriv (fun z : ℝ => heatKernel τ z) x)
      (deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        x) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hcoeff : HasDerivAt (fun τ : ℝ => -(x / (2 * τ)))
      (x / (2 * t ^ 2)) t := by
    have hden : HasDerivAt (fun τ : ℝ => 2 * τ) 2 t := by
      convert (hasDerivAt_id t).const_mul 2 using 1 <;> ring
    have hraw := (hasDerivAt_const t (-x)).div hden (by positivity : 2 * t ≠ 0)
    convert hraw using 1
    · funext τ
      change -(x / (2 * τ)) = (-x) / (2 * τ)
      ring
    · field_simp [ht0]
      ring
  have hformula : HasDerivAt
      (fun τ : ℝ => -(x / (2 * τ)) * heatKernel τ x)
      (deriv
        (fun z : ℝ => deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
        x) t := by
    have hprod := hcoeff.mul (heatKernel_time_hasDerivAt ht x)
    convert hprod using 1
    rw [deriv_deriv_deriv_heatKernel ht x]
    rw [ShenWork.IntervalNeumannFullKernel.deriv_deriv_heatKernel ht x]
    field_simp [ht0]
    ring
  apply hformula.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with τ hτ
  exact deriv_heatKernel hτ x

/-- The modified gradient kernel has generator `∂xx - 1` at positive time. -/
theorem wholeLineModifiedHeatGradientKernel_time_hasDerivAt
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun τ : ℝ => wholeLineModifiedHeatGradientKernel τ x)
      (Real.exp (-t) *
          deriv
            (fun z : ℝ => deriv
              (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
            x -
        wholeLineModifiedHeatGradientKernel t x) t := by
  have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-τ)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  unfold wholeLineModifiedHeatGradientKernel
  convert hexp.mul (heatKernelGradient_time_hasDerivAt ht x) using 1 <;> ring

def wholeLineModifiedHeatHessKernel (t x : ℝ) : ℝ :=
  Real.exp (-t) *
    deriv (fun z : ℝ => deriv (fun w : ℝ => heatKernel t w) z) x

def wholeLineModifiedHeatThirdKernel (t x : ℝ) : ℝ :=
  Real.exp (-t) *
    deriv
      (fun z : ℝ => deriv
        (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z)
      x

theorem wholeLineCauchyHeatOp_eq_modifiedKernel_integral
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyHeatOp t f x =
      ∫ y : ℝ, wholeLineModifiedHeatKernel t (x - y) * f y := by
  unfold wholeLineCauchyHeatOp modifiedSemigroup heatSemigroup
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  unfold wholeLineModifiedHeatKernel
  ring

theorem wholeLineCauchyHeatGradOp_eq_modifiedKernel_integral
    {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyHeatGradOp t f x =
      ∫ y : ℝ, wholeLineModifiedHeatGradientKernel t (x - y) * f y := by
  unfold wholeLineCauchyHeatGradOp
  apply integral_congr_ae
  filter_upwards with y
  rw [deriv_heatKernel_translated_left ht x y]
  unfold wholeLineModifiedHeatGradientKernel
  rw [deriv_heatKernel ht (x - y)]
  ring

theorem wholeLineCauchyHeatHessOp_eq_modifiedKernel_integral
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyHeatHessOp t f x =
      ∫ y : ℝ, wholeLineModifiedHeatHessKernel t (x - y) * f y := by
  unfold wholeLineCauchyHeatHessOp
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  unfold wholeLineModifiedHeatHessKernel
  ring

theorem wholeLineCauchyHeatThirdOp_eq_modifiedKernel_integral
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyHeatThirdOp t f x =
      ∫ y : ℝ, wholeLineModifiedHeatThirdKernel t (x - y) * f y := by
  unfold wholeLineCauchyHeatThirdOp
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  unfold wholeLineModifiedHeatThirdKernel
  ring

theorem abs_wholeLineModifiedHeatHessKernel_local_time_le
    {t s : ℝ} (ht : 0 < t) (hs : s ∈ Metric.ball t (t / 2)) (z : ℝ) :
    |wholeLineModifiedHeatHessKernel s z| ≤
      ((1 / t) * (z ^ 2 / t + 1)) *
        ((1 / Real.sqrt (2 * Real.pi * t)) *
          Real.exp (-(1 / (6 * t)) * z ^ 2)) := by
  have hdist := Metric.mem_ball.mp hs
  rw [Real.dist_eq] at hdist
  have hslow : t / 2 < s := by linarith [(abs_lt.mp hdist).1]
  have hspos : 0 < s := by linarith
  have ht_two_s : t ≤ 2 * s := by linarith
  have hinv : 1 / (2 * s) ≤ 1 / t :=
    one_div_le_one_div_of_le ht ht_two_s
  have hzdiv : z ^ 2 / (2 * s) ≤ z ^ 2 / t := by
    have := mul_le_mul_of_nonneg_left hinv (sq_nonneg z)
    convert this using 1 <;> ring
  have hcoeff :
      |(1 / (2 * s)) * (z ^ 2 / (2 * s) - 1)| ≤
        (1 / t) * (z ^ 2 / t + 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * s))]
    have habs : |z ^ 2 / (2 * s) - 1| ≤ z ^ 2 / (2 * s) + 1 := by
      calc
        |z ^ 2 / (2 * s) - 1| ≤
            |z ^ 2 / (2 * s)| + |(1 : ℝ)| := abs_sub _ _
        _ = z ^ 2 / (2 * s) + 1 := by
          rw [abs_of_nonneg (by positivity : 0 ≤ z ^ 2 / (2 * s)), abs_one]
    calc
      (1 / (2 * s)) * |z ^ 2 / (2 * s) - 1| ≤
          (1 / (2 * s)) * (z ^ 2 / (2 * s) + 1) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ (1 / t) * (z ^ 2 / t + 1) :=
        mul_le_mul hinv (add_le_add hzdiv le_rfl) (by positivity) (by positivity)
  have hrepr : wholeLineModifiedHeatHessKernel s z =
      ((1 / (2 * s)) * (z ^ 2 / (2 * s) - 1)) *
        wholeLineModifiedHeatKernel s z := by
    unfold wholeLineModifiedHeatHessKernel wholeLineModifiedHeatKernel
    rw [ShenWork.IntervalNeumannFullKernel.deriv_deriv_heatKernel hspos z]
    ring
  rw [hrepr, abs_mul]
  exact mul_le_mul hcoeff
    (abs_wholeLineModifiedHeatKernel_local_time_le ht hs z)
    (abs_nonneg _) (by positivity)

theorem abs_wholeLineModifiedHeatThirdKernel_local_time_le
    {t s : ℝ} (ht : 0 < t) (hs : s ∈ Metric.ball t (t / 2)) (z : ℝ) :
    |wholeLineModifiedHeatThirdKernel s z| ≤
      (3 / t + z ^ 2 / t ^ 2) *
        ((((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
          Real.sqrt (12 * t))) *
            Real.exp (-(1 / (12 * t)) * z ^ 2)) := by
  have hdist := Metric.mem_ball.mp hs
  rw [Real.dist_eq] at hdist
  have hslow : t / 2 < s := by linarith [(abs_lt.mp hdist).1]
  have hspos : 0 < s := by linarith
  have ht_two_s : t ≤ 2 * s := by linarith
  have hinv : 1 / (2 * s) ≤ 1 / t :=
    one_div_le_one_div_of_le ht ht_two_s
  have hinv_sq : 1 / (4 * s ^ 2) ≤ 1 / t ^ 2 := by
    have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 1 / (2 * s)) hinv
    convert hsq using 1 <;> field_simp <;> ring
  have hcoeff :
      |-3 / (2 * s) + z ^ 2 / (4 * s ^ 2)| ≤
        3 / t + z ^ 2 / t ^ 2 := by
    calc
      |-3 / (2 * s) + z ^ 2 / (4 * s ^ 2)| ≤
          |-3 / (2 * s)| + |z ^ 2 / (4 * s ^ 2)| := abs_add_le _ _
      _ = 3 * (1 / (2 * s)) + z ^ 2 * (1 / (4 * s ^ 2)) := by
        rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)),
          abs_of_nonneg (by positivity : 0 ≤ z ^ 2 / (4 * s ^ 2))]
        ring
      _ ≤ 3 * (1 / t) + z ^ 2 * (1 / t ^ 2) := by gcongr
      _ = 3 / t + z ^ 2 / t ^ 2 := by ring
  have hrepr : wholeLineModifiedHeatThirdKernel s z =
      (-3 / (2 * s) + z ^ 2 / (4 * s ^ 2)) *
        wholeLineModifiedHeatGradientKernel s z := by
    unfold wholeLineModifiedHeatThirdKernel wholeLineModifiedHeatGradientKernel
    rw [deriv_deriv_deriv_heatKernel hspos z, deriv_heatKernel hspos z]
    field_simp [ne_of_gt hspos]
    ring
  rw [hrepr, abs_mul]
  exact mul_le_mul hcoeff
    (abs_wholeLineModifiedHeatGradientKernel_local_time_le ht hs z)
    (abs_nonneg _) (by positivity)

theorem integrable_sq_mul_exp_neg_mul_sq_shift
    {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Integrable (fun y : ℝ =>
      (x - y) ^ 2 * Real.exp (-b * (x - y) ^ 2)) volume := by
  have hbase : Integrable (fun y : ℝ =>
      y ^ 2 * Real.exp (-b * y ^ 2)) volume := by
    simpa [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (s := (2 : ℝ)) (by norm_num))
  have hshift := hbase.comp_add_right (-x)
  convert hshift using 1
  ext y
  congr 1 <;> ring

/-- Positive-time differentiation of the modified value-kernel convolution
against a merely bounded measurable function. -/
theorem wholeLineModifiedHeatConvolution_time_hasDerivAt
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∫ y : ℝ,
        wholeLineModifiedHeatKernel τ (x - y) * f y)
      (∫ y : ℝ,
        (wholeLineModifiedHeatHessKernel t (x - y) -
          wholeLineModifiedHeatKernel t (x - y)) * f y) t := by
  let A : ℝ := 1 / Real.sqrt (2 * Real.pi * t)
  let bound : ℝ → ℝ := fun y =>
    ((((1 / t) * ((x - y) ^ 2 / t + 1)) *
          (A * Real.exp (-(1 / (6 * t)) * (x - y) ^ 2)) +
        A * Real.exp (-(1 / (6 * t)) * (x - y) ^ 2)) * M)
  let F : ℝ → ℝ → ℝ := fun τ y =>
    wholeLineModifiedHeatKernel τ (x - y) * f y
  let F' : ℝ → ℝ → ℝ := fun τ y =>
    (wholeLineModifiedHeatHessKernel τ (x - y) -
      wholeLineModifiedHeatKernel τ (x - y)) * f y
  have hball : Metric.ball t (t / 2) ∈ nhds t :=
    Metric.ball_mem_nhds t (half_pos ht)
  have hkernel_int : ∀ {τ : ℝ}, 0 < τ →
      Integrable (fun y : ℝ => wholeLineModifiedHeatKernel τ (x - y)) volume := by
    intro τ hτ
    have hbase := (wholeLineModifiedHeatKernel_integrable hτ).comp_neg.comp_add_right (-x)
    convert hbase using 1
    ext y
    congr 1
    ring
  have hF_int_at : ∀ {τ : ℝ}, 0 < τ → Integrable (F τ) volume := by
    intro τ hτ
    exact (hkernel_int hτ).mul_bdd hf_meas
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  have hhess_int : Integrable
      (fun y : ℝ => wholeLineModifiedHeatHessKernel t (x - y)) volume := by
    have hbase :=
      (ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_translated_integrable ht x)
        |>.const_mul (Real.exp (-t))
    simpa [wholeLineModifiedHeatHessKernel] using hbase
  have hF'_int : Integrable (F' t) volume := by
    have hdiff := hhess_int.sub (hkernel_int ht)
    exact hdiff.mul_bdd hf_meas
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  have hF_meas : ∀ᶠ τ in nhds t, AEStronglyMeasurable (F τ) volume := by
    filter_upwards [hball] with τ hτ
    have hdist := Metric.mem_ball.mp hτ
    rw [Real.dist_eq] at hdist
    exact (hF_int_at (by linarith [(abs_lt.mp hdist).1])).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    have hb : 0 < 1 / (6 * t) := by positivity
    have h0 := ShenWork.PaperOne.ConvLeibniz.integrable_exp_neg_mul_sq_shift hb x
    have h2 := integrable_sq_mul_exp_neg_mul_sq_shift hb x
    have hsum :=
      (h2.const_mul (((1 / t) * (1 / t)) * A)).add
        (h0.const_mul (((1 / t) + 1) * A))
    have hscaled := hsum.const_mul M
    convert hscaled using 1
    ext y
    dsimp [bound]
    ring
  have h_bound : ∀ᵐ y ∂volume, ∀ τ ∈ Metric.ball t (t / 2),
      ‖F' τ y‖ ≤ bound y := by
    filter_upwards with y
    intro τ hτ
    have hH := abs_wholeLineModifiedHeatHessKernel_local_time_le ht hτ (x - y)
    have hV := abs_wholeLineModifiedHeatKernel_local_time_le ht hτ (x - y)
    have hf0 := hf y
    dsimp [F', bound]
    rw [abs_mul]
    calc
      |wholeLineModifiedHeatHessKernel τ (x - y) -
            wholeLineModifiedHeatKernel τ (x - y)| * |f y| ≤
          (|wholeLineModifiedHeatHessKernel τ (x - y)| +
            |wholeLineModifiedHeatKernel τ (x - y)|) * M := by
              exact mul_le_mul (abs_sub _ _) hf0 (abs_nonneg _)
                (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ ((((1 / t) * ((x - y) ^ 2 / t + 1)) *
            (A * Real.exp (-(1 / (6 * t)) * (x - y) ^ 2)) +
          A * Real.exp (-(1 / (6 * t)) * (x - y) ^ 2)) * M) := by
            exact mul_le_mul_of_nonneg_right (add_le_add hH hV) hM
  have h_diff : ∀ᵐ y ∂volume, ∀ τ ∈ Metric.ball t (t / 2),
      HasDerivAt (fun q : ℝ => F q y) (F' τ y) τ := by
    filter_upwards with y τ hτ
    have hdist := Metric.mem_ball.mp hτ
    rw [Real.dist_eq] at hdist
    have hτpos : 0 < τ := by linarith [(abs_lt.mp hdist).1]
    simpa [F, F', wholeLineModifiedHeatHessKernel] using
      (wholeLineModifiedHeatKernel_time_hasDerivAt hτpos (x - y)).mul_const (f y)
  simpa [F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (x₀ := t) (s := Metric.ball t (t / 2))
      (F := F) (F' := F') (bound := bound)
      hball hF_meas (hF_int_at ht) hF'_int.aestronglyMeasurable
      h_bound hbound_int h_diff).2

/-- Positive-time differentiation of the modified gradient-kernel convolution
against a merely bounded measurable function. -/
theorem wholeLineModifiedHeatGradientConvolution_time_hasDerivAt
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    HasDerivAt
      (fun τ : ℝ => ∫ y : ℝ,
        wholeLineModifiedHeatGradientKernel τ (x - y) * f y)
      (∫ y : ℝ,
        (wholeLineModifiedHeatThirdKernel t (x - y) -
          wholeLineModifiedHeatGradientKernel t (x - y)) * f y) t := by
  let C : ℝ :=
    (1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) * Real.sqrt (12 * t)
  let bound : ℝ → ℝ := fun y =>
    (((3 / t + (x - y) ^ 2 / t ^ 2) *
          (C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) +
        C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) * M)
  let F : ℝ → ℝ → ℝ := fun τ y =>
    wholeLineModifiedHeatGradientKernel τ (x - y) * f y
  let F' : ℝ → ℝ → ℝ := fun τ y =>
    (wholeLineModifiedHeatThirdKernel τ (x - y) -
      wholeLineModifiedHeatGradientKernel τ (x - y)) * f y
  have hball : Metric.ball t (t / 2) ∈ nhds t :=
    Metric.ball_mem_nhds t (half_pos ht)
  have hkernel_int : ∀ {τ : ℝ}, 0 < τ →
      Integrable
        (fun y : ℝ => wholeLineModifiedHeatGradientKernel τ (x - y)) volume := by
    intro τ hτ
    have hbase :=
      (wholeLineModifiedHeatGradientKernel_integrable hτ).comp_neg.comp_add_right (-x)
    convert hbase using 1
    ext y
    congr 1
    ring
  have hF_int_at : ∀ {τ : ℝ}, 0 < τ → Integrable (F τ) volume := by
    intro τ hτ
    exact (hkernel_int hτ).mul_bdd hf_meas
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  have hthird_int : Integrable
      (fun y : ℝ => wholeLineModifiedHeatThirdKernel t (x - y)) volume := by
    have hbase := (thirdDeriv_heatKernel_translated_integrable ht x).const_mul
      (Real.exp (-t))
    simpa [wholeLineModifiedHeatThirdKernel] using hbase
  have hF'_int : Integrable (F' t) volume := by
    have hdiff := hthird_int.sub (hkernel_int ht)
    exact hdiff.mul_bdd hf_meas
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  have hF_meas : ∀ᶠ τ in nhds t, AEStronglyMeasurable (F τ) volume := by
    filter_upwards [hball] with τ hτ
    have hdist := Metric.mem_ball.mp hτ
    rw [Real.dist_eq] at hdist
    exact (hF_int_at (by linarith [(abs_lt.mp hdist).1])).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    have hb : 0 < 1 / (12 * t) := by positivity
    have h0 := ShenWork.PaperOne.ConvLeibniz.integrable_exp_neg_mul_sq_shift hb x
    have h2 := integrable_sq_mul_exp_neg_mul_sq_shift hb x
    have hsum :=
      (h2.const_mul ((1 / t ^ 2) * C)).add
        (h0.const_mul ((3 / t + 1) * C))
    have hscaled := hsum.const_mul M
    convert hscaled using 1
    ext y
    dsimp [bound]
    ring
  have h_bound : ∀ᵐ y ∂volume, ∀ τ ∈ Metric.ball t (t / 2),
      ‖F' τ y‖ ≤ bound y := by
    filter_upwards with y
    intro τ hτ
    have hT := abs_wholeLineModifiedHeatThirdKernel_local_time_le ht hτ (x - y)
    have hG := abs_wholeLineModifiedHeatGradientKernel_local_time_le ht hτ (x - y)
    have hf0 := hf y
    dsimp [F', bound]
    rw [abs_mul]
    calc
      |wholeLineModifiedHeatThirdKernel τ (x - y) -
            wholeLineModifiedHeatGradientKernel τ (x - y)| * |f y| ≤
          (|wholeLineModifiedHeatThirdKernel τ (x - y)| +
            |wholeLineModifiedHeatGradientKernel τ (x - y)|) * M := by
              exact mul_le_mul (abs_sub _ _) hf0 (abs_nonneg _)
                (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ (((3 / t + (x - y) ^ 2 / t ^ 2) *
            (C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) +
          C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) * M) := by
            exact mul_le_mul_of_nonneg_right (add_le_add hT hG) hM
  have h_diff : ∀ᵐ y ∂volume, ∀ τ ∈ Metric.ball t (t / 2),
      HasDerivAt (fun q : ℝ => F q y) (F' τ y) τ := by
    filter_upwards with y τ hτ
    have hdist := Metric.mem_ball.mp hτ
    rw [Real.dist_eq] at hdist
    have hτpos : 0 < τ := by linarith [(abs_lt.mp hdist).1]
    simpa [F, F', wholeLineModifiedHeatThirdKernel] using
      (wholeLineModifiedHeatGradientKernel_time_hasDerivAt hτpos (x - y)).mul_const
        (f y)
  simpa [F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (x₀ := t) (s := Metric.ball t (t / 2))
      (F := F) (F' := F') (bound := bound)
      hball hF_meas (hF_int_at ht) hF'_int.aestronglyMeasurable
      h_bound hbound_int h_diff).2

theorem wholeLineCauchyHeatOp_time_hasDerivAt
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    HasDerivAt (fun τ : ℝ => wholeLineCauchyHeatOp τ f x)
      (wholeLineCauchyHeatHessOp t f x - wholeLineCauchyHeatOp t f x) t := by
  have hraw := wholeLineModifiedHeatConvolution_time_hasDerivAt
    ht hM hf_meas hf x
  have hvalue_int : Integrable
      (fun y : ℝ => wholeLineModifiedHeatKernel t (x - y) * f y) volume := by
    have hkernel :=
      (wholeLineModifiedHeatKernel_integrable ht).comp_neg.comp_add_right (-x)
    have htranslated : Integrable
        (fun y : ℝ => wholeLineModifiedHeatKernel t (x - y)) volume := by
      convert hkernel using 1
      ext y
      congr 1
      ring
    exact htranslated.mul_bdd hf_meas
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  have hhess_int : Integrable
      (fun y : ℝ => wholeLineModifiedHeatHessKernel t (x - y) * f y) volume := by
    have hbase :=
      (ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
        ht x hf hf_meas).const_mul (Real.exp (-t))
    convert hbase using 1 <;> simp [wholeLineModifiedHeatHessKernel] <;> ring
  have hfun : (fun τ : ℝ => wholeLineCauchyHeatOp τ f x) =
      fun τ : ℝ => ∫ y : ℝ,
        wholeLineModifiedHeatKernel τ (x - y) * f y := by
    funext τ
    exact wholeLineCauchyHeatOp_eq_modifiedKernel_integral τ f x
  have hderiv :
      (∫ y : ℝ,
        (wholeLineModifiedHeatHessKernel t (x - y) -
          wholeLineModifiedHeatKernel t (x - y)) * f y) =
        wholeLineCauchyHeatHessOp t f x - wholeLineCauchyHeatOp t f x := by
    rw [show (fun y : ℝ =>
          (wholeLineModifiedHeatHessKernel t (x - y) -
            wholeLineModifiedHeatKernel t (x - y)) * f y) =
        fun y : ℝ =>
          wholeLineModifiedHeatHessKernel t (x - y) * f y -
            wholeLineModifiedHeatKernel t (x - y) * f y by
      funext y
      ring]
    rw [integral_sub hhess_int hvalue_int]
    rw [← wholeLineCauchyHeatHessOp_eq_modifiedKernel_integral,
      ← wholeLineCauchyHeatOp_eq_modifiedKernel_integral]
  rw [hfun, ← hderiv]
  exact hraw

theorem wholeLineCauchyHeatGradOp_time_hasDerivAt
    {f : ℝ → ℝ} {t M : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    HasDerivAt (fun τ : ℝ => wholeLineCauchyHeatGradOp τ f x)
      (wholeLineCauchyHeatThirdOp t f x - wholeLineCauchyHeatGradOp t f x) t := by
  have hraw := wholeLineModifiedHeatGradientConvolution_time_hasDerivAt
    ht hM hf_meas hf x
  have hgrad_int : Integrable
      (fun y : ℝ => wholeLineModifiedHeatGradientKernel t (x - y) * f y) volume := by
    have hkernel :=
      (wholeLineModifiedHeatGradientKernel_integrable ht).comp_neg.comp_add_right (-x)
    have htranslated : Integrable
        (fun y : ℝ => wholeLineModifiedHeatGradientKernel t (x - y)) volume := by
      convert hkernel using 1
      ext y
      congr 1
      ring
    exact htranslated.mul_bdd hf_meas
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  have hthird_int : Integrable
      (fun y : ℝ => wholeLineModifiedHeatThirdKernel t (x - y) * f y) volume := by
    have hbase := (thirdDeriv_heatKernel_mul_bounded_integrable ht x hf hf_meas).const_mul
      (Real.exp (-t))
    convert hbase using 1 <;> simp [wholeLineModifiedHeatThirdKernel] <;> ring
  have hfun : (fun τ : ℝ => wholeLineCauchyHeatGradOp τ f x) =
      fun τ : ℝ => ∫ y : ℝ,
        wholeLineModifiedHeatGradientKernel τ (x - y) * f y := by
    funext τ
    rcases lt_or_ge 0 τ with hτ | hτ
    · exact wholeLineCauchyHeatGradOp_eq_modifiedKernel_integral hτ f x
    · have hzero : (fun z : ℝ => heatKernel τ z) = fun _ => 0 := by
        funext z
        exact ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos hτ z
      simp [wholeLineCauchyHeatGradOp, wholeLineModifiedHeatGradientKernel,
        hzero, deriv_const]
  have hderiv :
      (∫ y : ℝ,
        (wholeLineModifiedHeatThirdKernel t (x - y) -
          wholeLineModifiedHeatGradientKernel t (x - y)) * f y) =
        wholeLineCauchyHeatThirdOp t f x - wholeLineCauchyHeatGradOp t f x := by
    rw [show (fun y : ℝ =>
          (wholeLineModifiedHeatThirdKernel t (x - y) -
            wholeLineModifiedHeatGradientKernel t (x - y)) * f y) =
        fun y : ℝ =>
          wholeLineModifiedHeatThirdKernel t (x - y) * f y -
            wholeLineModifiedHeatGradientKernel t (x - y) * f y by
      funext y
      ring]
    rw [integral_sub hthird_int hgrad_int]
    rw [← wholeLineCauchyHeatThirdOp_eq_modifiedKernel_integral,
      ← wholeLineCauchyHeatGradOp_eq_modifiedKernel_integral ht]
  rw [hfun, ← hderiv]
  exact hraw

/-! ## The terminal diagonal at zero lag

At a point separated from the support of the source, the Gaussian tail beats
every inverse power of the lag.  Thus the value and gradient operators,
totalized by zero for nonpositive lag, have derivative zero at lag zero. -/

theorem heatKernelPointwiseBound_mul_tailGaussianScale
    {t : ℝ} (ht : 0 < t) :
    (1 / Real.sqrt (4 * Real.pi * t)) *
        Real.sqrt (Real.pi / (1 / (16 * t))) = 2 := by
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
  rw [hscale, hden]
  field_simp [hsπ, hst]
  norm_num

theorem heatGradPointwiseBound_mul_tailGaussianScale
    {t : ℝ} (ht : 0 < t) :
    heatGradPointwiseBound t *
        Real.sqrt (Real.pi / (1 / (16 * t))) =
      2 * Real.sqrt 2 / Real.sqrt t := by
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
  have h8 : Real.sqrt (4 * (2 * t)) = 2 * Real.sqrt 2 * Real.sqrt t := by
    rw [show (4 * (2 * t) : ℝ) = (2 : ℝ) ^ 2 * (2 * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  rw [hscale]
  unfold heatGradPointwiseBound
  rw [hden, h8]
  field_simp [ht0, hsπ, hst]
  nlinarith

theorem wholeLineCauchyHeatOp_abs_le_of_zero_ball
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |wholeLineCauchyHeatOp t f x| ≤
      2 * Real.exp (-r ^ 2 / (16 * t)) * M := by
  have hkernel : ∀ z, |wholeLineModifiedHeatKernel t z| ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        Real.exp (-z ^ 2 / (8 * t)) := by
    intro z
    have hexp_time : Real.exp (-t) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
    unfold wholeLineModifiedHeatKernel heatKernel
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (4 * Real.pi * t)),
      abs_of_nonneg (Real.exp_nonneg _)]
    have hexp_space : Real.exp (-z ^ 2 / (4 * t)) ≤
        Real.exp (-z ^ 2 / (8 * t)) := by
      apply Real.exp_le_exp.mpr
      have ht0 : t ≠ 0 := ne_of_gt ht
      rw [show -z ^ 2 / (4 * t) = (-2 * z ^ 2) / (8 * t) by
        field_simp [ht0]
        ring]
      exact (div_le_div_iff_of_pos_right (by positivity : 0 < 8 * t)).2
        (by nlinarith [sq_nonneg z])
    calc
      Real.exp (-t) *
            (1 / Real.sqrt (4 * Real.pi * t) *
              Real.exp (-z ^ 2 / (4 * t))) ≤
          1 * (1 / Real.sqrt (4 * Real.pi * t) *
            Real.exp (-z ^ 2 / (8 * t))) := by
        exact mul_le_mul hexp_time
          (mul_le_mul_of_nonneg_left hexp_space (by positivity))
          (by positivity) (by positivity)
      _ = (1 / Real.sqrt (4 * Real.pi * t)) *
          Real.exp (-z ^ 2 / (8 * t)) := one_mul _
  have hint : Integrable
      (fun y : ℝ => wholeLineModifiedHeatKernel t (x - y) * f y) volume := by
    have hbase :=
      (wholeLineModifiedHeatKernel_integrable ht).comp_neg.comp_add_right (-x)
    have htranslated : Integrable
        (fun y : ℝ => wholeLineModifiedHeatKernel t (x - y)) volume := by
      convert hbase using 1
      ext y
      congr 1
      ring
    exact htranslated.mul_bdd hf_meas
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  have hraw := gaussianTailConvolution_abs_le ht
    (by positivity : 0 ≤ 1 / Real.sqrt (4 * Real.pi * t)) hM hr
    hkernel hf hzero hint
  rw [← wholeLineCauchyHeatOp_eq_modifiedKernel_integral] at hraw
  calc
    |wholeLineCauchyHeatOp t f x| ≤
        ((1 / Real.sqrt (4 * Real.pi * t)) *
          Real.exp (-r ^ 2 / (16 * t)) * M) *
            Real.sqrt (Real.pi / (1 / (16 * t))) := hraw
    _ = 2 * Real.exp (-r ^ 2 / (16 * t)) * M := by
      rw [show
        ((1 / Real.sqrt (4 * Real.pi * t)) *
            Real.exp (-r ^ 2 / (16 * t)) * M) *
              Real.sqrt (Real.pi / (1 / (16 * t))) =
          ((1 / Real.sqrt (4 * Real.pi * t)) *
              Real.sqrt (Real.pi / (1 / (16 * t)))) *
            Real.exp (-r ^ 2 / (16 * t)) * M by ring]
      rw [heatKernelPointwiseBound_mul_tailGaussianScale ht]

theorem wholeLineCauchyHeatGradOp_abs_le_of_zero_ball
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |wholeLineCauchyHeatGradOp t f x| ≤
      (2 * Real.sqrt 2 / Real.sqrt t) *
        Real.exp (-r ^ 2 / (16 * t)) * M := by
  have hkernel : ∀ z, |wholeLineModifiedHeatGradientKernel t z| ≤
      heatGradPointwiseBound t * Real.exp (-z ^ 2 / (8 * t)) := by
    intro z
    have hexp_time : Real.exp (-t) ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
    unfold wholeLineModifiedHeatGradientKernel
    rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      Real.exp (-t) * |deriv (fun w : ℝ => heatKernel t w) z| ≤
          1 * (heatGradPointwiseBound t *
            Real.exp (-z ^ 2 / (8 * t))) := by
        exact mul_le_mul hexp_time
          (by simpa [show 4 * (2 * t) = 8 * t by ring] using
            abs_deriv_heatKernel_le ht z)
          (abs_nonneg _) (by positivity)
      _ = heatGradPointwiseBound t *
          Real.exp (-z ^ 2 / (8 * t)) := one_mul _
  have hint : Integrable
      (fun y : ℝ => wholeLineModifiedHeatGradientKernel t (x - y) * f y) volume := by
    have hbase :=
      (wholeLineModifiedHeatGradientKernel_integrable ht).comp_neg.comp_add_right (-x)
    have htranslated : Integrable
        (fun y : ℝ => wholeLineModifiedHeatGradientKernel t (x - y)) volume := by
      convert hbase using 1
      ext y
      congr 1
      ring
    exact htranslated.mul_bdd hf_meas
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)
  have hraw := gaussianTailConvolution_abs_le ht
    (by unfold heatGradPointwiseBound; positivity) hM hr hkernel hf hzero hint
  rw [← wholeLineCauchyHeatGradOp_eq_modifiedKernel_integral ht] at hraw
  calc
    |wholeLineCauchyHeatGradOp t f x| ≤
        (heatGradPointwiseBound t *
          Real.exp (-r ^ 2 / (16 * t)) * M) *
            Real.sqrt (Real.pi / (1 / (16 * t))) := hraw
    _ = (2 * Real.sqrt 2 / Real.sqrt t) *
          Real.exp (-r ^ 2 / (16 * t)) * M := by
      rw [show
        (heatGradPointwiseBound t *
            Real.exp (-r ^ 2 / (16 * t)) * M) *
              Real.sqrt (Real.pi / (1 / (16 * t))) =
          (heatGradPointwiseBound t *
              Real.sqrt (Real.pi / (1 / (16 * t)))) *
            Real.exp (-r ^ 2 / (16 * t)) * M by ring]
      rw [heatGradPointwiseBound_mul_tailGaussianScale ht]

theorem tendsto_inv_rpow_mul_exp_neg_div_nhdsGT_zero
    (s : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => (1 / t) ^ s * Real.exp (-c / t))
      (𝓝[>] 0) (𝓝 0) := by
  simpa [one_div, div_eq_mul_inv] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s c hc).comp
      tendsto_inv_nhdsGT_zero

/-- The half inverse-time Gaussian tail is uniformly bounded. -/
theorem inv_sqrt_mul_exp_neg_div_le
    {tau c : ℝ} (htau : 0 < tau) (hc : 0 < c) :
    (1 / Real.sqrt tau) * Real.exp (-c / tau) ≤
      (((1 : ℝ) / 2) / Real.exp 1) ^ ((1 : ℝ) / 2) *
        c ^ (-((1 : ℝ) / 2)) := by
  have hpow : (1 / tau) ^ ((1 : ℝ) / 2) = 1 / Real.sqrt tau := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.sqrt_one]
  have h := rpow_mul_exp_neg_mul_le
    (σ := (1 : ℝ) / 2) (by norm_num)
    (lam := 1 / tau) (t := c) (by positivity) hc
  rw [hpow] at h
  simpa [div_eq_mul_inv, mul_comm] using h

/-- The off-support gradient tail is uniform over every positive lag. -/
theorem wholeLineCauchyHeatGradOp_abs_le_of_zero_ball_uniform
    {f : ℝ → ℝ} {t M r x : ℝ}
    (ht : 0 < t) (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    |wholeLineCauchyHeatGradOp t f x| ≤
      2 * Real.sqrt 2 * M *
        ((((1 : ℝ) / 2) / Real.exp 1) ^ ((1 : ℝ) / 2) *
          (r ^ 2 / 16) ^ (-((1 : ℝ) / 2))) := by
  have hc : 0 < r ^ 2 / 16 := by positivity
  have htail := inv_sqrt_mul_exp_neg_div_le ht hc
  have hop := wholeLineCauchyHeatGradOp_abs_le_of_zero_ball
    ht hM hr hf_meas hf hzero
  have hexponent : -r ^ 2 / (16 * t) = -(r ^ 2 / 16) / t := by
    field_simp [ne_of_gt ht]
  calc
    |wholeLineCauchyHeatGradOp t f x| ≤
        (2 * Real.sqrt 2 / Real.sqrt t) *
          Real.exp (-r ^ 2 / (16 * t)) * M := hop
    _ = 2 * Real.sqrt 2 * M *
          ((1 / Real.sqrt t) * Real.exp (-(r ^ 2 / 16) / t)) := by
      rw [hexponent]
      ring
    _ ≤ 2 * Real.sqrt 2 * M *
        ((((1 : ℝ) / 2) / Real.exp 1) ^ ((1 : ℝ) / 2) *
          (r ^ 2 / 16) ^ (-((1 : ℝ) / 2))) := by
      exact mul_le_mul_of_nonneg_left htail (by positivity)

theorem wholeLineCauchyHeatOp_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyHeatOp t f x = 0 := by
  have hzero : (fun z : ℝ => heatKernel t z) = fun _ => 0 := by
    funext z
    exact ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht z
  simp [wholeLineCauchyHeatOp, modifiedSemigroup, heatSemigroup, hzero]

theorem wholeLineCauchyHeatGradOp_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    wholeLineCauchyHeatGradOp t f x = 0 := by
  have hzero : (fun z : ℝ => heatKernel t z) = fun _ => 0 := by
    funext z
    exact ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht z
  simp [wholeLineCauchyHeatGradOp, hzero, deriv_const]

theorem wholeLineCauchyHeatOp_zero_lag_hasDerivAt_of_zero_ball
    {f : ℝ → ℝ} {M r x : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    HasDerivAt (fun t : ℝ => wholeLineCauchyHeatOp t f x) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    symm
    simp [wholeLineCauchyHeatOp_eq_zero_of_nonpos ht.le,
      wholeLineCauchyHeatOp_eq_zero_of_nonpos le_rfl]
  · have hc : 0 < r ^ 2 / 16 := by positivity
    have htail := tendsto_inv_rpow_mul_exp_neg_div_nhdsGT_zero 1 hc
    have hupper : Tendsto
        (fun t : ℝ => (2 * M) *
          ((1 / t) ^ (1 : ℝ) * Real.exp (-(r ^ 2 / 16) / t)))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul htail
    refine squeeze_zero_norm' ?_ hupper
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have hop := wholeLineCauchyHeatOp_abs_le_of_zero_ball
      htpos hM hr hf_meas hf hzero
    have hexponent : -r ^ 2 / (16 * t) = -(r ^ 2 / 16) / t := by
      field_simp [ne_of_gt htpos]
    rw [hexponent] at hop
    rw [wholeLineCauchyHeatOp_eq_zero_of_nonpos le_rfl]
    simp only [zero_add, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos htpos]
    rw [Real.rpow_one]
    calc
      t⁻¹ * |wholeLineCauchyHeatOp t f x| ≤
          t⁻¹ * (2 * Real.exp (-(r ^ 2 / 16) / t) * M) := by
        gcongr
      _ = (2 * M) * ((1 / t) * Real.exp (-(r ^ 2 / 16) / t)) := by ring

theorem wholeLineCauchyHeatGradOp_zero_lag_hasDerivAt_of_zero_ball
    {f : ℝ → ℝ} {M r x : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r)
    (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M)
    (hzero : ∀ y, dist y x < r → f y = 0) :
    HasDerivAt (fun t : ℝ => wholeLineCauchyHeatGradOp t f x) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    symm
    simp [wholeLineCauchyHeatGradOp_eq_zero_of_nonpos ht.le,
      wholeLineCauchyHeatGradOp_eq_zero_of_nonpos le_rfl]
  · have hc : 0 < r ^ 2 / 16 := by positivity
    have htail := tendsto_inv_rpow_mul_exp_neg_div_nhdsGT_zero ((3 : ℝ) / 2) hc
    have hupper : Tendsto
        (fun t : ℝ => (2 * Real.sqrt 2 * M) *
          ((1 / t) ^ ((3 : ℝ) / 2) * Real.exp (-(r ^ 2 / 16) / t)))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul htail
    refine squeeze_zero_norm' ?_ hupper
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have hop := wholeLineCauchyHeatGradOp_abs_le_of_zero_ball
      htpos hM hr hf_meas hf hzero
    have hexponent : -r ^ 2 / (16 * t) = -(r ^ 2 / 16) / t := by
      field_simp [ne_of_gt htpos]
    rw [hexponent] at hop
    have hpow : (1 / t) ^ ((3 : ℝ) / 2) =
        1 / (t * Real.sqrt t) := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]
      rw [Real.sqrt_div (by positivity), Real.sqrt_one]
      field_simp
    rw [wholeLineCauchyHeatGradOp_eq_zero_of_nonpos le_rfl]
    simp only [zero_add, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos htpos]
    rw [hpow]
    calc
      t⁻¹ * |wholeLineCauchyHeatGradOp t f x| ≤
          t⁻¹ *
            ((2 * Real.sqrt 2 / Real.sqrt t) *
              Real.exp (-(r ^ 2 / 16) / t) * M) := by
        gcongr
      _ = (2 * Real.sqrt 2 * M) *
          ((1 / (t * Real.sqrt t)) *
            Real.exp (-(r ^ 2 / 16) / t)) := by
        field_simp [ne_of_gt htpos, ne_of_gt (Real.sqrt_pos.mpr htpos)]

/-! ## Fixed-upper differentiation of a value history -/

/-- A value Duhamel history is time differentiable at a point where its source
vanishes on a product neighborhood.  The moving upper endpoint is replaced by
the fixed endpoint `t + η`; kernels at nonpositive lag are identically zero. -/
theorem wholeLineCauchyValueHistory_time_hasDerivAt_of_local_zero
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M eta r x : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (heta : 0 < eta) (hwindow : 2 * eta < t) (hr : 0 < r)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hzero : ∀ s, dist s t < 2 * eta →
      ∀ y, dist y x < r → (F s).1 y = 0) :
    HasDerivAt (fun q : ℝ => wholeLineCauchyValueHistory F q x)
      (∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatHessOp (t - s) (F s).1 x -
          wholeLineCauchyHeatOp (t - s) (F s).1 x)) t := by
  let b : ℝ := t + eta
  let Cold : ℝ := ((5 * Real.sqrt 2 / 2) * eta ^ (-(1 : ℝ))) * M
  let Crecent : ℝ :=
    5 * M * ((1 / Real.exp 1) * (r ^ 2 / 16)⁻¹)
  let C : ℝ := max Cold Crecent + M
  let G : ℝ → ℝ → ℝ := fun q s =>
    wholeLineCauchyHeatOp (q - s) (F s).1 x
  let G' : ℝ → ℝ → ℝ := fun q s =>
    wholeLineCauchyHeatHessOp (q - s) (F s).1 x -
      wholeLineCauchyHeatOp (q - s) (F s).1 x
  have hbpos : 0 < b := by dsimp [b]; linarith
  have hC0 : 0 ≤ C := by
    dsimp [C, Cold, Crecent]
    positivity
  have hf_bound : ∀ s y, |(F s).1 y| ≤ M := fun s y =>
    (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
  have hG_meas : ∀ q, AEStronglyMeasurable (G q) volume := by
    intro q
    simpa [G] using wholeLineCauchyHeatOp_s_dependent_aestronglyMeasurable hF q x
  have hG'_meas : ∀ q, AEStronglyMeasurable (G' q) volume := by
    intro q
    exact (wholeLineCauchyHeatHessOp_s_dependent_aestronglyMeasurable hF q x).sub
      (wholeLineCauchyHeatOp_s_dependent_aestronglyMeasurable hF q x)
  have hG_int : ∀ q ∈ Metric.ball t (eta / 2),
      IntervalIntegrable (G q) volume 0 b := by
    intro q hq
    apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le hbpos.le (hG_meas q)
    intro s hs
    rw [Real.norm_eq_abs]
    by_cases hlag : 0 ≤ q - s
    · exact wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
        (hf_bound s) hM (F s).1.continuous.aestronglyMeasurable hlag x
    · dsimp [G]
      rw [wholeLineCauchyHeatOp_eq_zero_of_nonpos (le_of_not_ge hlag), abs_zero]
      exact hM
  have hderiv_bound : ∀ s, ∀ q ∈ Metric.ball t (eta / 2),
      ‖G' q s‖ ≤ C := by
    intro s q hq
    have hqt : |q - t| < eta / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hq
    by_cases hlag : 0 < q - s
    · have hqpos : 0 < q - s := hlag
      have hheat := wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
        (hf_bound s) hM (F s).1.continuous.aestronglyMeasurable hqpos.le x
      have hhess : |wholeLineCauchyHeatHessOp (q - s) (F s).1 x| ≤
          max Cold Crecent := by
        by_cases hold : s ≤ t - 2 * eta
        · have hlag_eta : eta ≤ q - s := by
            have hqlo : t - eta / 2 < q := by linarith [(abs_lt.mp hqt).1]
            linarith
          have hinv : (q - s) ^ (-(1 : ℝ)) ≤ eta ^ (-(1 : ℝ)) := by
            rw [Real.rpow_neg_one, Real.rpow_neg_one]
            simpa [one_div] using one_div_le_one_div_of_le heta hlag_eta
          have hglobal := wholeLineCauchyHeatHessOp_abs_le
            (x := x) hqpos hM (F s).1.continuous.aestronglyMeasurable (hf_bound s)
          refine hglobal.trans (le_max_of_le_left ?_)
          dsimp [Cold]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinv (by positivity)) hM
        · have hslo : t - 2 * eta < s := lt_of_not_ge hold
          have hshi : s < t + eta / 2 := by
            have hqhi : q < t + eta / 2 := by linarith [(abs_lt.mp hqt).2]
            linarith
          have hst : dist s t < 2 * eta := by
            rw [Real.dist_eq]
            apply abs_lt.mpr
            constructor <;> linarith
          have hzero_s : ∀ y, dist y x < r → (F s).1 y = 0 := hzero s hst
          have hrecent := wholeLineCauchyHeatHessOp_abs_le_of_zero_ball_uniform
            hqpos hM hr (F s).1.continuous.aestronglyMeasurable
              (hf_bound s) hzero_s
          exact hrecent.trans (le_max_right _ _)
      dsimp [G']
      calc
        |wholeLineCauchyHeatHessOp (q - s) (F s).1 x -
            wholeLineCauchyHeatOp (q - s) (F s).1 x| ≤
            |wholeLineCauchyHeatHessOp (q - s) (F s).1 x| +
              |wholeLineCauchyHeatOp (q - s) (F s).1 x| := abs_sub _ _
        _ ≤ max Cold Crecent + M := add_le_add hhess hheat
        _ = C := rfl
    · have hnonpos : q - s ≤ 0 := le_of_not_gt hlag
      dsimp [G']
      rw [wholeLineCauchyHeatHessOp_eq_zero_of_nonpos hnonpos,
        wholeLineCauchyHeatOp_eq_zero_of_nonpos hnonpos, sub_self, abs_zero]
      exact hC0
  have hdiff : ∀ s, ∀ q ∈ Metric.ball t (eta / 2),
      HasDerivAt (fun w : ℝ => G w s) (G' q s) q := by
    intro s q hq
    by_cases hpos : 0 < q - s
    · have hbase := wholeLineCauchyHeatOp_time_hasDerivAt
        hpos hM (F s).1.continuous.aestronglyMeasurable (hf_bound s) x
      have hlin : HasDerivAt (fun w : ℝ => w - s) 1 q := by
        simpa using (hasDerivAt_id q).sub_const s
      simpa [G, G', Function.comp_def] using hbase.comp q hlin
    · have hnonpos : q - s ≤ 0 := le_of_not_gt hpos
      rcases hnonpos.eq_or_lt with heq | hneg
      · have hqs : q = s := sub_eq_zero.mp heq
        have hqt : dist s t < 2 * eta := by
          rw [← hqs]
          have : dist q t < eta / 2 := by simpa [Metric.mem_ball] using hq
          exact this.trans (by linarith)
        have hzero_s : ∀ y, dist y x < r → (F s).1 y = 0 := hzero s hqt
        have hbase := wholeLineCauchyHeatOp_zero_lag_hasDerivAt_of_zero_ball
          hM hr (F s).1.continuous.aestronglyMeasurable (hf_bound s) hzero_s
        rw [← heq] at hbase
        have hlin : HasDerivAt (fun w : ℝ => w - s) 1 q := by
          simpa using (hasDerivAt_id q).sub_const s
        have hcomp := hbase.comp q hlin
        simpa [G, G', heq,
          wholeLineCauchyHeatHessOp_eq_zero_of_nonpos le_rfl,
          wholeLineCauchyHeatOp_eq_zero_of_nonpos le_rfl,
          Function.comp_def] using hcomp
      · have hqs : q < s := sub_neg.mp hneg
        have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 q := hasDerivAt_const q 0
        have hevent : (fun w : ℝ => G w s) =ᶠ[𝓝 q] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds hqs] with w hw
          simp [G, wholeLineCauchyHeatOp_eq_zero_of_nonpos (sub_nonpos.mpr hw.le)]
        have hz := hconst.congr_of_eventuallyEq hevent
        simpa [G', wholeLineCauchyHeatHessOp_eq_zero_of_nonpos hnonpos,
          wholeLineCauchyHeatOp_eq_zero_of_nonpos hnonpos] using hz
  have hfixed_pair := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := b)
    (F := G) (F' := G') (x₀ := t)
    (s := Metric.ball t (eta / 2)) (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds t (half_pos heta))
    (by filter_upwards with q; exact (hG_meas q).restrict)
    (hG_int t (Metric.mem_ball_self (half_pos heta)))
    (hG'_meas t).restrict
    (by filter_upwards with s hs q hq; exact hderiv_bound s q hq)
    intervalIntegrable_const
    (by filter_upwards with s hs q hq; exact hdiff s q hq)
  have hfixed := hfixed_pair.2
  have hfixed_deriv : (∫ s in (0 : ℝ)..b, G' t s) =
      ∫ s in (0 : ℝ)..t, G' t s := by
    have hleft : IntervalIntegrable (G' t) volume 0 t := by
      apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le
        ht.le (hG'_meas t)
      intro s hs
      exact hderiv_bound s t (Metric.mem_ball_self (half_pos heta))
    have hright : IntervalIntegrable (G' t) volume t b := by
      apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le
        (by dsimp [b]; linarith : t ≤ b) (hG'_meas t)
      intro s hs
      exact hderiv_bound s t (Metric.mem_ball_self (half_pos heta))
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
    have hzero_right : (∫ s in t..b, G' t s) = 0 := by
      calc
        (∫ s in t..b, G' t s) = ∫ _s in t..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le (by dsimp [b]; linarith : t ≤ b)] at hs
          have hnonpos : t - s ≤ 0 := sub_nonpos.mpr hs.1
          simp [G', wholeLineCauchyHeatHessOp_eq_zero_of_nonpos hnonpos,
            wholeLineCauchyHeatOp_eq_zero_of_nonpos hnonpos]
        _ = 0 := intervalIntegral.integral_zero
    rw [hzero_right, add_zero]
  rw [hfixed_deriv] at hfixed
  have hnear_eq :
      (fun q : ℝ => ∫ s in (0 : ℝ)..b, G q s) =ᶠ[𝓝 t]
        fun q : ℝ => wholeLineCauchyValueHistory F q x := by
    filter_upwards [Metric.ball_mem_nhds t (half_pos heta)] with q hq
    have hqt : |q - t| < eta / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hq
    have heta_lt_t : eta < t := by linarith
    have hq0 : 0 < q := by linarith [(abs_lt.mp hqt).1]
    have hqb : q ≤ b := by
      dsimp [b]
      linarith [(abs_lt.mp hqt).2]
    have h0q : IntervalIntegrable (G q) volume 0 q := by
      apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le hq0.le (hG_meas q)
      intro s hs
      rw [Real.norm_eq_abs]
      exact wholeLineCauchyHeatOp_abs_bound_of_nonneg_time
        (hf_bound s) hM (F s).1.continuous.aestronglyMeasurable
          (sub_nonneg.mpr hs.2) x
    have hqb_int : IntervalIntegrable (G q) volume q b := by
      apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le (C := M) hqb (hG_meas q)
      intro s hs
      have hnonpos : q - s ≤ 0 := sub_nonpos.mpr hs.1
      simpa [G, wholeLineCauchyHeatOp_eq_zero_of_nonpos hnonpos] using hM
    rw [← intervalIntegral.integral_add_adjacent_intervals h0q hqb_int]
    have hzero_qb : (∫ s in q..b, G q s) = 0 := by
      calc
        (∫ s in q..b, G q s) = ∫ _s in q..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le hqb] at hs
          exact wholeLineCauchyHeatOp_eq_zero_of_nonpos (sub_nonpos.mpr hs.1) _ _
        _ = 0 := intervalIntegral.integral_zero
    rw [hzero_qb, add_zero]
    rfl
  exact hfixed.congr_of_eventuallyEq hnear_eq.symm

/-! ## Fixed-upper differentiation of a gradient history -/

/-- A gradient Duhamel history is time differentiable at a point where its
source vanishes on a product neighborhood. -/
theorem wholeLineCauchyGradientHistory_time_hasDerivAt_of_local_zero
    {F : ℝ → WholeLineBUC} (hF : Continuous F)
    {t M eta r x : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (heta : 0 < eta) (hwindow : 2 * eta < t) (hr : 0 < r)
    (hFnorm : ∀ s, ‖F s‖ ≤ M)
    (hzero : ∀ s, dist s t < 2 * eta →
      ∀ y, dist y x < r → (F s).1 y = 0) :
    HasDerivAt (fun q : ℝ => wholeLineCauchyGradientHistory F q x)
      (∫ s in (0 : ℝ)..t,
        (wholeLineCauchyHeatThirdOp (t - s) (F s).1 x -
          wholeLineCauchyHeatGradOp (t - s) (F s).1 x)) t := by
  let b : ℝ := t + eta
  let ColdThird : ℝ :=
    (heatThirdTailConstant / (eta * Real.sqrt eta)) * M
  let CrecentThird : ℝ :=
    heatThirdTailConstant * M *
      ((((3 : ℝ) / 2) / Real.exp 1) ^ ((3 : ℝ) / 2) *
        (r ^ 2 / 16) ^ (-((3 : ℝ) / 2)))
  let ColdGrad : ℝ :=
    ((2 / Real.sqrt (4 * Real.pi)) * M) * eta ^ (-(1 / 2 : ℝ))
  let CrecentGrad : ℝ :=
    2 * Real.sqrt 2 * M *
      ((((1 : ℝ) / 2) / Real.exp 1) ^ ((1 : ℝ) / 2) *
        (r ^ 2 / 16) ^ (-((1 : ℝ) / 2)))
  let C : ℝ := max ColdThird CrecentThird + max ColdGrad CrecentGrad
  let G : ℝ → ℝ → ℝ := fun q s =>
    wholeLineCauchyHeatGradOp (q - s) (F s).1 x
  let G' : ℝ → ℝ → ℝ := fun q s =>
    wholeLineCauchyHeatThirdOp (q - s) (F s).1 x -
      wholeLineCauchyHeatGradOp (q - s) (F s).1 x
  have hbpos : 0 < b := by dsimp [b]; linarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    apply add_nonneg
    · apply le_max_of_le_left
      dsimp [ColdThird]
      exact mul_nonneg
        (div_nonneg heatThirdTailConstant_nonneg (by positivity)) hM
    · apply le_max_of_le_left
      dsimp [ColdGrad]
      positivity
  have hf_bound : ∀ s y, |(F s).1 y| ≤ M := fun s y =>
    (WholeLineBUC.abs_apply_le_norm (F s) y).trans (hFnorm s)
  have hG_meas : ∀ q, AEStronglyMeasurable (G q) volume := by
    intro q
    simpa [G] using wholeLineCauchyHeatGradOp_s_dependent_aestronglyMeasurable hF q x
  have hG'_meas : ∀ q, AEStronglyMeasurable (G' q) volume := by
    intro q
    exact (wholeLineCauchyHeatThirdOp_s_dependent_aestronglyMeasurable hF q x).sub
      (wholeLineCauchyHeatGradOp_s_dependent_aestronglyMeasurable hF q x)
  have hG_int : ∀ q ∈ Metric.ball t (eta / 2),
      IntervalIntegrable (G q) volume 0 b := by
    intro q hq
    have hqt : |q - t| < eta / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hq
    have heta_lt_t : eta < t := by linarith
    have hq0 : 0 < q := by linarith [(abs_lt.mp hqt).1]
    have hqb : q ≤ b := by
      dsimp [b]
      linarith [(abs_lt.mp hqt).2]
    have h0q : IntervalIntegrable (G q) volume 0 q := by
      simpa [G] using
        wholeLineCauchyGradientHistory_intervalIntegrable hF hq0 hM hFnorm x
    have hqb_int : IntervalIntegrable (G q) volume q b := by
      apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le (C := 0) hqb (hG_meas q)
      intro s hs
      have hnonpos : q - s ≤ 0 := sub_nonpos.mpr hs.1
      simp [G, wholeLineCauchyHeatGradOp_eq_zero_of_nonpos hnonpos]
    exact h0q.trans hqb_int
  have hderiv_bound : ∀ s, ∀ q ∈ Metric.ball t (eta / 2),
      ‖G' q s‖ ≤ C := by
    intro s q hq
    have hqt : |q - t| < eta / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hq
    by_cases hlag : 0 < q - s
    · have hqpos : 0 < q - s := hlag
      have hthird : |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| ≤
          max ColdThird CrecentThird := by
        by_cases hold : s ≤ t - 2 * eta
        · have hlag_eta : eta ≤ q - s := by
            have hqlo : t - eta / 2 < q := by linarith [(abs_lt.mp hqt).1]
            linarith
          have hsqrt : Real.sqrt eta ≤ Real.sqrt (q - s) :=
            Real.sqrt_le_sqrt hlag_eta
          have hprod : eta * Real.sqrt eta ≤
              (q - s) * Real.sqrt (q - s) :=
            mul_le_mul hlag_eta hsqrt (Real.sqrt_nonneg _) hqpos.le
          have hinv : 1 / ((q - s) * Real.sqrt (q - s)) ≤
              1 / (eta * Real.sqrt eta) :=
            one_div_le_one_div_of_le
              (mul_pos heta (Real.sqrt_pos.mpr heta)) hprod
          have hglobal := wholeLineCauchyHeatThirdOp_abs_le (x := x)
            hqpos hM (F s).1.continuous.aestronglyMeasurable (hf_bound s)
          refine hglobal.trans (le_max_of_le_left ?_)
          dsimp [ColdThird]
          have hcoef := mul_le_mul_of_nonneg_left hinv heatThirdTailConstant_nonneg
          exact mul_le_mul_of_nonneg_right
            (by simpa [div_eq_mul_inv] using hcoef) hM
        · have hslo : t - 2 * eta < s := lt_of_not_ge hold
          have hshi : s < t + eta / 2 := by
            have hqhi : q < t + eta / 2 := by linarith [(abs_lt.mp hqt).2]
            linarith
          have hst : dist s t < 2 * eta := by
            rw [Real.dist_eq]
            apply abs_lt.mpr
            constructor <;> linarith
          have hzero_s : ∀ y, dist y x < r → (F s).1 y = 0 := hzero s hst
          have hrecent := wholeLineCauchyHeatThirdOp_abs_le_of_zero_ball_uniform
            (x := x) hqpos hM hr (F s).1.continuous.aestronglyMeasurable
              (hf_bound s) hzero_s
          exact hrecent.trans (le_max_right _ _)
      have hgrad : |wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤
          max ColdGrad CrecentGrad := by
        by_cases hold : s ≤ t - 2 * eta
        · have hlag_eta : eta ≤ q - s := by
            have hqlo : t - eta / 2 < q := by linarith [(abs_lt.mp hqt).1]
            linarith
          have hinv : (q - s) ^ (-(1 / 2 : ℝ)) ≤
              eta ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos heta hlag_eta (by norm_num)
          have hglobal := wholeLineCauchyHeatGradOp_norm_le_rpow
            hqpos hM (hf_bound s) x
          rw [Real.norm_eq_abs] at hglobal
          refine hglobal.trans (le_max_of_le_left ?_)
          dsimp [ColdGrad]
          exact mul_le_mul_of_nonneg_left hinv (by positivity)
        · have hslo : t - 2 * eta < s := lt_of_not_ge hold
          have hshi : s < t + eta / 2 := by
            have hqhi : q < t + eta / 2 := by linarith [(abs_lt.mp hqt).2]
            linarith
          have hst : dist s t < 2 * eta := by
            rw [Real.dist_eq]
            apply abs_lt.mpr
            constructor <;> linarith
          have hzero_s : ∀ y, dist y x < r → (F s).1 y = 0 := hzero s hst
          have hrecent := wholeLineCauchyHeatGradOp_abs_le_of_zero_ball_uniform
            (x := x) hqpos hM hr (F s).1.continuous.aestronglyMeasurable
              (hf_bound s) hzero_s
          exact hrecent.trans (le_max_right _ _)
      dsimp [G']
      calc
        |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x -
            wholeLineCauchyHeatGradOp (q - s) (F s).1 x| ≤
            |wholeLineCauchyHeatThirdOp (q - s) (F s).1 x| +
              |wholeLineCauchyHeatGradOp (q - s) (F s).1 x| := abs_sub _ _
        _ ≤ max ColdThird CrecentThird + max ColdGrad CrecentGrad :=
          add_le_add hthird hgrad
        _ = C := rfl
    · have hnonpos : q - s ≤ 0 := le_of_not_gt hlag
      dsimp [G']
      rw [wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos hnonpos,
        wholeLineCauchyHeatGradOp_eq_zero_of_nonpos hnonpos, sub_self, abs_zero]
      exact hC0
  have hdiff : ∀ s, ∀ q ∈ Metric.ball t (eta / 2),
      HasDerivAt (fun w : ℝ => G w s) (G' q s) q := by
    intro s q hq
    by_cases hpos : 0 < q - s
    · have hbase := wholeLineCauchyHeatGradOp_time_hasDerivAt
        hpos hM (F s).1.continuous.aestronglyMeasurable (hf_bound s) x
      have hlin : HasDerivAt (fun w : ℝ => w - s) 1 q := by
        simpa using (hasDerivAt_id q).sub_const s
      simpa [G, G', Function.comp_def] using hbase.comp q hlin
    · have hnonpos : q - s ≤ 0 := le_of_not_gt hpos
      rcases hnonpos.eq_or_lt with heq | hneg
      · have hqs : q = s := sub_eq_zero.mp heq
        have hqt : dist s t < 2 * eta := by
          rw [← hqs]
          have : dist q t < eta / 2 := by simpa [Metric.mem_ball] using hq
          exact this.trans (by linarith)
        have hzero_s : ∀ y, dist y x < r → (F s).1 y = 0 := hzero s hqt
        have hbase := wholeLineCauchyHeatGradOp_zero_lag_hasDerivAt_of_zero_ball
          hM hr (F s).1.continuous.aestronglyMeasurable (hf_bound s) hzero_s
        rw [← heq] at hbase
        have hlin : HasDerivAt (fun w : ℝ => w - s) 1 q := by
          simpa using (hasDerivAt_id q).sub_const s
        have hcomp := hbase.comp q hlin
        simpa [G, G', heq,
          wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos le_rfl,
          wholeLineCauchyHeatGradOp_eq_zero_of_nonpos le_rfl,
          Function.comp_def] using hcomp
      · have hqs : q < s := sub_neg.mp hneg
        have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 q := hasDerivAt_const q 0
        have hevent : (fun w : ℝ => G w s) =ᶠ[𝓝 q] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds hqs] with w hw
          simp [G, wholeLineCauchyHeatGradOp_eq_zero_of_nonpos (sub_nonpos.mpr hw.le)]
        have hz := hconst.congr_of_eventuallyEq hevent
        simpa [G', wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos hnonpos,
          wholeLineCauchyHeatGradOp_eq_zero_of_nonpos hnonpos] using hz
  have hfixed_pair := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := b)
    (F := G) (F' := G') (x₀ := t)
    (s := Metric.ball t (eta / 2)) (bound := fun _ : ℝ => C)
    (Metric.ball_mem_nhds t (half_pos heta))
    (by filter_upwards with q; exact (hG_meas q).restrict)
    (hG_int t (Metric.mem_ball_self (half_pos heta)))
    (hG'_meas t).restrict
    (by filter_upwards with s hs q hq; exact hderiv_bound s q hq)
    intervalIntegrable_const
    (by filter_upwards with s hs q hq; exact hdiff s q hq)
  have hfixed := hfixed_pair.2
  have hfixed_deriv : (∫ s in (0 : ℝ)..b, G' t s) =
      ∫ s in (0 : ℝ)..t, G' t s := by
    have hleft : IntervalIntegrable (G' t) volume 0 t := by
      apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le ht.le (hG'_meas t)
      intro s hs
      exact hderiv_bound s t (Metric.mem_ball_self (half_pos heta))
    have hright : IntervalIntegrable (G' t) volume t b := by
      apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le
        (by dsimp [b]; linarith : t ≤ b) (hG'_meas t)
      intro s hs
      exact hderiv_bound s t (Metric.mem_ball_self (half_pos heta))
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright]
    have hzero_right : (∫ s in t..b, G' t s) = 0 := by
      calc
        (∫ s in t..b, G' t s) = ∫ _s in t..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le (by dsimp [b]; linarith : t ≤ b)] at hs
          have hnonpos : t - s ≤ 0 := sub_nonpos.mpr hs.1
          simp [G', wholeLineCauchyHeatThirdOp_eq_zero_of_nonpos hnonpos,
            wholeLineCauchyHeatGradOp_eq_zero_of_nonpos hnonpos]
        _ = 0 := intervalIntegral.integral_zero
    rw [hzero_right, add_zero]
  rw [hfixed_deriv] at hfixed
  have hnear_eq :
      (fun q : ℝ => ∫ s in (0 : ℝ)..b, G q s) =ᶠ[𝓝 t]
        fun q : ℝ => wholeLineCauchyGradientHistory F q x := by
    filter_upwards [Metric.ball_mem_nhds t (half_pos heta)] with q hq
    have hqt : |q - t| < eta / 2 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hq
    have heta_lt_t : eta < t := by linarith
    have hq0 : 0 < q := by linarith [(abs_lt.mp hqt).1]
    have hqb : q ≤ b := by
      dsimp [b]
      linarith [(abs_lt.mp hqt).2]
    have h0q : IntervalIntegrable (G q) volume 0 q := by
      simpa [G] using
        wholeLineCauchyGradientHistory_intervalIntegrable hF hq0 hM hFnorm x
    have hqb_int : IntervalIntegrable (G q) volume q b := by
      apply intervalIntegrable_of_aestronglyMeasurable_of_norm_le (C := 0) hqb (hG_meas q)
      intro s hs
      have hnonpos : q - s ≤ 0 := sub_nonpos.mpr hs.1
      simp [G, wholeLineCauchyHeatGradOp_eq_zero_of_nonpos hnonpos]
    rw [← intervalIntegral.integral_add_adjacent_intervals h0q hqb_int]
    have hzero_qb : (∫ s in q..b, G q s) = 0 := by
      calc
        (∫ s in q..b, G q s) = ∫ _s in q..b, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le hqb] at hs
          exact wholeLineCauchyHeatGradOp_eq_zero_of_nonpos (sub_nonpos.mpr hs.1) _ _
        _ = 0 := intervalIntegral.integral_zero
    rw [hzero_qb, add_zero]
    rfl
  exact hfixed.congr_of_eventuallyEq hnear_eq.symm

/-! ## Actual clamped-source time derivatives at a negative point -/

/-- An interior strict-negative point supplies a real-time product
neighborhood on which both totalized clamped sources vanish. -/
theorem wholeLineCauchy_sourceTrajectories_real_zero_near_negative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ)
    (ht : 0 < z.1) (htop : z.1 < T) (hneg : (U z).1 x < 0) :
    ∃ eta > 0, 2 * eta < z.1 ∧ ∃ r > 0,
      ∀ s, dist s z.1 < 2 * eta → ∀ y, dist y x < r →
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 y = 0 ∧
        (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 y = 0 := by
  rcases wholeLineCauchy_sourceTrajectories_zero_near_negative
      p hM hT U z x hneg with ⟨eps, heps, hzero⟩
  let eta : ℝ := min (eps / 4) (min (z.1 / 4) ((T - z.1) / 4))
  have heta : 0 < eta := by
    dsimp [eta]
    apply lt_min
    · exact div_pos heps (by norm_num)
    · apply lt_min
      · exact div_pos ht (by norm_num)
      · exact div_pos (sub_pos.mpr htop) (by norm_num)
  have heta_eps : eta ≤ eps / 4 := by
    dsimp [eta]
    exact min_le_left _ _
  have heta_time : eta ≤ z.1 / 4 := by
    dsimp [eta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have heta_top : eta ≤ (T - z.1) / 4 := by
    dsimp [eta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hwindow : 2 * eta < z.1 := by linarith
  refine ⟨eta, heta, hwindow, eps, heps, ?_⟩
  intro s hs y hy
  have hsabs : |s - z.1| < 2 * eta := by
    simpa [Real.dist_eq] using hs
  have hs0 : 0 ≤ s := by
    have hslo := (abs_lt.mp hsabs).1
    linarith
  have hsT : s ≤ T := by
    have hshi := (abs_lt.mp hsabs).2
    linarith
  let w : Set.Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
  have hw : dist w z < eps := by
    change dist s z.1 < eps
    exact hs.trans (by linarith)
  exact hzero w y hw hy

/-- The actual clamped chemotaxis history has its time derivative at every
interior strict-negative point. -/
theorem wholeLineCauchyFluxGradientHistory_time_hasDerivAt_at_negative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ)
    (ht : 0 < z.1) (htop : z.1 < T) (hneg : (U z).1 x < 0) :
    HasDerivAt
      (fun q : ℝ => wholeLineCauchyGradientHistory
        (wholeLineCauchyFluxSourceTrajectory p hM hT U) q x)
      (∫ s in (0 : ℝ)..z.1,
        (wholeLineCauchyHeatThirdOp (z.1 - s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 x -
          wholeLineCauchyHeatGradOp (z.1 - s)
            (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 x)) z.1 := by
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
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
  rcases wholeLineCauchy_sourceTrajectories_real_zero_near_negative
      p hM hT U z x ht htop hneg with
    ⟨eta, heta, hwindow, r, hr, hzero⟩
  change HasDerivAt (fun q : ℝ => wholeLineCauchyGradientHistory F q x) _ z.1
  apply wholeLineCauchyGradientHistory_time_hasDerivAt_of_local_zero
    hFcont ht hMF heta hwindow hr hFnorm
  intro s hs y hy
  exact (hzero s hs y hy).1

/-- The actual clamped reaction history has its time derivative at every
interior strict-negative point. -/
theorem wholeLineCauchyReactionValueHistory_time_hasDerivAt_at_negative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ)
    (ht : 0 < z.1) (htop : z.1 < T) (hneg : (U z).1 x < 0) :
    HasDerivAt
      (fun q : ℝ => wholeLineCauchyValueHistory
        (wholeLineCauchyReactionSourceTrajectory p hM hT U) q x)
      (∫ s in (0 : ℝ)..z.1,
        (wholeLineCauchyHeatHessOp (z.1 - s)
            (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 x -
          wholeLineCauchyHeatOp (z.1 - s)
            (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 x)) z.1 := by
  let F : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  let MR : ℝ := M + M * (1 + M ^ p.α)
  have hMR : 0 ≤ MR := by
    dsimp [MR]
    exact add_nonneg hM
      (mul_nonneg hM (add_nonneg zero_le_one (Real.rpow_nonneg hM _)))
  have hFcont : Continuous F := by
    simpa [F] using wholeLineCauchyReactionSourceTrajectory_continuous p hM hT U
  have hFnorm : ∀ s, ‖F s‖ ≤ MR := by
    intro s
    simpa [F, MR, wholeLineCauchyReactionSourceTrajectory] using
      wholeLineCauchyTruncatedReactionBUC_norm_le p hM
        (wholeLineBUCTrajectoryExtend hT U s)
  rcases wholeLineCauchy_sourceTrajectories_real_zero_near_negative
      p hM hT U z x ht htop hneg with
    ⟨eta, heta, hwindow, r, hr, hzero⟩
  change HasDerivAt (fun q : ℝ => wholeLineCauchyValueHistory F q x) _ z.1
  apply wholeLineCauchyValueHistory_time_hasDerivAt_of_local_zero
    hFcont ht hMR heta hwindow hr hFnorm
  intro s hs y hy
  exact (hzero s hs y hy).2

/-! ## Scalar-history form of the canonical fixed-point identity -/

theorem wholeLineCauchyGradientBUCIntegrand_apply_eq_of_lt
    (p : CMParams) {M T t s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hs : s < t) (x : ℝ) :
    (wholeLineCauchyGradientBUCIntegrand p hM hT U t s).1 x =
      wholeLineCauchyHeatGradOp (t - s)
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 x := by
  have hlag : 0 < t - s := sub_pos.mpr hs
  simp [wholeLineCauchyGradientBUCIntegrand,
    wholeLineCauchyHeatGradientBUCTotal, hlag]

theorem wholeLineCauchyValueBUCIntegrand_apply_eq_of_lt
    (p : CMParams) {M T t s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (hs : s < t) (x : ℝ) :
    (wholeLineCauchyValueBUCIntegrand p hM hT U t s).1 x =
      wholeLineCauchyHeatOp (t - s)
        (wholeLineCauchyReactionSourceTrajectory p hM hT U s).1 x := by
  have hlag : 0 < t - s := sub_pos.mpr hs
  simp [wholeLineCauchyValueBUCIntegrand, wholeLineCauchyHeatBUCTotal, hlag]

/-- The canonical BUC fixed-point equation written in the exact scalar-history
form consumed by the time and spatial derivative capstones. -/
theorem wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) (ht : 0 < z.1) :
    (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x =
      wholeLineCauchyHeatOp z.1 u₀.1 x +
        (-p.χ) * wholeLineCauchyGradientHistory
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall)) z.1 x +
        wholeLineCauchyValueHistory
          (wholeLineCauchyReactionSourceTrajectory p hM hT
            (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall)) z.1 x := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  have hgrad :
      (∫ s in (0 : ℝ)..z.1,
        (wholeLineCauchyGradientBUCIntegrand p hM hT U z.1 s).1 x) =
      wholeLineCauchyGradientHistory
        (wholeLineCauchyFluxSourceTrajectory p hM hT U) z.1 x := by
    unfold wholeLineCauchyGradientHistory
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume z.1] with s hne hs
    rw [Set.uIoc_of_le ht.le] at hs
    exact wholeLineCauchyGradientBUCIntegrand_apply_eq_of_lt
      p hM hT U (lt_of_le_of_ne hs.2 hne) x
  have hvalue :
      (∫ s in (0 : ℝ)..z.1,
        (wholeLineCauchyValueBUCIntegrand p hM hT U z.1 s).1 x) =
      wholeLineCauchyValueHistory
        (wholeLineCauchyReactionSourceTrajectory p hM hT U) z.1 x := by
    unfold wholeLineCauchyValueHistory
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume z.1] with s hne hs
    rw [Set.uIoc_of_le ht.le] at hs
    exact wholeLineCauchyValueBUCIntegrand_apply_eq_of_lt
      p hM hT U (lt_of_le_of_ne hs.2 hne) x
  have hfix := wholeLineCauchyBUCMildFixedPoint_apply_eq_integrals
    p hM hT u₀ hsmall z x
  change (U z).1 x = _ at hfix ⊢
  rw [show (wholeLineCauchyHeatBUCTotal z.1 u₀).1 x =
      wholeLineCauchyHeatOp z.1 u₀.1 x by
        simp [wholeLineCauchyHeatBUCTotal, ht], hgrad, hvalue] at hfix
  exact hfix

/-- Time derivative of the canonical clamped fixed point at an interior
strict-negative point, in generator form. -/
theorem wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_at_negative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ)
    (ht : 0 < z.1) (htop : z.1 < T)
    (hneg : (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x < 0) :
    HasDerivAt
      (fun q : ℝ =>
        (wholeLineBUCTrajectoryExtend hT
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) q).1 x)
      ((wholeLineCauchyHeatHessOp z.1 u₀.1 x -
          wholeLineCauchyHeatOp z.1 u₀.1 x) +
        (-p.χ) * (∫ s in (0 : ℝ)..z.1,
          (wholeLineCauchyHeatThirdOp (z.1 - s)
              (wholeLineCauchyFluxSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x -
            wholeLineCauchyHeatGradOp (z.1 - s)
              (wholeLineCauchyFluxSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x)) +
        (∫ s in (0 : ℝ)..z.1,
          (wholeLineCauchyHeatHessOp (z.1 - s)
              (wholeLineCauchyReactionSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x -
            wholeLineCauchyHeatOp (z.1 - s)
              (wholeLineCauchyReactionSourceTrajectory p hM hT
                (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) s).1 x))) z.1 := by
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  have hu₀bound : ∀ y, |u₀.1 y| ≤ ‖u₀‖ := fun y =>
    WholeLineBUC.abs_apply_le_norm u₀ y
  have hheat := wholeLineCauchyHeatOp_time_hasDerivAt
    ht (norm_nonneg u₀) u₀.1.continuous.aestronglyMeasurable hu₀bound x
  have hflux := wholeLineCauchyFluxGradientHistory_time_hasDerivAt_at_negative
    p hM hT U z x ht htop hneg
  have hreaction := wholeLineCauchyReactionValueHistory_time_hasDerivAt_at_negative
    p hM hT U z x ht htop hneg
  have hrhs := (hheat.add (hflux.const_mul (-p.χ))).add hreaction
  have hevent :
      (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x) =ᶠ[𝓝 z.1]
        (fun q : ℝ => wholeLineCauchyHeatOp q u₀.1 x +
          (-p.χ) * wholeLineCauchyGradientHistory F q x +
          wholeLineCauchyValueHistory R q x) := by
    filter_upwards [Ioo_mem_nhds ht htop] with q hq
    let w : Set.Icc (0 : ℝ) T := ⟨q, hq.1.le, hq.2.le⟩
    rw [wholeLineBUCTrajectoryExtend_eq hT U w.2]
    simpa [U, F, R, w] using
      wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
        p hM hT u₀ hsmall w x hq.1
  change HasDerivAt (fun q : ℝ => (wholeLineBUCTrajectoryExtend hT U q).1 x) _ z.1
  exact hrhs.congr_of_eventuallyEq hevent

#print axioms wholeLineCauchyHeatOp_time_hasDerivAt
#print axioms wholeLineCauchyHeatGradOp_time_hasDerivAt
#print axioms wholeLineCauchyHeatOp_zero_lag_hasDerivAt_of_zero_ball
#print axioms wholeLineCauchyHeatGradOp_zero_lag_hasDerivAt_of_zero_ball
#print axioms wholeLineCauchyValueHistory_time_hasDerivAt_of_local_zero
#print axioms wholeLineCauchyGradientHistory_time_hasDerivAt_of_local_zero
#print axioms wholeLineCauchyFluxGradientHistory_time_hasDerivAt_at_negative
#print axioms wholeLineCauchyReactionValueHistory_time_hasDerivAt_at_negative
#print axioms wholeLineCauchyBUCMildFixedPoint_apply_eq_histories
#print axioms wholeLineCauchyBUCMildFixedPoint_time_hasDerivAt_at_negative

end ShenWork.Paper1
