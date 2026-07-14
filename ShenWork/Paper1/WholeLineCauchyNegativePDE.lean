import ShenWork.Paper1.WholeLineCauchyBUCOffSupport

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

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

#print axioms wholeLineCauchyHeatOp_time_hasDerivAt
#print axioms wholeLineCauchyHeatGradOp_time_hasDerivAt

end ShenWork.Paper1
