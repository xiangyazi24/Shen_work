import ShenWork.PaperOne.WholeLineHeatGenerator
import ShenWork.PDE.IntervalFullKernelSecondDerivLinfty

open MeasureTheory Filter Topology Real Set
open scoped Topology

noncomputable section

namespace ShenWork.PaperOne

namespace ConvLeibniz

open ShenWork.IntervalNeumannFullKernel

lemma integrable_exp_neg_mul_sq_shift {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-b * (x - y) ^ 2)) volume := by
  have hshift :
      Integrable (fun y : ℝ => Real.exp (-b * (y + -x) ^ 2)) volume :=
    (integrable_exp_neg_mul_sq hb).comp_add_right (-x)
  convert hshift using 1
  ext y
  congr 1
  ring

lemma integrable_heatGradWindowBound_shift {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable
      (fun y : ℝ => heatGradWindowBound t (x - y) 1 (0 : ℤ)) volume := by
  have hb : 0 < 1 / (4 * (4 * t)) := by positivity
  have hbase := integrable_exp_neg_mul_sq_shift hb x
  convert
    hbase.const_mul
      (heatGradPointwiseBound t * Real.exp ((1 : ℝ) ^ 2 / (4 * (2 * t))))
    using 1
  ext y
  unfold heatGradWindowBound
  simp only [Int.cast_zero, mul_zero, add_zero, one_pow]
  rw [show -((x - y) ^ 2) / (4 * (4 * t)) =
      -(1 / (4 * (4 * t))) * (x - y) ^ 2 by
    field_simp]

lemma integrable_heatHessWindowBound_shift {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable
      (fun y : ℝ => heatHessWindowBound t (x - y) 1 (0 : ℤ)) volume := by
  have hb : 0 < 1 / (4 * (4 * t)) := by positivity
  have hbase := integrable_exp_neg_mul_sq_shift hb x
  convert
    hbase.const_mul
      (heatHessPointwiseBound t * Real.exp ((1 : ℝ) ^ 2 / (4 * (2 * t))))
    using 1
  ext y
  unfold heatHessWindowBound
  simp only [Int.cast_zero, mul_zero, add_zero, one_pow]
  rw [show -((x - y) ^ 2) / (4 * (4 * t)) =
      -(1 / (4 * (4 * t))) * (x - y) ^ 2 by
    field_simp]

lemma secondDeriv_heatKernel_translated_integrable {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    Integrable
      (fun y : ℝ =>
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y))
      volume := by
  have habs :
      Integrable
        (fun y : ℝ =>
          |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y)|)
        volume := by
    simpa [sub_eq_add_neg, add_comm] using
      ((secondDeriv_heatKernel_abs_integrable ht).comp_neg.comp_add_right (-x))
  have hmeas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y))
        volume :=
    ((continuous_secondDeriv_heatKernel ht).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact (integrable_norm_iff hmeas).mp (by
    simpa [Real.norm_eq_abs] using habs)

lemma secondDeriv_heatKernel_mul_bounded_integrable {t M : ℝ}
    (ht : 0 < t) {f : ℝ → ℝ} (x : ℝ)
    (hf : ∀ y, |f y| ≤ M) (hf_meas : AEStronglyMeasurable f volume) :
    Integrable
      (fun y : ℝ =>
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y) *
          f y) volume :=
  (secondDeriv_heatKernel_translated_integrable ht x).mul_bdd hf_meas
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hf y)

lemma abs_secondDeriv_heatKernel_local_time_le {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Metric.ball t (t / 2)) (w : ℝ) :
    |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel s z) u) w| ≤
      (5 * ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)))) *
        Real.exp (-(1 / (12 * t)) * w ^ 2) := by
  have hdist := Metric.mem_ball.mp hs
  rw [Real.dist_eq] at hdist
  have hlow : t / 2 < s := by
    have hlt := (abs_lt.mp hdist).1
    linarith
  have hup_s : s < 3 * t / 2 := by
    have hlt := (abs_lt.mp hdist).2
    linarith
  have hspos : 0 < s := by linarith
  have hbase := abs_secondDeriv_heatKernel_le hspos w
  have hcoeff :
      heatHessPointwiseBound s ≤
        5 * ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t))) := by
    have ht_le_two_s : t ≤ 2 * s := by linarith
    have h1 : 1 / (2 * s) ≤ 1 / t :=
      one_div_le_one_div_of_le ht ht_le_two_s
    have hsqrt_le :
        Real.sqrt (2 * Real.pi * t) ≤ Real.sqrt (4 * Real.pi * s) := by
      apply Real.sqrt_le_sqrt
      nlinarith [Real.pi_pos, ht_le_two_s]
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
    have h2 : 1 / Real.sqrt (4 * Real.pi * s) ≤
        1 / Real.sqrt (2 * Real.pi * t) :=
      one_div_le_one_div_of_le hsqrt_pos hsqrt_le
    have hprod :
        (1 / (2 * s)) * (1 / Real.sqrt (4 * Real.pi * s)) ≤
          (1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    unfold heatHessPointwiseBound
    nlinarith
  have hexp :
      Real.exp (-w ^ 2 / (4 * (2 * s))) ≤
        Real.exp (-(1 / (12 * t)) * w ^ 2) := by
    have hden_le : 4 * (2 * s) ≤ 12 * t := by nlinarith
    have hden_pos : 0 < 4 * (2 * s) := by positivity
    have hinv : 1 / (12 * t) ≤ 1 / (4 * (2 * s)) :=
      one_div_le_one_div_of_le hden_pos hden_le
    have hmul :=
      mul_le_mul_of_nonneg_right hinv (sq_nonneg w)
    apply Real.exp_le_exp.mpr
    have hneg := neg_le_neg hmul
    convert hneg using 1
    · field_simp [ne_of_gt hspos]
    · ring
  exact hbase.trans
    (mul_le_mul hcoeff hexp (Real.exp_nonneg _)
      (by positivity : 0 ≤ 5 * ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)))))

theorem heatConvolution_space_deriv {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun z : ℝ => heatSemigroup t f z)
      (∫ y : ℝ, deriv (fun w : ℝ => heatKernel t (w - y)) x * f y) x := by
  let F : ℝ → ℝ → ℝ := fun z y => heatKernel t (z - y) * f y
  let F' : ℝ → ℝ → ℝ :=
    fun z y => deriv (fun w : ℝ => heatKernel t (w - y)) z * f y
  let bound : ℝ → ℝ := fun y =>
    heatGradWindowBound t (x - y) 1 (0 : ℤ) * M
  have hs : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x one_pos
  have hF_meas :
      ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) volume := by
    filter_upwards with z
    exact (heatKernel_mul_bounded_integrable ht z hf hf_meas).aestronglyMeasurable
  have hF_int : Integrable (F x) volume := by
    exact heatKernel_mul_bounded_integrable ht x hf hf_meas
  have hF'_meas : AEStronglyMeasurable (F' x) volume := by
    exact (heatKernel_deriv_mul_bounded_integrable ht x hf hf_meas).aestronglyMeasurable
  have h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball x 1, ‖F' z y‖ ≤ bound y := by
    filter_upwards with y z hz
    have hz1 :
        |z - y - ((x - y) + 2 * ((0 : ℤ) : ℝ))| ≤ 1 := by
      rw [show z - y - ((x - y) + 2 * ((0 : ℤ) : ℝ)) = z - x by norm_num]
      rw [← Real.dist_eq]
      exact le_of_lt (Metric.mem_ball.mp hz)
    have hker :=
      abs_deriv_heatKernel_le_windowShift
        (t := t) ht (x - y) 1 (0 : ℤ) (w := z - y) hz1
    have hker' :
        |deriv (fun w : ℝ => heatKernel t (w - y)) z| ≤
          heatGradWindowBound t (x - y) 1 (0 : ℤ) := by
      rw [deriv_heatKernel_translated_left ht z y]
      simpa [deriv_heatKernel ht (z - y)] using hker
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hker' (hf y) (abs_nonneg _) (by
      unfold heatGradWindowBound heatGradPointwiseBound
      positivity)
  have hbound_int : Integrable bound volume := by
    dsimp [bound]
    exact (integrable_heatGradWindowBound_shift ht x).mul_const M
  have h_diff :
      ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball x 1,
        HasDerivAt (fun z' : ℝ => F z' y) (F' z y) z := by
    filter_upwards with y z _hz
    dsimp [F, F']
    convert (heatKernel_translated_hasDerivAt_left ht z y).mul_const (f y) using 1
    rw [deriv_heatKernel_translated_left ht z y]
  simpa [heatSemigroup, F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := bound) (F := F) (F' := F')
      (x₀ := x) (s := Metric.ball x 1)
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

theorem heatConvolution_space_second_deriv {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun z : ℝ => deriv (fun w : ℝ => heatSemigroup t f w) z)
      (∫ y : ℝ,
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y) *
          f y) x := by
  have hFeq :
      (fun z : ℝ => deriv (fun w : ℝ => heatSemigroup t f w) z) =
        fun z : ℝ =>
          ∫ y : ℝ, deriv (fun w : ℝ => heatKernel t (w - y)) z * f y := by
    funext z
    exact (heatConvolution_space_deriv
      (f := f) (t := t) (x := z) (M := M) ht hf_meas hf).deriv
  rw [hFeq]
  let F : ℝ → ℝ → ℝ :=
    fun z y => deriv (fun w : ℝ => heatKernel t (w - y)) z * f y
  let F' : ℝ → ℝ → ℝ :=
    fun z y =>
      deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (z - y) *
        f y
  let bound : ℝ → ℝ := fun y =>
    heatHessWindowBound t (x - y) 1 (0 : ℤ) * M
  have hs : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x one_pos
  have hF_meas :
      ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) volume := by
    filter_upwards with z
    exact (heatKernel_deriv_mul_bounded_integrable ht z hf hf_meas).aestronglyMeasurable
  have hF_int : Integrable (F x) volume := by
    exact heatKernel_deriv_mul_bounded_integrable ht x hf hf_meas
  have hF'_meas : AEStronglyMeasurable (F' x) volume := by
    exact (secondDeriv_heatKernel_mul_bounded_integrable ht x hf hf_meas).aestronglyMeasurable
  have h_bound :
      ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball x 1, ‖F' z y‖ ≤ bound y := by
    filter_upwards with y z hz
    have hz1 :
        |z - y - ((x - y) + 2 * ((0 : ℤ) : ℝ))| ≤ 1 := by
      rw [show z - y - ((x - y) + 2 * ((0 : ℤ) : ℝ)) = z - x by norm_num]
      rw [← Real.dist_eq]
      exact le_of_lt (Metric.mem_ball.mp hz)
    have hker :=
      abs_secondDeriv_heatKernel_le_windowShift
        (t := t) ht (x - y) 1 (0 : ℤ) (w := z - y) hz1
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hker (hf y) (abs_nonneg _) (by
      unfold heatHessWindowBound heatHessPointwiseBound
      positivity)
  have hbound_int : Integrable bound volume := by
    dsimp [bound]
    exact (integrable_heatHessWindowBound_shift ht x).mul_const M
  have h_diff :
      ∀ᵐ y ∂volume, ∀ z ∈ Metric.ball x 1,
        HasDerivAt (fun z' : ℝ => F z' y) (F' z y) z := by
    filter_upwards with y z _hz
    dsimp [F, F']
    have hfun :
        (fun z' : ℝ => deriv (fun w : ℝ => heatKernel t (w - y)) z') =
          fun z' : ℝ => deriv (fun u : ℝ => heatKernel t u) (z' - y) := by
      funext z'
      rw [deriv_heatKernel_translated_left ht z' y, deriv_heatKernel ht (z' - y)]
    have hinner : HasDerivAt (fun z' : ℝ => z' - y) 1 z := by
      simpa [sub_eq_add_neg] using (hasDerivAt_id z).add_const (-y)
    have hmain :=
      ((heatKernel_secondDeriv_hasDerivAt ht (z - y)).comp z hinner).mul_const (f y)
    simpa [hfun, deriv_deriv_heatKernel ht (z - y)] using hmain
  simpa [F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := bound) (F := F) (F' := F')
      (x₀ := x) (s := Metric.ball x 1)
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

theorem heatConvolution_time_hasDerivAt {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun s : ℝ => heatSemigroup s f x)
      (∫ y : ℝ,
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y) *
          f y) t := by
  let F : ℝ → ℝ → ℝ := fun s y => heatKernel s (x - y) * f y
  let F' : ℝ → ℝ → ℝ :=
    fun s y =>
      deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel s z) u) (x - y) *
        f y
  let C : ℝ := 5 * ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)))
  let bound : ℝ → ℝ := fun y =>
    (C * M) * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)
  have hM : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hf 0)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hs : Metric.ball t (t / 2) ∈ 𝓝 t :=
    Metric.ball_mem_nhds t (half_pos ht)
  have hF_meas :
      ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) volume := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hspos
    exact (heatKernel_mul_bounded_integrable hspos x hf hf_meas).aestronglyMeasurable
  have hF_int : Integrable (F t) volume := by
    exact heatKernel_mul_bounded_integrable ht x hf hf_meas
  have hF'_meas : AEStronglyMeasurable (F' t) volume := by
    exact (secondDeriv_heatKernel_mul_bounded_integrable ht x hf hf_meas).aestronglyMeasurable
  have h_bound :
      ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball t (t / 2), ‖F' s y‖ ≤ bound y := by
    filter_upwards with y s hsball
    have hker := abs_secondDeriv_heatKernel_local_time_le ht hsball (x - y)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel s z) u) (x - y)| *
          |f y|
          ≤ (C * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2)) * M := by
            exact mul_le_mul hker (hf y) (abs_nonneg _)
              (mul_nonneg hC_nonneg (Real.exp_nonneg _))
      _ = (C * M) * Real.exp (-(1 / (12 * t)) * (x - y) ^ 2) := by ring
  have hbound_int : Integrable bound volume := by
    have hb : 0 < 1 / (12 * t) := by positivity
    dsimp [bound]
    exact (integrable_exp_neg_mul_sq_shift hb x).const_mul (C * M)
  have h_diff :
      ∀ᵐ y ∂volume, ∀ s ∈ Metric.ball t (t / 2),
        HasDerivAt (fun r : ℝ => F r y) (F' s y) s := by
    filter_upwards with y s hsball
    have hdist := Metric.mem_ball.mp hsball
    rw [Real.dist_eq] at hdist
    have hspos : 0 < s := by
      have hlt := (abs_lt.mp hdist).1
      linarith [ht]
    dsimp [F, F']
    have hmain := (heatKernel_time_hasDerivAt hspos (x - y)).mul_const (f y)
    convert hmain using 1
    rw [heatKernel_second_spatial_deriv hspos (x - y)]
  simpa [heatSemigroup, F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := bound) (F := F) (F' := F')
      (x₀ := t) (s := Metric.ball t (t / 2))
      hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

theorem heatSemigroupGeneratorConvolutionFrontier_of_bounded
    {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HeatSemigroupGeneratorConvolutionFrontier f t x := by
  unfold HeatSemigroupGeneratorConvolutionFrontier
  have htime :=
    heatConvolution_time_hasDerivAt
      (f := f) (t := t) (x := x) (M := M) ht hf_meas hf
  have hspace :=
    heatConvolution_space_second_deriv
      (f := f) (t := t) (x := x) (M := M) ht hf_meas hf
  convert htime using 1
  exact hspace.deriv

theorem wholeLineHeatOp_time_hasDerivAt_of_bounded
    {f : ℝ → ℝ} {t x M : ℝ}
    (ht : 0 < t) (hf_meas : AEStronglyMeasurable f volume)
    (hf : ∀ y, |f y| ≤ M) :
    HasDerivAt (fun s : ℝ => wholeLineHeatOp s f x)
      (deriv (deriv (fun z : ℝ => wholeLineHeatOp t f z)) x -
        wholeLineHeatOp t f x) t := by
  exact wholeLineHeatOp_time_hasDerivAt_of_convolution_frontier
    (f := f) (t := t) (x := x)
    (heatSemigroupGeneratorConvolutionFrontier_of_bounded
      (f := f) (t := t) (x := x) (M := M) ht hf_meas hf)

#print axioms heatConvolution_space_deriv
#print axioms heatConvolution_space_second_deriv
#print axioms heatConvolution_time_hasDerivAt
#print axioms heatSemigroupGeneratorConvolutionFrontier_of_bounded
#print axioms wholeLineHeatOp_time_hasDerivAt_of_bounded

end ConvLeibniz

end ShenWork.PaperOne
