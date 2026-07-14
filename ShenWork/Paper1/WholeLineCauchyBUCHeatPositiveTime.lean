import ShenWork.Paper1.WholeLineCauchyBUCHeatContinuity
import ShenWork.PDE.IntervalNeumannFullKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction
open ShenWork.IntervalNeumannFullKernel

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time continuity of the whole-line Gaussian BUC operators

Local Gaussian majorants give `L¹` continuity in the time parameter for both
the modified value kernel and its spatial derivative.  The convolution
kernel-difference estimate then promotes this to strong BUC continuity.
-/

theorem wholeLineModifiedHeatKernel_continuousAt_time
    {t : ℝ} (ht : 0 < t) (z : ℝ) :
    ContinuousAt (fun s : ℝ => wholeLineModifiedHeatKernel s z) t := by
  have hsqrt : Real.sqrt (4 * Real.pi * t) ≠ 0 := by positivity
  unfold wholeLineModifiedHeatKernel heatKernel
  fun_prop (disch := positivity)

theorem wholeLineModifiedHeatGradientKernel_continuousAt_time
    {t : ℝ} (ht : 0 < t) (z : ℝ) :
    ContinuousAt (fun s : ℝ => wholeLineModifiedHeatGradientKernel s z) t := by
  let F : ℝ → ℝ := fun s =>
    Real.exp (-s) * (-(z / (2 * s)) * heatKernel s z)
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hsqrt : Real.sqrt (4 * Real.pi * t) ≠ 0 := by positivity
  have hF : ContinuousAt F t := by
    dsimp [F, heatKernel]
    fun_prop (disch := positivity)
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [F, wholeLineModifiedHeatGradientKernel, deriv_heatKernel hs z]

theorem abs_wholeLineModifiedHeatKernel_local_time_le
    {t s : ℝ} (ht : 0 < t) (hs : s ∈ Metric.ball t (t / 2)) (z : ℝ) :
    |wholeLineModifiedHeatKernel s z| ≤
      (1 / Real.sqrt (2 * Real.pi * t)) *
        Real.exp (-(1 / (6 * t)) * z ^ 2) := by
  have hdist := Metric.mem_ball.mp hs
  rw [Real.dist_eq] at hdist
  have hlow : t / 2 < s := by
    linarith [(abs_lt.mp hdist).1]
  have hup : s < 3 * t / 2 := by
    linarith [(abs_lt.mp hdist).2]
  have hspos : 0 < s := by linarith
  have hsqrt_le :
      Real.sqrt (2 * Real.pi * t) ≤ Real.sqrt (4 * Real.pi * s) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  have hpref : 1 / Real.sqrt (4 * Real.pi * s) ≤
      1 / Real.sqrt (2 * Real.pi * t) :=
    one_div_le_one_div_of_le (by positivity) hsqrt_le
  have hexp_time : Real.exp (-s) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (by linarith : -s ≤ 0)
  have hden_le : 4 * s ≤ 6 * t := by linarith
  have hinv : 1 / (6 * t) ≤ 1 / (4 * s) :=
    one_div_le_one_div_of_le (by positivity) hden_le
  have hexp_space : Real.exp (-z ^ 2 / (4 * s)) ≤
      Real.exp (-(1 / (6 * t)) * z ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hinv (sq_nonneg z)
    have hneg := neg_le_neg hmul
    convert hneg using 1 <;> ring
  unfold wholeLineModifiedHeatKernel heatKernel
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
    abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (4 * Real.pi * s)),
    abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (-s) *
        (1 / Real.sqrt (4 * Real.pi * s) * Real.exp (-z ^ 2 / (4 * s)))
        ≤ 1 *
          (1 / Real.sqrt (2 * Real.pi * t) *
            Real.exp (-(1 / (6 * t)) * z ^ 2)) := by
      gcongr
    _ = (1 / Real.sqrt (2 * Real.pi * t)) *
          Real.exp (-(1 / (6 * t)) * z ^ 2) := one_mul _

theorem abs_wholeLineModifiedHeatGradientKernel_local_time_le
    {t s : ℝ} (ht : 0 < t) (hs : s ∈ Metric.ball t (t / 2)) (z : ℝ) :
    |wholeLineModifiedHeatGradientKernel s z| ≤
      ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
        Real.sqrt (12 * t)) *
          Real.exp (-(1 / (12 * t)) * z ^ 2) := by
  have hdist := Metric.mem_ball.mp hs
  rw [Real.dist_eq] at hdist
  have hlow : t / 2 < s := by
    linarith [(abs_lt.mp hdist).1]
  have hup : s < 3 * t / 2 := by
    linarith [(abs_lt.mp hdist).2]
  have hspos : 0 < s := by linarith
  have ht_le_two_s : t ≤ 2 * s := by linarith
  have h1 : 1 / (2 * s) ≤ 1 / t :=
    one_div_le_one_div_of_le ht ht_le_two_s
  have hsqrt_le :
      Real.sqrt (2 * Real.pi * t) ≤ Real.sqrt (4 * Real.pi * s) := by
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos, ht_le_two_s]
  have h2 : 1 / Real.sqrt (4 * Real.pi * s) ≤
      1 / Real.sqrt (2 * Real.pi * t) :=
    one_div_le_one_div_of_le (by positivity) hsqrt_le
  have hsqrt_time : Real.sqrt (4 * (2 * s)) ≤ Real.sqrt (12 * t) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hcoeff : heatGradPointwiseBound s ≤
      (1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) * Real.sqrt (12 * t) := by
    unfold heatGradPointwiseBound
    exact mul_le_mul
      (mul_le_mul h1 h2 (by positivity) (by positivity)) hsqrt_time
      (Real.sqrt_nonneg _) (by positivity)
  have hden_le : 4 * (2 * s) ≤ 12 * t := by linarith
  have hinv : 1 / (12 * t) ≤ 1 / (4 * (2 * s)) :=
    one_div_le_one_div_of_le (by positivity) hden_le
  have hexp_space : Real.exp (-z ^ 2 / (4 * (2 * s))) ≤
      Real.exp (-(1 / (12 * t)) * z ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hinv (sq_nonneg z)
    have hneg := neg_le_neg hmul
    convert hneg using 1 <;> ring
  have hkernel : |deriv (fun w : ℝ => heatKernel s w) z| ≤
      ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
        Real.sqrt (12 * t)) *
          Real.exp (-(1 / (12 * t)) * z ^ 2) :=
    (abs_deriv_heatKernel_le hspos z).trans
      (mul_le_mul hcoeff hexp_space (Real.exp_nonneg _) (by positivity))
  have hexp_time : Real.exp (-s) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (by linarith : -s ≤ 0)
  unfold wholeLineModifiedHeatGradientKernel
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (-s) * |deriv (fun w : ℝ => heatKernel s w) z|
        ≤ 1 *
          (((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
            Real.sqrt (12 * t)) *
              Real.exp (-(1 / (12 * t)) * z ^ 2)) :=
      mul_le_mul hexp_time hkernel (abs_nonneg _) (by positivity)
    _ = ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
          Real.sqrt (12 * t)) *
            Real.exp (-(1 / (12 * t)) * z ^ 2) := one_mul _

theorem wholeLineModifiedHeatKernel_L1_tendsto
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun s : ℝ => ∫ z : ℝ,
        |wholeLineModifiedHeatKernel s z - wholeLineModifiedHeatKernel t z|)
      (𝓝 t) (𝓝 0) := by
  let F : ℝ → ℝ → ℝ := fun s z =>
    |wholeLineModifiedHeatKernel s z - wholeLineModifiedHeatKernel t z|
  let C : ℝ := 1 / Real.sqrt (2 * Real.pi * t)
  let bound : ℝ → ℝ := fun z =>
    2 * (C * Real.exp (-(1 / (6 * t)) * z ^ 2))
  have hball : Metric.ball t (t / 2) ∈ 𝓝 t :=
    Metric.ball_mem_nhds t (half_pos ht)
  have htball : t ∈ Metric.ball t (t / 2) :=
    Metric.mem_ball_self (half_pos ht)
  have hF_meas : Filter.Eventually
      (fun s => AEStronglyMeasurable (F s) volume) (𝓝 t) := by
    filter_upwards [hball] with s hs
    have hspos : 0 < s := by
      have hdist := Metric.mem_ball.mp hs
      rw [Real.dist_eq] at hdist
      linarith [(abs_lt.mp hdist).1]
    exact ((wholeLineModifiedHeatKernel_continuous hspos).sub
      (wholeLineModifiedHeatKernel_continuous ht)).abs.aestronglyMeasurable
  have h_bound : Filter.Eventually
      (fun s => ∀ᵐ z ∂volume, ‖F s z‖ ≤ bound z) (𝓝 t) := by
    filter_upwards [hball] with s hs
    exact Eventually.of_forall fun z => by
      dsimp [F, bound, C]
      rw [abs_abs]
      calc
        |wholeLineModifiedHeatKernel s z - wholeLineModifiedHeatKernel t z|
            ≤ |wholeLineModifiedHeatKernel s z| +
                |wholeLineModifiedHeatKernel t z| := abs_sub _ _
        _ ≤ (1 / Real.sqrt (2 * Real.pi * t)) *
              Real.exp (-(1 / (6 * t)) * z ^ 2) +
            (1 / Real.sqrt (2 * Real.pi * t)) *
              Real.exp (-(1 / (6 * t)) * z ^ 2) :=
          add_le_add
            (abs_wholeLineModifiedHeatKernel_local_time_le ht hs z)
            (abs_wholeLineModifiedHeatKernel_local_time_le ht htball z)
        _ = 2 * ((1 / Real.sqrt (2 * Real.pi * t)) *
              Real.exp (-(1 / (6 * t)) * z ^ 2)) := by ring
  have hbound_int : Integrable bound volume := by
    have hb : (0 : ℝ) < 1 / (6 * t) := by positivity
    dsimp [bound, C]
    simpa [mul_assoc] using
      (integrable_exp_neg_mul_sq hb).const_mul
        (2 * (1 / Real.sqrt (2 * Real.pi * t)))
  have h_lim : ∀ᵐ z ∂volume,
      Tendsto (fun s : ℝ => F s z) (𝓝 t) (𝓝 0) :=
    Eventually.of_forall fun z => by
      have h := ((wholeLineModifiedHeatKernel_continuousAt_time ht z).sub
        (continuousAt_const : ContinuousAt
          (fun _ : ℝ => wholeLineModifiedHeatKernel t z) t)).abs
      change Tendsto
        (fun s : ℝ =>
          |wholeLineModifiedHeatKernel s z - wholeLineModifiedHeatKernel t z|)
        (𝓝 t)
        (𝓝 |wholeLineModifiedHeatKernel t z -
          wholeLineModifiedHeatKernel t z|) at h
      simpa [F] using h
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝 t) (F := F) (f := fun _ : ℝ => (0 : ℝ))
    bound hF_meas h_bound hbound_int h_lim
  simpa [F] using hDCT

theorem wholeLineModifiedHeatGradientKernel_L1_tendsto
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun s : ℝ => ∫ z : ℝ,
        |wholeLineModifiedHeatGradientKernel s z -
          wholeLineModifiedHeatGradientKernel t z|)
      (𝓝 t) (𝓝 0) := by
  let F : ℝ → ℝ → ℝ := fun s z =>
    |wholeLineModifiedHeatGradientKernel s z -
      wholeLineModifiedHeatGradientKernel t z|
  let C : ℝ :=
    (1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) * Real.sqrt (12 * t)
  let bound : ℝ → ℝ := fun z =>
    2 * (C * Real.exp (-(1 / (12 * t)) * z ^ 2))
  have hball : Metric.ball t (t / 2) ∈ 𝓝 t :=
    Metric.ball_mem_nhds t (half_pos ht)
  have htball : t ∈ Metric.ball t (t / 2) :=
    Metric.mem_ball_self (half_pos ht)
  have hF_meas : Filter.Eventually
      (fun s => AEStronglyMeasurable (F s) volume) (𝓝 t) := by
    filter_upwards [hball] with s hs
    have hspos : 0 < s := by
      have hdist := Metric.mem_ball.mp hs
      rw [Real.dist_eq] at hdist
      linarith [(abs_lt.mp hdist).1]
    exact ((wholeLineModifiedHeatGradientKernel_continuous hspos).sub
      (wholeLineModifiedHeatGradientKernel_continuous ht)).abs.aestronglyMeasurable
  have h_bound : Filter.Eventually
      (fun s => ∀ᵐ z ∂volume, ‖F s z‖ ≤ bound z) (𝓝 t) := by
    filter_upwards [hball] with s hs
    exact Eventually.of_forall fun z => by
      dsimp [F, bound, C]
      rw [abs_abs]
      calc
        |wholeLineModifiedHeatGradientKernel s z -
            wholeLineModifiedHeatGradientKernel t z|
            ≤ |wholeLineModifiedHeatGradientKernel s z| +
                |wholeLineModifiedHeatGradientKernel t z| := abs_sub _ _
        _ ≤ (((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
                Real.sqrt (12 * t)) *
              Real.exp (-(1 / (12 * t)) * z ^ 2)) +
            (((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
                Real.sqrt (12 * t)) *
              Real.exp (-(1 / (12 * t)) * z ^ 2)) :=
          add_le_add
            (abs_wholeLineModifiedHeatGradientKernel_local_time_le ht hs z)
            (abs_wholeLineModifiedHeatGradientKernel_local_time_le ht htball z)
        _ = 2 * (((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
                Real.sqrt (12 * t)) *
              Real.exp (-(1 / (12 * t)) * z ^ 2)) := by ring
  have hbound_int : Integrable bound volume := by
    have hb : (0 : ℝ) < 1 / (12 * t) := by positivity
    dsimp [bound, C]
    simpa [mul_assoc] using
      (integrable_exp_neg_mul_sq hb).const_mul
        (2 * ((1 / t) * (1 / Real.sqrt (2 * Real.pi * t)) *
          Real.sqrt (12 * t)))
  have h_lim : ∀ᵐ z ∂volume,
      Tendsto (fun s : ℝ => F s z) (𝓝 t) (𝓝 0) :=
    Eventually.of_forall fun z => by
      have h := ((wholeLineModifiedHeatGradientKernel_continuousAt_time ht z).sub
        (continuousAt_const : ContinuousAt
          (fun _ : ℝ => wholeLineModifiedHeatGradientKernel t z) t)).abs
      change Tendsto
        (fun s : ℝ => |wholeLineModifiedHeatGradientKernel s z -
          wholeLineModifiedHeatGradientKernel t z|)
        (𝓝 t)
        (𝓝 |wholeLineModifiedHeatGradientKernel t z -
          wholeLineModifiedHeatGradientKernel t z|) at h
      simpa [F] using h
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝 t) (F := F) (f := fun _ : ℝ => (0 : ℝ))
    bound hF_meas h_bound hbound_int h_lim
  simpa [F] using hDCT

theorem wholeLineCauchyHeatBUCTotal_continuousAt_of_pos
    {t : ℝ} (ht : 0 < t) (u : WholeLineBUC) :
    ContinuousAt (fun s : ℝ => wholeLineCauchyHeatBUCTotal s u) t := by
  have hupper : Tendsto
      (fun s : ℝ => (∫ z : ℝ,
        |wholeLineModifiedHeatKernel s z - wholeLineModifiedHeatKernel t z|) * ‖u‖)
      (𝓝 t) (𝓝 0) := by
    simpa using (wholeLineModifiedHeatKernel_L1_tendsto ht).mul_const ‖u‖
  refine tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hupper)
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hspos : 0 < s := hs
  rw [show wholeLineCauchyHeatBUCTotal s u =
      wholeLineCauchyHeatBUC s hspos u by
    simp [wholeLineCauchyHeatBUCTotal, hspos]]
  rw [show wholeLineCauchyHeatBUCTotal t u =
      wholeLineCauchyHeatBUC t ht u by
    simp [wholeLineCauchyHeatBUCTotal, ht]]
  simpa [wholeLineCauchyHeatBUC] using
    kernelConvBUC_kernel_dist_le
      (wholeLineModifiedHeatKernel_continuous hspos)
      (wholeLineModifiedHeatKernel_integrable hspos)
      (wholeLineModifiedHeatKernel_continuous ht)
      (wholeLineModifiedHeatKernel_integrable ht) u

/-- The modified Gaussian gradient operator, totalized by zero outside
positive time.  Only its positive-time continuity is used. -/
def wholeLineCauchyHeatGradientBUCTotal
    (t : ℝ) (u : WholeLineBUC) : WholeLineBUC :=
  if ht : 0 < t then wholeLineCauchyHeatGradientBUC t ht u else 0

theorem wholeLineCauchyHeatGradientBUCTotal_continuousAt_of_pos
    {t : ℝ} (ht : 0 < t) (u : WholeLineBUC) :
    ContinuousAt (fun s : ℝ => wholeLineCauchyHeatGradientBUCTotal s u) t := by
  have hupper : Tendsto
      (fun s : ℝ => (∫ z : ℝ,
        |wholeLineModifiedHeatGradientKernel s z -
          wholeLineModifiedHeatGradientKernel t z|) * ‖u‖)
      (𝓝 t) (𝓝 0) := by
    simpa using
      (wholeLineModifiedHeatGradientKernel_L1_tendsto ht).mul_const ‖u‖
  refine tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hupper)
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hspos : 0 < s := hs
  rw [show wholeLineCauchyHeatGradientBUCTotal s u =
      wholeLineCauchyHeatGradientBUC s hspos u by
    simp [wholeLineCauchyHeatGradientBUCTotal, hspos]]
  rw [show wholeLineCauchyHeatGradientBUCTotal t u =
      wholeLineCauchyHeatGradientBUC t ht u by
    simp [wholeLineCauchyHeatGradientBUCTotal, ht]]
  simpa [wholeLineCauchyHeatGradientBUC] using
    kernelConvBUC_kernel_dist_le
      (wholeLineModifiedHeatGradientKernel_continuous hspos)
      (wholeLineModifiedHeatGradientKernel_integrable hspos)
      (wholeLineModifiedHeatGradientKernel_continuous ht)
      (wholeLineModifiedHeatGradientKernel_integrable ht) u

theorem wholeLineCauchyHeatBUCTotal_jointContinuousAt_of_pos
    {t : ℝ} (ht : 0 < t) (u : WholeLineBUC) :
    ContinuousAt
      (fun q : ℝ × WholeLineBUC =>
        wholeLineCauchyHeatBUCTotal q.1 q.2) (t, u) := by
  have hdist : Tendsto (fun q : ℝ × WholeLineBUC => dist q.2 u)
      (𝓝 (t, u)) (𝓝 0) := by
    have h := continuousAt_snd.dist
      (continuousAt_const : ContinuousAt
        (fun _ : ℝ × WholeLineBUC => u) (t, u))
    change Tendsto (fun q : ℝ × WholeLineBUC => dist q.2 u)
      (𝓝 (t, u)) (𝓝 (dist u u)) at h
    simpa using h
  have hexp : Tendsto (fun q : ℝ × WholeLineBUC => Real.exp (-q.1))
      (𝓝 (t, u)) (𝓝 (Real.exp (-t))) := by
    exact (by fun_prop : ContinuousAt
      (fun q : ℝ × WholeLineBUC => Real.exp (-q.1)) (t, u))
  have hfirst : Tendsto
      (fun q : ℝ × WholeLineBUC => Real.exp (-q.1) * dist q.2 u)
      (𝓝 (t, u)) (𝓝 0) := by
    simpa using hexp.mul hdist
  have hkernel : Tendsto
      (fun q : ℝ × WholeLineBUC => ∫ z : ℝ,
        |wholeLineModifiedHeatKernel q.1 z -
          wholeLineModifiedHeatKernel t z|)
      (𝓝 (t, u)) (𝓝 0) :=
    (wholeLineModifiedHeatKernel_L1_tendsto ht).comp continuousAt_fst
  have hsecond : Tendsto
      (fun q : ℝ × WholeLineBUC => (∫ z : ℝ,
        |wholeLineModifiedHeatKernel q.1 z -
          wholeLineModifiedHeatKernel t z|) * ‖u‖)
      (𝓝 (t, u)) (𝓝 0) := by
    simpa using hkernel.mul_const ‖u‖
  have hupper : Tendsto
      (fun q : ℝ × WholeLineBUC =>
        Real.exp (-q.1) * dist q.2 u +
          (∫ z : ℝ, |wholeLineModifiedHeatKernel q.1 z -
            wholeLineModifiedHeatKernel t z|) * ‖u‖)
      (𝓝 (t, u)) (𝓝 0) := by
    simpa using hfirst.add hsecond
  refine tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hupper)
  filter_upwards [continuousAt_fst (Ioi_mem_nhds ht)] with q hq
  have hqpos : 0 < q.1 := hq
  rw [show wholeLineCauchyHeatBUCTotal q.1 q.2 =
      wholeLineCauchyHeatBUC q.1 hqpos q.2 by
    simp [wholeLineCauchyHeatBUCTotal, hqpos]]
  rw [show wholeLineCauchyHeatBUCTotal t u =
      wholeLineCauchyHeatBUC t ht u by
    simp [wholeLineCauchyHeatBUCTotal, ht]]
  simpa [wholeLineCauchyHeatBUC,
    wholeLineModifiedHeatKernel_integral_abs hqpos] using
    kernelConvBUC_joint_dist_le
      (wholeLineModifiedHeatKernel_continuous hqpos)
      (wholeLineModifiedHeatKernel_integrable hqpos)
      (wholeLineModifiedHeatKernel_continuous ht)
      (wholeLineModifiedHeatKernel_integrable ht) q.2 u

theorem wholeLineCauchyHeatGradientBUCTotal_jointContinuousAt_of_pos
    {t : ℝ} (ht : 0 < t) (u : WholeLineBUC) :
    ContinuousAt
      (fun q : ℝ × WholeLineBUC =>
        wholeLineCauchyHeatGradientBUCTotal q.1 q.2) (t, u) := by
  have hdist : Tendsto (fun q : ℝ × WholeLineBUC => dist q.2 u)
      (𝓝 (t, u)) (𝓝 0) := by
    have h := continuousAt_snd.dist
      (continuousAt_const : ContinuousAt
        (fun _ : ℝ × WholeLineBUC => u) (t, u))
    change Tendsto (fun q : ℝ × WholeLineBUC => dist q.2 u)
      (𝓝 (t, u)) (𝓝 (dist u u)) at h
    simpa using h
  have hcoeff : Tendsto
      (fun q : ℝ × WholeLineBUC =>
        Real.exp (-q.1) * (2 / Real.sqrt (4 * Real.pi * q.1)))
      (𝓝 (t, u))
      (𝓝 (Real.exp (-t) * (2 / Real.sqrt (4 * Real.pi * t)))) := by
    exact (by fun_prop (disch := positivity) : ContinuousAt
      (fun q : ℝ × WholeLineBUC =>
        Real.exp (-q.1) * (2 / Real.sqrt (4 * Real.pi * q.1))) (t, u))
  have hfirst : Tendsto
      (fun q : ℝ × WholeLineBUC =>
        (Real.exp (-q.1) * (2 / Real.sqrt (4 * Real.pi * q.1))) *
          dist q.2 u)
      (𝓝 (t, u)) (𝓝 0) := by
    simpa using hcoeff.mul hdist
  have hkernel : Tendsto
      (fun q : ℝ × WholeLineBUC => ∫ z : ℝ,
        |wholeLineModifiedHeatGradientKernel q.1 z -
          wholeLineModifiedHeatGradientKernel t z|)
      (𝓝 (t, u)) (𝓝 0) :=
    (wholeLineModifiedHeatGradientKernel_L1_tendsto ht).comp continuousAt_fst
  have hsecond : Tendsto
      (fun q : ℝ × WholeLineBUC => (∫ z : ℝ,
        |wholeLineModifiedHeatGradientKernel q.1 z -
          wholeLineModifiedHeatGradientKernel t z|) * ‖u‖)
      (𝓝 (t, u)) (𝓝 0) := by
    simpa using hkernel.mul_const ‖u‖
  have hupper : Tendsto
      (fun q : ℝ × WholeLineBUC =>
        (Real.exp (-q.1) * (2 / Real.sqrt (4 * Real.pi * q.1))) *
            dist q.2 u +
          (∫ z : ℝ, |wholeLineModifiedHeatGradientKernel q.1 z -
            wholeLineModifiedHeatGradientKernel t z|) * ‖u‖)
      (𝓝 (t, u)) (𝓝 0) := by
    simpa using hfirst.add hsecond
  refine tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hupper)
  filter_upwards [continuousAt_fst (Ioi_mem_nhds ht)] with q hq
  have hqpos : 0 < q.1 := hq
  rw [show wholeLineCauchyHeatGradientBUCTotal q.1 q.2 =
      wholeLineCauchyHeatGradientBUC q.1 hqpos q.2 by
    simp [wholeLineCauchyHeatGradientBUCTotal, hqpos]]
  rw [show wholeLineCauchyHeatGradientBUCTotal t u =
      wholeLineCauchyHeatGradientBUC t ht u by
    simp [wholeLineCauchyHeatGradientBUCTotal, ht]]
  simpa [wholeLineCauchyHeatGradientBUC,
    wholeLineModifiedHeatGradientKernel_integral_abs hqpos] using
    kernelConvBUC_joint_dist_le
      (wholeLineModifiedHeatGradientKernel_continuous hqpos)
      (wholeLineModifiedHeatGradientKernel_integrable hqpos)
      (wholeLineModifiedHeatGradientKernel_continuous ht)
      (wholeLineModifiedHeatGradientKernel_integrable ht) q.2 u

section WholeLineCauchyBUCHeatPositiveTimeAxiomAudit

#print axioms wholeLineModifiedHeatKernel_L1_tendsto
#print axioms wholeLineModifiedHeatGradientKernel_L1_tendsto
#print axioms wholeLineCauchyHeatBUCTotal_continuousAt_of_pos
#print axioms wholeLineCauchyHeatGradientBUCTotal_continuousAt_of_pos
#print axioms wholeLineCauchyHeatBUCTotal_jointContinuousAt_of_pos
#print axioms wholeLineCauchyHeatGradientBUCTotal_jointContinuousAt_of_pos

end WholeLineCauchyBUCHeatPositiveTimeAxiomAudit

end ShenWork.Paper1
