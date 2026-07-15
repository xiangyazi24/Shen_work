import ShenWork.Paper3.IntervalDomainUniformHeatKernelFloor

/-!
# A heat-kernel floor on an arbitrary fixed positive-time window

This is the scaled form of `IntervalDomainUniformHeatKernelFloor`.  The
constant is explicit and positive for every lower time `τ > 0`.
-/

open MeasureTheory Set

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalNeumannFullKernel

def positiveTimeWindowHeatKernelFloor (τ : ℝ) : ℝ :=
  1 / Real.sqrt (8 * Real.pi * τ) * Real.exp (-(1 : ℝ) / (4 * τ))

theorem positiveTimeWindowHeatKernelFloor_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < positiveTimeWindowHeatKernelFloor τ := by
  unfold positiveTimeWindowHeatKernelFloor
  positivity

theorem positiveTimeWindowHeatKernelFloor_le_heatKernel
    {τ t z : ℝ} (hτ : 0 < τ) (ht : t ∈ Icc τ (2 * τ))
    (hz : z ∈ Icc (-1 : ℝ) 1) :
    positiveTimeWindowHeatKernelFloor τ ≤ heatKernel t z := by
  have ht0 : 0 < t := hτ.trans_le ht.1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden_pos : 0 < Real.sqrt (4 * Real.pi * t) := by positivity
  have hden_floor_pos : 0 < Real.sqrt (8 * Real.pi * τ) := by positivity
  have hzsq : z ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - z by linarith [hz.2])
      (show 0 ≤ 1 + z by linarith [hz.1])]
  have hfrac : z ^ 2 / (4 * t) ≤ 1 / (4 * τ) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 4 * t)
      (by positivity : 0 < 4 * τ)]
    have hmul : z ^ 2 * τ ≤ t := by
      have hzτ : z ^ 2 * τ ≤ 1 * τ :=
        mul_le_mul_of_nonneg_right hzsq hτ.le
      exact hzτ.trans (by simpa using ht.1)
    nlinarith
  have harg : -(1 : ℝ) / (4 * τ) ≤ -z ^ 2 / (4 * t) := by
    simpa only [neg_div] using neg_le_neg hfrac
  have hexp : Real.exp (-(1 : ℝ) / (4 * τ)) ≤
      Real.exp (-z ^ 2 / (4 * t)) := Real.exp_le_exp.mpr harg
  have hrad : 4 * Real.pi * t ≤ 8 * Real.pi * τ := by
    nlinarith [ht.2, hpi, hτ]
  have hsqrt : Real.sqrt (4 * Real.pi * t) ≤
      Real.sqrt (8 * Real.pi * τ) := Real.sqrt_le_sqrt hrad
  have hinv : 1 / Real.sqrt (8 * Real.pi * τ) ≤
      1 / Real.sqrt (4 * Real.pi * t) :=
    one_div_le_one_div_of_le hden_pos hsqrt
  unfold positiveTimeWindowHeatKernelFloor heatKernel
  exact mul_le_mul hinv hexp (Real.exp_pos _).le
    (le_of_lt (div_pos zero_lt_one hden_pos))

theorem positiveTimeWindowHeatKernelFloor_le_intervalNeumannFullKernel
    {τ t x y : ℝ} (hτ : 0 < τ) (ht : t ∈ Icc τ (2 * τ))
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    positiveTimeWindowHeatKernelFloor τ ≤
      intervalNeumannFullKernel t x y := by
  have ht0 : 0 < t := hτ.trans_le ht.1
  have hxy : x - y ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hfloor := positiveTimeWindowHeatKernelFloor_le_heatKernel hτ ht hxy
  rw [intervalNeumannFullKernel]
  have hsumA := latticeGaussianSummable ht0 (x - y)
  have hsumB := latticeGaussianSummable ht0 (x + y)
  have hsum : Summable (fun k : ℤ =>
      heatKernel t (x - y + 2 * (k : ℝ)) +
        heatKernel t (x + y + 2 * (k : ℝ))) := hsumA.add hsumB
  have hterm :
      heatKernel t (x - y + 2 * ((0 : ℤ) : ℝ)) +
          heatKernel t (x + y + 2 * ((0 : ℤ) : ℝ)) ≤
        ∑' k : ℤ,
          (heatKernel t (x - y + 2 * (k : ℝ)) +
            heatKernel t (x + y + 2 * (k : ℝ))) := by
    simpa using hsum.sum_le_tsum ({(0 : ℤ)} : Finset ℤ)
      (fun k _ => add_nonneg (heatKernel_nonneg ht0 _)
        (heatKernel_nonneg ht0 _))
  have hdirect : heatKernel t (x - y) ≤
      heatKernel t (x - y + 2 * ((0 : ℤ) : ℝ)) +
        heatKernel t (x + y + 2 * ((0 : ℤ) : ℝ)) := by
    norm_num
    exact heatKernel_nonneg ht0 _
  exact hfloor.trans (hdirect.trans hterm)

theorem positiveTimeWindowHeatKernelFloor_mul_integral_le_semigroup
    {τ t x : ℝ} (hτ : 0 < τ) (ht : t ∈ Icc τ (2 * τ))
    (hx : x ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} {B : ℝ}
    (hf_int : Integrable f (ShenWork.IntervalDomain.intervalMeasure 1))
    (hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hf_nonneg : ∀ y, y ∈ Icc (0 : ℝ) 1 → 0 ≤ f y)
    (hf_bound : ∀ y, |f y| ≤ B) :
    positiveTimeWindowHeatKernelFloor τ *
        (∫ y, f y ∂(ShenWork.IntervalDomain.intervalMeasure 1)) ≤
      intervalFullSemigroupOperator t f x := by
  have ht0 : 0 < t := hτ.trans_le ht.1
  have hK_int := intervalNeumannFullKernel_integrable ht0 x
  have hKf_int : Integrable
      (fun y => intervalNeumannFullKernel t x y * f y)
      (ShenWork.IntervalDomain.intervalMeasure 1) := by
    have hmul : Integrable
        (fun y => f y * intervalNeumannFullKernel t x y)
        (ShenWork.IntervalDomain.intervalMeasure 1) :=
      hK_int.bdd_mul hf_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact (hf_bound y).trans (le_abs_self B))
    exact hmul.congr (Filter.Eventually.of_forall fun y => mul_comm _ _)
  have hfloor_f_int : Integrable
      (fun y => positiveTimeWindowHeatKernelFloor τ * f y)
      (ShenWork.IntervalDomain.intervalMeasure 1) :=
    hf_int.const_mul (positiveTimeWindowHeatKernelFloor τ)
  calc
    positiveTimeWindowHeatKernelFloor τ *
          (∫ y, f y ∂(ShenWork.IntervalDomain.intervalMeasure 1)) =
        ∫ y, positiveTimeWindowHeatKernelFloor τ * f y
          ∂(ShenWork.IntervalDomain.intervalMeasure 1) := by
            rw [integral_const_mul]
    _ ≤ ∫ y, intervalNeumannFullKernel t x y * f y
          ∂(ShenWork.IntervalDomain.intervalMeasure 1) := by
      apply integral_mono_ae hfloor_f_int hKf_int
      simp only [ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet]
      refine (ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun y hy => ?_)
      exact mul_le_mul_of_nonneg_right
        (positiveTimeWindowHeatKernelFloor_le_intervalNeumannFullKernel
          hτ ht hx hy)
        (hf_nonneg y hy)
    _ = intervalFullSemigroupOperator t f x := rfl

end ShenWork.Paper3

#print axioms ShenWork.Paper3.positiveTimeWindowHeatKernelFloor_mul_integral_le_semigroup
