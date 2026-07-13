import ShenWork.PDE.IntervalFullKernelSupBound

/-!
# A uniform positive-time floor for the interval Neumann heat kernel

The negative-sensitivity minimal branch needs a quantitative form of the
strict positivity used in the paper's strong-maximum-principle argument.  On
the compact window `1 <= t <= 2`, `x,y in [0,1]`, the direct Gaussian image
already has a uniform positive lower bound.  Since every remaining image is
nonnegative, the same bound holds for the full Neumann kernel.

No compactness or stability package is used here.
-/

open MeasureTheory Set

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalNeumannFullKernel

/-- A concrete positive floor for the direct Gaussian image on the unit
positive-time window. -/
def unitWindowHeatKernelFloor : ℝ :=
  1 / Real.sqrt (8 * Real.pi) * Real.exp (-(1 : ℝ) / 4)

theorem unitWindowHeatKernelFloor_pos : 0 < unitWindowHeatKernelFloor := by
  unfold unitWindowHeatKernelFloor
  positivity

/-- On `1 <= t <= 2` and `|z| <= 1`, the Gaussian is bounded below by the
fixed positive constant `unitWindowHeatKernelFloor`. -/
theorem unitWindowHeatKernelFloor_le_heatKernel
    {t z : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) (hz : z ∈ Icc (-1 : ℝ) 1) :
    unitWindowHeatKernelFloor ≤ heatKernel t z := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden_pos : 0 < Real.sqrt (4 * Real.pi * t) := by positivity
  have hden_floor_pos : 0 < Real.sqrt (8 * Real.pi) := by positivity
  have hzsq : z ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - z by linarith [hz.2])
      (show 0 ≤ 1 + z by linarith [hz.1])]
  have harg : -(1 : ℝ) / 4 ≤ -z ^ 2 / (4 * t) := by
    have h4t : 0 < 4 * t := by positivity
    rw [le_div_iff₀ h4t]
    nlinarith [hzsq, ht.1]
  have hexp : Real.exp (-(1 : ℝ) / 4) ≤ Real.exp (-z ^ 2 / (4 * t)) :=
    Real.exp_le_exp.mpr harg
  have hrad : 4 * Real.pi * t ≤ 8 * Real.pi := by
    nlinarith [ht.2, hpi]
  have hsqrt : Real.sqrt (4 * Real.pi * t) ≤ Real.sqrt (8 * Real.pi) :=
    Real.sqrt_le_sqrt hrad
  have hinv : 1 / Real.sqrt (8 * Real.pi) ≤
      1 / Real.sqrt (4 * Real.pi * t) := by
    exact one_div_le_one_div_of_le hden_pos hsqrt
  unfold unitWindowHeatKernelFloor heatKernel
  exact mul_le_mul hinv hexp (Real.exp_pos _).le
    (le_of_lt (div_pos zero_lt_one hden_pos))

/-- The full Neumann heat kernel has the same uniform floor on the compact
unit positive-time window. -/
theorem unitWindowHeatKernelFloor_le_intervalNeumannFullKernel
    {t x y : ℝ} (ht : t ∈ Icc (1 : ℝ) 2)
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    unitWindowHeatKernelFloor ≤ intervalNeumannFullKernel t x y := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have hxy : x - y ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hfloor := unitWindowHeatKernelFloor_le_heatKernel ht hxy
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

/-- Quantitative positivity improvement of the full Neumann semigroup on the
unit positive-time window.  A nonnegative source is bounded below after heat
propagation by the kernel floor times its total mass. -/
theorem unitWindowHeatKernelFloor_mul_integral_le_semigroup
    {t x : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) (hx : x ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} {B : ℝ}
    (hf_int : Integrable f (ShenWork.IntervalDomain.intervalMeasure 1))
    (hf_meas : AEStronglyMeasurable f
      (ShenWork.IntervalDomain.intervalMeasure 1))
    (hf_nonneg : ∀ y, y ∈ Icc (0 : ℝ) 1 → 0 ≤ f y)
    (hf_bound : ∀ y, |f y| ≤ B) :
    unitWindowHeatKernelFloor *
        (∫ y, f y ∂(ShenWork.IntervalDomain.intervalMeasure 1)) ≤
      intervalFullSemigroupOperator t f x := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
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
  have hfloor_f_int : Integrable (fun y => unitWindowHeatKernelFloor * f y)
      (ShenWork.IntervalDomain.intervalMeasure 1) :=
    hf_int.const_mul unitWindowHeatKernelFloor
  calc
    unitWindowHeatKernelFloor *
          (∫ y, f y ∂(ShenWork.IntervalDomain.intervalMeasure 1)) =
        ∫ y, unitWindowHeatKernelFloor * f y
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
        (unitWindowHeatKernelFloor_le_intervalNeumannFullKernel ht hx hy)
        (hf_nonneg y hy)
    _ = intervalFullSemigroupOperator t f x := rfl

#print axioms unitWindowHeatKernelFloor_le_heatKernel
#print axioms unitWindowHeatKernelFloor_le_intervalNeumannFullKernel
#print axioms unitWindowHeatKernelFloor_mul_integral_le_semigroup

end ShenWork.Paper3
