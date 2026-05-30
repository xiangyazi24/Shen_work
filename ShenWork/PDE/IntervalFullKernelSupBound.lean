/-
  ShenWork/PDE/IntervalFullKernelSupBound.lean

  **T2 — full Neumann kernel `L∞→L∞` (sup) bound.**

  Full-kernel analogue of `intervalSemigroupOperator_Linfty_bound`: the full
  Neumann propagator is an `L∞` contraction,

    `|intervalFullSemigroupOperator t f x| ≤ M`  whenever `|f| ≤ M`,

  resting on the three kernel facts — nonnegativity, integrability, and mass `= 1`
  (`intervalNeumannFullKernel_integral_eq_one`, T2-c) — exactly as the zeroth
  version rests on `normalizedZerothReflectionKernel_{nonneg, integrable, mass≤1}`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelMass

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- The full Neumann kernel is nonnegative. -/
theorem intervalNeumannFullKernel_nonneg {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    0 ≤ intervalNeumannFullKernel t x y := by
  rw [intervalNeumannFullKernel]
  exact tsum_nonneg fun k => add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _)

/-- The full Neumann kernel is integrable against `intervalMeasure 1`. -/
theorem intervalNeumannFullKernel_integrable {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (fun y : ℝ => intervalNeumannFullKernel t x y) (intervalMeasure 1) := by
  simp only [intervalMeasure, intervalSet]
  exact (continuousOn_intervalNeumannFullKernel_snd ht x).integrableOn_Icc

/-- Mass `= 1` against the interval measure (`intervalMeasure 1 = volume.restrict (Icc 0 1)`). -/
theorem intervalNeumannFullKernel_intervalMeasure_integral_eq_one {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y, intervalNeumannFullKernel t x y ∂(intervalMeasure 1)) = 1 := by
  have hconv :
      (∫ y, intervalNeumannFullKernel t x y ∂(intervalMeasure 1))
        = ∫ y in (0 : ℝ)..1, intervalNeumannFullKernel t x y := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [intervalMeasure, intervalSet]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hconv]
  exact intervalNeumannFullKernel_integral_eq_one ht x

/-- **Full-kernel `L∞→L∞` (sup) bound.**  `|intervalFullSemigroupOperator t f x| ≤ M`
whenever `|f| ≤ M`. -/
theorem intervalFullSemigroupOperator_Linfty_bound {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalFullSemigroupOperator t f x| ≤ M := by
  have hkernel_int := intervalNeumannFullKernel_integrable ht x
  have hupper_int : Integrable (fun y => M * intervalNeumannFullKernel t x y) (intervalMeasure 1) :=
    hkernel_int.const_mul M
  have hmass := intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht x
  have hnorm : ‖∫ y, intervalNeumannFullKernel t x y * f y ∂(intervalMeasure 1)‖ ≤ M :=
    calc ‖∫ y, intervalNeumannFullKernel t x y * f y ∂(intervalMeasure 1)‖
        ≤ ∫ y, ‖intervalNeumannFullKernel t x y * f y‖ ∂(intervalMeasure 1) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ y, M * intervalNeumannFullKernel t x y ∂(intervalMeasure 1) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun y => norm_nonneg _) hupper_int
            (Filter.Eventually.of_forall fun y => ?_)
          change ‖intervalNeumannFullKernel t x y * f y‖
            ≤ M * intervalNeumannFullKernel t x y
          rw [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (intervalNeumannFullKernel_nonneg ht x y)]
          calc intervalNeumannFullKernel t x y * ‖f y‖
              ≤ intervalNeumannFullKernel t x y * M :=
                mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hf y)
                  (intervalNeumannFullKernel_nonneg ht x y)
            _ = M * intervalNeumannFullKernel t x y := by ring
      _ = M * ∫ y, intervalNeumannFullKernel t x y ∂(intervalMeasure 1) :=
          MeasureTheory.integral_const_mul _ _
      _ = M * 1 := by rw [hmass]
      _ = M := by ring
  rw [Real.norm_eq_abs] at hnorm
  exact hnorm

end ShenWork.IntervalNeumannFullKernel
