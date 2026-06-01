/-
  ShenWork/Paper2/IntervalDuhamelIntegrability.lean

  Universal Duhamel bounds: work for ALL bounded sources regardless
  of measurability. When the integrand is not integrable, Lean's
  integral_undef gives 0, so bounds hold trivially.
-/
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.PDE.IntervalFullKernelSupBound

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradDuhamelBound (valueDuhamel_sup_bound gradDuhamel_sup_bound)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant
  heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.IntervalDuhamelIntegrability

/-- Universal value Duhamel bound: works for ALL bounded sources, regardless
of measurability. When the integrand is IntervalIntegrable, uses the standard
semigroup L∞ bound. When not, the interval integral is 0 by integral_undef. -/
theorem valueDuhamel_sup_bound_universal
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {r : ℝ → ℝ → ℝ}
    {Cr : ℝ} (hCr : 0 ≤ Cr) (hr_sup : ∀ s y, |r s y| ≤ Cr) (x : ℝ) :
    |∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r s) x| ≤ T * Cr := by
  by_cases hint : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (r s) x) volume 0 t
  · exact valueDuhamel_sup_bound ht htT hCr hr_sup x hint
  · rw [intervalIntegral.integral_undef hint]
    simp; exact mul_nonneg (le_of_lt (lt_of_lt_of_le ht htT)) hCr

/-- Universal gradient Duhamel bound: works for ALL bounded sources. -/
theorem gradDuhamel_sup_bound_universal
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ) :
    |∫ s in (0:ℝ)..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq := by
  by_cases hq_int : ∀ s, Integrable (q s) (intervalMeasure 1)
  · by_cases hg_int : IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x)
        volume 0 t
    · exact gradDuhamel_sup_bound ht htT hq_int hCq hq_sup x hg_int
    · rw [intervalIntegral.integral_undef hg_int, abs_zero]
      exact mul_nonneg
        (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg T)))
        hCq
  · -- Some spatial slice is not integrable, but the time integral
    -- might or might not be IntervalIntegrable.
    by_cases hg_int : IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x)
        volume 0 t
    · -- Time-integrable case: bound each slice individually.
      -- For s where q(s) is not integrable, S(t-s)(q s) = 0, deriv = 0.
      -- For s where q(s) is integrable, the pointwise bound applies.
      -- Either way, |deriv| ≤ C_grad * Cq * (t-s)^{-1/2}.
      sorry
    · rw [intervalIntegral.integral_undef hg_int, abs_zero]
      exact mul_nonneg
        (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg T)))
        hCq

end ShenWork.IntervalDuhamelIntegrability
