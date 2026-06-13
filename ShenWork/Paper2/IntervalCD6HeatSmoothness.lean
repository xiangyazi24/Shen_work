import ShenWork.Paper2.IntervalCD6CosineModeBounds

noncomputable section

namespace ShenWork.Paper2.CD6HeatSmoothness

open ShenWork.Paper2.CD6CosineModeBounds

theorem unitIntervalCosineHeatValue_contDiff_seven
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ}
    (hM : ∀ n, |a n| ≤ M) :
    ContDiff ℝ 7 (fun x => unitIntervalCosineHeatValue t a x) := by
  unfold unitIntervalCosineHeatValue
  let v : ℕ → ℕ → ℝ := fun k n =>
    |(n : ℝ) * Real.pi| ^ k *
      Real.exp (-t * unitIntervalCosineEigenvalue n) * |M|
  refine contDiff_tsum
    (f := fun n x => unitIntervalCosineHeatPointWeight t x n * a n)
    (v := v) (N := (7 : ℕ∞)) ?_ ?_ ?_
  · intro n
    unfold unitIntervalCosineHeatPointWeight unitIntervalCosineMode
    fun_prop
  · intro k _hk
    exact (frequency_pow_mul_exp_summable k ht).mul_right |M|
  · intro k n x _hk
    unfold v unitIntervalCosineHeatPointWeight
    set c : ℝ := Real.exp (-t * unitIntervalCosineEigenvalue n) * a n with hc
    have hterm :
        (fun y : ℝ =>
          Real.exp (-t * unitIntervalCosineEigenvalue n) *
            unitIntervalCosineMode n y * a n) =
        fun y : ℝ => c * unitIntervalCosineMode n y := by
      funext y
      rw [hc]
      ring
    change ‖iteratedFDeriv ℝ k (fun y : ℝ =>
      Real.exp (-t * unitIntervalCosineEigenvalue n) *
        unitIntervalCosineMode n y * a n) x‖ ≤
        |(n : ℝ) * Real.pi| ^ k *
          Real.exp (-t * unitIntervalCosineEigenvalue n) * |M|
    rw [hterm, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hcd : ContDiffAt ℝ (k : WithTop ℕ∞) (unitIntervalCosineMode n) x := by
      unfold unitIntervalCosineMode
      fun_prop
    rw [iteratedDeriv_const_mul c hcd, Real.norm_eq_abs, abs_mul]
    have hmode : |iteratedDeriv k (unitIntervalCosineMode n) x| ≤
        |(n : ℝ) * Real.pi| ^ k := by
      simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        using unitIntervalCosineMode_iteratedFDeriv_bound k n x
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    have hcabs : |c| ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) * |M| := by
      rw [hc, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left hMn (Real.exp_nonneg _)
    calc |c| * |iteratedDeriv k (unitIntervalCosineMode n) x|
        ≤ (Real.exp (-t * unitIntervalCosineEigenvalue n) * |M|) *
            |(n : ℝ) * Real.pi| ^ k := by
          exact mul_le_mul hcabs hmode (abs_nonneg _)
            (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))
      _ = |(n : ℝ) * Real.pi| ^ k *
            Real.exp (-t * unitIntervalCosineEigenvalue n) * |M| := by ring

end ShenWork.Paper2.CD6HeatSmoothness
