import ShenWork.Paper2.IntervalCD6Tail

noncomputable section

namespace ShenWork.Paper2.CD6CosineModeBounds

theorem unitIntervalCosineMode_iteratedFDeriv_bound
    (k n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (unitIntervalCosineMode n) x‖ ≤
      |(n : ℝ) * Real.pi| ^ k := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  set freq : ℝ := (n : ℝ) * Real.pi with hfreq
  have hcomp := congrFun
    (iteratedDeriv_comp_const_mul (n := k) (f := Real.cos)
      (Real.contDiff_cos (n := (k : WithTop ℕ∞))) freq) x
  change ‖iteratedDeriv k (fun y : ℝ => Real.cos (freq * y)) x‖ ≤
    |freq| ^ k
  rw [hcomp, Real.norm_eq_abs, abs_mul, abs_pow]
  calc |freq| ^ k * |iteratedDeriv k Real.cos (freq * x)|
      ≤ |freq| ^ k * 1 := by
        exact mul_le_mul_of_nonneg_left
          (Real.abs_iteratedDeriv_cos_le_one k _)
          (pow_nonneg (abs_nonneg freq) k)
    _ = |freq| ^ k := by ring

theorem frequency_pow_mul_exp_summable
    (k : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      |(n : ℝ) * Real.pi| ^ k *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase : Summable (fun n : ℕ =>
      Real.pi ^ k * ((n : ℝ) ^ k *
        Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)))) := by
    simpa [mul_assoc] using
      (Real.summable_pow_mul_exp_neg_nat_mul k hc).mul_left
        (Real.pi ^ k)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · exact mul_nonneg (pow_nonneg (abs_nonneg _) k) (Real.exp_nonneg _)
  · have hn_sq_ge : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst n
        norm_num
      · exact le_self_pow₀ (by exact_mod_cast hn) (by norm_num)
    have hlam_eq :
        unitIntervalCosineEigenvalue n = (n : ℝ) ^ 2 * Real.pi ^ 2 := by
      unfold unitIntervalCosineEigenvalue
      ring
    have hexp_le :
        Real.exp (-τ * unitIntervalCosineEigenvalue n) ≤
          Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      rw [hlam_eq]
      nlinarith [mul_nonneg hτ.le (sq_nonneg Real.pi), hn_sq_ge]
    have hfreq_eq :
        |(n : ℝ) * Real.pi| ^ k = Real.pi ^ k * (n : ℝ) ^ k := by
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le)]
      rw [mul_pow]
      ring
    calc |(n : ℝ) * Real.pi| ^ k *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)
        = Real.pi ^ k * ((n : ℝ) ^ k *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
          rw [hfreq_eq]
          ring
      _ ≤ Real.pi ^ k * ((n : ℝ) ^ k *
            Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp_le (by positivity))
            (by positivity)

end ShenWork.Paper2.CD6CosineModeBounds
