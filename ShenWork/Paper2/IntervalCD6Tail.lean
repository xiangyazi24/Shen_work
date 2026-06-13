import ShenWork.Paper2.IntervalACBPolynomialBridge
import ShenWork.PDE.IntervalH3E

/-!
# Lane CD6 heat tails

This module is the working front for the sixth-order clamped-source tail and
the higher heat-tail extensions needed by the χ₀<0 resolver-C² branch.
-/

noncomputable section

namespace ShenWork.Paper2.CD6Tail

private theorem eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase : Summable (fun n : ℕ =>
      Real.pi ^ (2 * m) * ((n : ℝ) ^ (2 * m) *
        Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)))) := by
    simpa [mul_assoc] using
      (Real.summable_pow_mul_exp_neg_nat_mul (2 * m) hc).mul_left
        (Real.pi ^ (2 * m))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
  · have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue
      positivity
    exact mul_nonneg (pow_nonneg hlam m) (Real.exp_nonneg _)
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
    have hpow_eq :
        unitIntervalCosineEigenvalue n ^ m =
          Real.pi ^ (2 * m) * (n : ℝ) ^ (2 * m) := by
      rw [hlam_eq, mul_pow]
      rw [pow_mul, pow_mul]
      rw [mul_comm]
    calc unitIntervalCosineEigenvalue n ^ m *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)
        = Real.pi ^ (2 * m) * ((n : ℝ) ^ (2 * m) *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
          rw [hpow_eq]
          ring
      _ ≤ Real.pi ^ (2 * m) * ((n : ℝ) ^ (2 * m) *
            Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp_le (by positivity))
            (by positivity)

theorem eigenvalue_fourth_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              Real.exp (-τ * unitIntervalCosineEigenvalue n))))) := by
  simpa [pow_succ, pow_two, mul_assoc] using
    (eigenvalue_pow_mul_exp_summable 4 hτ)

theorem eigenvalue_fifth_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n *
          (unitIntervalCosineEigenvalue n *
            (unitIntervalCosineEigenvalue n *
              (unitIntervalCosineEigenvalue n *
                Real.exp (-τ * unitIntervalCosineEigenvalue n)))))) := by
  simpa [pow_succ, pow_two, mul_assoc] using
    (eigenvalue_pow_mul_exp_summable 5 hτ)

theorem eigenvalue_sixth_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ (6 : ℕ) *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) :=
  eigenvalue_pow_mul_exp_summable 6 hτ

theorem eigenvalue_seventh_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ (7 : ℕ) *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) :=
  eigenvalue_pow_mul_exp_summable 7 hτ

end ShenWork.Paper2.CD6Tail
