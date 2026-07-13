import ShenWork.Paper3.IntervalDomainThetaMomentUniform

/-!
# The scalar weight in the Paper 3 entropy--elliptic estimate

For `eta = betaTilde beta`, testing the elliptic signal equation against
`(v - vStar) * (1 + v) ^ (-eta)` produces the coefficient

`(1 + v)^(-eta) - eta * (v - vStar) * (1 + v)^(-eta-1)`.

The paper's three-piece definition of `eta` is precisely what makes this
coefficient dominate
`(1 + eta * vStar) * (1 + v)^(-2*beta)` for every nonnegative signal.
-/

namespace ShenWork.Paper3

noncomputable section

/-- The pointwise coefficient produced by the weighted elliptic multiplier. -/
def entropyEllipticWeight (beta vStar v : ℝ) : ℝ :=
  (1 + v) ^ (-betaTilde beta) -
    betaTilde beta * (v - vStar) *
      (1 + v) ^ (-betaTilde beta - 1)

/-- The scalar lower bound behind the first strong-sensitivity threshold.
The three cases are `beta <= 1/2`, `1/2 <= beta <= 1`, and `1 <= beta`. -/
theorem entropyEllipticWeight_lower
    {beta vStar v : ℝ}
    (hbeta : 0 ≤ beta) (hvStar : 0 ≤ vStar) (hv : 0 ≤ v) :
    (1 + betaTilde beta * vStar) * (1 + v) ^ (-2 * beta) ≤
      entropyEllipticWeight beta vStar v := by
  have hbase : 1 ≤ 1 + v := by linarith
  have hbase_pos : 0 < 1 + v := lt_of_lt_of_le zero_lt_one hbase
  by_cases hhalf : beta ≤ 1 / 2
  · have heta : betaTilde beta = 0 :=
      betaTilde_eq_zero_of_beta_le_half hhalf
    rw [entropyEllipticWeight, heta]
    norm_num
    exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  by_cases hone : beta ≤ 1
  · have hmem : beta ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_of_not_ge hhalf, hone⟩
    have heta : betaTilde beta = 2 * beta - 1 :=
      betaTilde_eq_two_mul_sub_one_of_mem_Icc hmem
    rw [entropyEllipticWeight, heta]
    have hpow_split :
        (1 + v) ^ (-(2 * beta - 1)) =
          (1 + v) * (1 + v) ^ (-2 * beta) := by
      calc
        (1 + v) ^ (-(2 * beta - 1)) =
            (1 + v) ^ (1 + (-2 * beta)) := by congr 1 <;> ring
        _ = (1 + v) ^ (1 : ℝ) * (1 + v) ^ (-2 * beta) := by
          rw [Real.rpow_add hbase_pos]
        _ = (1 + v) * (1 + v) ^ (-2 * beta) := by
          rw [Real.rpow_one]
    have hpow_tail :
        (1 + v) ^ (-(2 * beta - 1) - 1) =
          (1 + v) ^ (-2 * beta) := by
      congr 1
      ring
    rw [hpow_split, hpow_tail]
    have hcoef :
        1 + (2 * beta - 1) * vStar ≤
          (1 + v) - (2 * beta - 1) * (v - vStar) := by
      have heta_nonneg : 0 ≤ 2 * beta - 1 := by linarith [hmem.1]
      have heta_le_one : 2 * beta - 1 ≤ 1 := by linarith [hmem.2]
      nlinarith [mul_nonneg (sub_nonneg.mpr heta_le_one) hv]
    have hpow_nonneg : 0 ≤ (1 + v) ^ (-2 * beta) :=
      Real.rpow_nonneg hbase_pos.le _
    nlinarith [mul_le_mul_of_nonneg_right hcoef hpow_nonneg]
  · have hone_le : 1 ≤ beta := le_of_not_ge hone
    have heta : betaTilde beta = 1 :=
      betaTilde_eq_one_of_one_le_beta hone_le
    rw [entropyEllipticWeight, heta]
    norm_num
    have hpow_le :
        (1 + v) ^ (-(2 * beta)) ≤ ((1 + v) ^ (2 : ℕ))⁻¹ := by
      calc
        (1 + v) ^ (-(2 * beta)) ≤ (1 + v) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
        _ = ((1 + v) ^ (2 : ℕ))⁻¹ := by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
            Real.rpow_neg hbase_pos.le, Real.rpow_two]
    have hpow_inv :
        (1 + v)⁻¹ - (v - vStar) * ((1 + v) ^ (2 : ℕ))⁻¹ =
          (1 + vStar) * ((1 + v) ^ (2 : ℕ))⁻¹ := by
      have hne : 1 + v ≠ 0 := ne_of_gt hbase_pos
      field_simp
      ring
    rw [Real.rpow_neg_one]
    calc
      (1 + vStar) * (1 + v) ^ (-(2 * beta)) ≤
          (1 + vStar) * ((1 + v) ^ (2 : ℕ))⁻¹ :=
        mul_le_mul_of_nonneg_left hpow_le (by linarith)
      _ = (1 + v)⁻¹ - (v - vStar) * ((1 + v) ^ (2 : ℕ))⁻¹ :=
        hpow_inv.symm

#print axioms entropyEllipticWeight_lower

end

end ShenWork.Paper3
