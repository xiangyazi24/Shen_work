import ShenWork.Paper1.WholeLineChiPosRectangleWallMOne

/-!
# The rectangle wall `2 χ γ ≥ α` is sharp along the whole `γ = 1` family

`WholeLineChiPosRectangleWallMOne` proves the wall at the single degenerate
point `m = γ = α = 1`, where the exponents are linear and the stationary pair
can be written down exactly.  This file upgrades that to the entire critical
family `γ = 1` (so `α = m`), for every `m > 1`.

Statement: if `2 χ > m` then for all sufficiently small gaps `d` the symmetric
pair

`ell = 1 - d / 2`,  `M = 1 + d / 2`

satisfies BOTH rectangle budgets with `new = old` and with **zero** slack
(`delta = 0`).  So the budget system again has stationary points of arbitrarily
small gap, and the contraction condition `2 χ γ < α` cannot be relaxed by any
rearrangement of the two scalar inequalities.

Both budget estimates reduce to a single Bernoulli inequality: for `1 ≤ m` and
`0 ≤ y ≤ 1`,

`1 - y ^ m ≤ m * (1 - y)`,

used directly for the floor and, after the substitution `y = 1 / x`, for the
ceiling in the form `x ^ m - 1 ≤ m * x ^ (m - 1) * (x - 1)`.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- Bernoulli, in the form needed for the floor budget. -/
theorem one_sub_rpow_le_mul_one_sub {m y : ℝ} (hm : 1 ≤ m)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - y ^ m ≤ m * (1 - y) := by
  have hs : (-1 : ℝ) ≤ y - 1 := by linarith
  have h := one_add_mul_self_le_rpow_one_add hs hm
  have hy : (1 : ℝ) + (y - 1) = y := by ring
  rw [hy] at h
  linarith

/-- The same inequality at the large endpoint, obtained by inverting. -/
theorem rpow_sub_one_le_mul_rpow_sub_one {m x : ℝ} (hm : 1 ≤ m)
    (hx : 1 ≤ x) :
    x ^ m - 1 ≤ m * x ^ (m - 1) * (x - 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 ≤ 1 / x := by positivity
  have hy1 : 1 / x ≤ 1 := by
    rw [div_le_one hx0]; exact hx
  have hbern := one_sub_rpow_le_mul_one_sub hm hy0 hy1
  have hinv : (1 / x) ^ m = 1 / x ^ m := by
    rw [one_div, one_div, Real.inv_rpow hx0.le]
  rw [hinv] at hbern
  have hxm : 0 < x ^ m := Real.rpow_pos_of_pos hx0 m
  have hsplit : x ^ m = x ^ (m - 1) * x := by
    rw [← Real.rpow_add_one hx0.ne' (m - 1)]
    congr 1
    ring
  -- multiply the inverted Bernoulli inequality through by `x ^ m > 0`
  have hmul := mul_le_mul_of_nonneg_left hbern hxm.le
  have hlhs : x ^ m * (1 - 1 / x ^ m) = x ^ m - 1 := by
    field_simp
  have hrhs : x ^ m * (m * (1 - 1 / x)) = m * x ^ (m - 1) * (x - 1) := by
    rw [hsplit]
    field_simp
  rw [hlhs, hrhs] at hmul
  exact hmul

/-- **The wall is sharp along `γ = 1`.**  If `2 χ > m` (i.e. `2 χ γ > α` at the
critical exponent with `γ = 1`), the symmetric pair of gap `d` satisfies both
budgets with `new = old` and zero slack, for every `d` small enough that
`m / 2 ≤ χ * (1 - d / 2) ^ (m - 1)`. -/
theorem chiPos_budget_stationary_gammaOne
    {p : CMParams} (hgamma : p.γ = 1) (halpha : p.α = p.m)
    (hm : 1 ≤ p.m) {d : ℝ} (hd : 0 < d) (hd2 : d < 2)
    (hchi : p.m / 2 ≤ p.χ * (1 - d / 2) ^ (p.m - 1)) :
    1 - (1 - d / 2) ^ p.α ≤
        p.χ * ((1 - d / 2) ^ (p.m - 1) *
          ((1 + d / 2) ^ p.γ - (1 - d / 2) ^ p.γ)) ∧
      (1 + d / 2) ^ p.α - 1 ≤
        p.χ * ((1 + d / 2) ^ (p.m - 1) *
          ((1 + d / 2) ^ p.γ - (1 - d / 2) ^ p.γ)) := by
  have hell0 : (0 : ℝ) ≤ 1 - d / 2 := by linarith
  have hell1 : (1 : ℝ) - d / 2 ≤ 1 := by linarith
  have hM1 : (1 : ℝ) ≤ 1 + d / 2 := by linarith
  have hgap : (1 + d / 2) ^ p.γ - (1 - d / 2) ^ p.γ = d := by
    rw [hgamma, Real.rpow_one, Real.rpow_one]; ring
  constructor
  · -- floor: `1 - ell ^ m ≤ m * (1 - ell) = m * d / 2 ≤ chi * ell ^ (m-1) * d`
    rw [halpha, hgap]
    have hb := one_sub_rpow_le_mul_one_sub hm hell0 hell1
    have hstep : p.m * (1 - (1 - d / 2)) = p.m * d / 2 := by ring
    rw [hstep] at hb
    nlinarith [hb, hchi, hd]
  · -- ceiling: `M ^ m - 1 ≤ m * M ^ (m-1) * (d/2) ≤ chi * M ^ (m-1) * d`
    rw [halpha, hgap]
    have hb := rpow_sub_one_le_mul_rpow_sub_one hm hM1
    have hstep : (1 : ℝ) + d / 2 - 1 = d / 2 := by ring
    rw [hstep] at hb
    have hMpos : (0 : ℝ) < (1 + d / 2) ^ (p.m - 1) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hA0pos : (0 : ℝ) < (1 - d / 2) ^ (p.m - 1) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hA0le : (1 - d / 2) ^ (p.m - 1) ≤ 1 :=
      Real.rpow_le_one hell0 hell1 (by linarith)
    have hchipos : 0 < p.χ := by nlinarith [hchi, hA0pos, hm]
    have hchi2 : p.m / 2 ≤ p.χ := by nlinarith [hchi, hA0le, hchipos]
    have hslack : 0 ≤ (p.χ - p.m / 2) * ((1 + d / 2) ^ (p.m - 1) * d) :=
      mul_nonneg (by linarith) (mul_nonneg hMpos.le hd.le)
    nlinarith [hb, hslack]

section AxiomAudit

#print axioms one_sub_rpow_le_mul_one_sub
#print axioms rpow_sub_one_le_mul_rpow_sub_one
#print axioms chiPos_budget_stationary_gammaOne

end AxiomAudit

end ShenWork.Paper1
