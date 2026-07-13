import ShenWork.Paper3.ThresholdOrdering
import Mathlib.Analysis.MeanInequalities

/-! # The minimal-model half-threshold lies below the spectral threshold -/

namespace ShenWork.Paper3

open ShenWork.Paper2

noncomputable section

/-- The elementary coefficient inequality used in Lemma A.8. -/
private theorem two_beta_sub_one_le_youngCoefficient
    {beta : ℝ} (hbeta : 1 ≤ beta) :
    2 * beta - 1 ≤ beta * (beta / (beta - 1)) ^ (beta - 1) := by
  rcases eq_or_lt_of_le hbeta with rfl | hbeta
  · norm_num
  have hbeta0 : 0 < beta := lt_trans zero_lt_one hbeta
  have hsub0 : 0 < beta - 1 := sub_pos.mpr hbeta
  let q : ℝ := (beta - 1) / beta
  have hq0 : 0 < q := div_pos hsub0 hbeta0
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hbeta0]
    linarith
  have hweight0 : 0 ≤ 1 / beta := by positivity
  have hweights : q + 1 / beta = 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
    ring
  have hqplus0 : 0 ≤ 1 + q := by linarith
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    hq0.le hweight0 hq0.le hqplus0 hweights
  have harith : q * q + (1 / beta) * (1 + q) = 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
    ring
  rw [harith] at hamgm
  have hleft0 : 0 ≤ q ^ q * (1 + q) ^ (1 / beta) :=
    mul_nonneg (Real.rpow_nonneg hq0.le _) (Real.rpow_nonneg hqplus0 _)
  have hraised := Real.rpow_le_rpow hleft0 hamgm hbeta0.le
  have hqmul : q * beta = beta - 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
  have hinvmul : (1 / beta) * beta = 1 := by
    field_simp [hbeta0.ne']
  have hpower :
      (q ^ q * (1 + q) ^ (1 / beta)) ^ beta =
        q ^ (beta - 1) * (1 + q) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hq0.le _)
        (Real.rpow_nonneg hqplus0 _),
      ← Real.rpow_mul hq0.le, ← Real.rpow_mul hqplus0,
      hqmul, hinvmul, Real.rpow_one]
  have hqbound : q ^ (beta - 1) * (1 + q) ≤ 1 := by
    rw [hpower] at hraised
    simpa using hraised
  have hqpow0 : 0 < q ^ (beta - 1) := Real.rpow_pos_of_pos hq0 _
  have hratio : 1 + q ≤ (q ^ (beta - 1))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hqpow0]
    simpa [mul_comm] using hqbound
  have hbase : beta / (beta - 1) = q⁻¹ := by
    dsimp [q]
    field_simp [hbeta0.ne', hsub0.ne']
  have hcoef : 1 + q ≤ (beta / (beta - 1)) ^ (beta - 1) := by
    rw [hbase, Real.inv_rpow hq0.le]
    exact hratio
  have hidentity : beta * (1 + q) = 2 * beta - 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
    ring
  rw [← hidentity]
  exact mul_le_mul_of_nonneg_left hcoef hbeta0.le

/-- For `beta ≥ 1`, the coefficient occurring in the minimal threshold obeys
`(2 beta - 1) v ≤ (1+v)^beta` for every nonnegative signal level. -/
theorem two_beta_sub_one_mul_le_one_add_rpow
    {beta v : ℝ} (hbeta : 1 ≤ beta) (hv : 0 ≤ v) :
    (2 * beta - 1) * v ≤ (1 + v) ^ beta := by
  rcases eq_or_lt_of_le hbeta with rfl | hbeta
  · norm_num
  have hbeta0 : 0 < beta := lt_trans zero_lt_one hbeta
  have hsub0 : 0 < beta - 1 := sub_pos.mpr hbeta
  let q : ℝ := (beta - 1) / beta
  have hq0 : 0 < q := div_pos hsub0 hbeta0
  have hweight0 : 0 ≤ 1 / beta := by positivity
  have hweights : q + 1 / beta = 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
    ring
  have hpone0 : 0 ≤ beta / (beta - 1) := (div_pos hbeta0 hsub0).le
  have hptwo0 : 0 ≤ beta * v := mul_nonneg hbeta0.le hv
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    hq0.le hweight0 hpone0 hptwo0 hweights
  have harith :
      q * (beta / (beta - 1)) + (1 / beta) * (beta * v) = 1 + v := by
    dsimp [q]
    field_simp [hbeta0.ne', hsub0.ne']
  rw [harith] at hamgm
  have hleft0 :
      0 ≤ (beta / (beta - 1)) ^ q * (beta * v) ^ (1 / beta) :=
    mul_nonneg (Real.rpow_nonneg hpone0 _ ) (Real.rpow_nonneg hptwo0 _)
  have hraised := Real.rpow_le_rpow hleft0 hamgm hbeta0.le
  have hqmul : q * beta = beta - 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
  have hinvmul : (1 / beta) * beta = 1 := by
    field_simp [hbeta0.ne']
  have hpower :
      ((beta / (beta - 1)) ^ q * (beta * v) ^ (1 / beta)) ^ beta =
        (beta / (beta - 1)) ^ (beta - 1) * (beta * v) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hpone0 _)
        (Real.rpow_nonneg hptwo0 _),
      ← Real.rpow_mul hpone0, ← Real.rpow_mul hptwo0,
      hqmul, hinvmul, Real.rpow_one]
  have hyoung :
      (beta / (beta - 1)) ^ (beta - 1) * (beta * v) ≤
        (1 + v) ^ beta := by
    rw [hpower] at hraised
    exact hraised
  have hcoef := two_beta_sub_one_le_youngCoefficient hbeta.le
  have hscaled := mul_le_mul_of_nonneg_right hcoef hv
  calc
    (2 * beta - 1) * v ≤
        (beta * (beta / (beta - 1)) ^ (beta - 1)) * v := hscaled
    _ = (beta / (beta - 1)) ^ (beta - 1) * (beta * v) := by ring
    _ ≤ (1 + v) ^ beta := hyoung

#print axioms two_beta_sub_one_mul_le_one_add_rpow

end

end ShenWork.Paper3
