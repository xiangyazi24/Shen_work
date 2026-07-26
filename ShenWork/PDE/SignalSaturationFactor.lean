import Mathlib.Analysis.MeanInequalities

/-!
# Sharp scalar signal-saturation factor

For `β ≥ 1`, the function `z ↦ z (1+z)^(-β)` has the explicit maximum

`σβ = 1` when `β = 1`, and
`σβ = (β-1)^(β-1) / β^β` when `β > 1`.

The proof uses Young's inequality with conjugate exponents
`β` and `β/(β-1)`, so no differentiability or maximizer API is required.
-/

namespace ShenWork

noncomputable section

/-- Sharp upper factor for `z / (1+z)^β` on the nonnegative half-line. -/
def signalSaturationFactor (beta : ℝ) : ℝ :=
  if beta = 1 then 1
  else (beta - 1) ^ (beta - 1) / beta ^ beta

/-- Positivity of the sharp saturation factor in its natural range. -/
theorem signalSaturationFactor_pos
    {beta : ℝ} (hbeta : 1 ≤ beta) :
    0 < signalSaturationFactor beta := by
  by_cases hbeta1 : beta = 1
  · simp [signalSaturationFactor, hbeta1]
  have hbeta' : 1 < beta := lt_of_le_of_ne hbeta (Ne.symm hbeta1)
  rw [signalSaturationFactor, if_neg hbeta1]
  exact div_pos
    (Real.rpow_pos_of_pos (sub_pos.mpr hbeta') _)
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one hbeta') _)

set_option maxHeartbeats 1000000 in
-- Real-power conjugate-exponent normalization is the only expensive step.
/-- Sharp scalar saturation inequality. -/
theorem signal_mul_one_add_rpow_neg_le_factor
    {beta z : ℝ} (hbeta : 1 ≤ beta) (hz : 0 ≤ z) :
    z * (1 + z) ^ (-beta) ≤ signalSaturationFactor beta := by
  by_cases hbeta1 : beta = 1
  · subst beta
    rw [signalSaturationFactor, if_pos rfl,
      Real.rpow_neg_one, ← div_eq_mul_inv]
    exact (div_le_one (by linarith : 0 < 1 + z)).2 (by linarith)
  have hbeta' : 1 < beta := lt_of_le_of_ne hbeta (Ne.symm hbeta1)
  have hbeta0 : 0 < beta := lt_trans zero_lt_one hbeta'
  have hbetam1 : 0 < beta - 1 := sub_pos.mpr hbeta'
  rw [signalSaturationFactor, if_neg hbeta1]
  by_cases hz0 : z = 0
  · subst z
    simp only [zero_mul]
    exact (div_pos
      (Real.rpow_pos_of_pos hbetam1 _)
      (Real.rpow_pos_of_pos hbeta0 _)).le
  have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  let p : ℝ := beta
  let q : ℝ := beta / (beta - 1)
  let A : ℝ := (beta * z) ^ (1 / beta)
  let B : ℝ := (beta / (beta - 1)) ^ ((beta - 1) / beta)
  have hq1 : 1 < q := by
    dsimp [q]
    rw [one_lt_div hbetam1]
    linarith
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hpq : p.HolderConjugate q := by
    rw [Real.holderConjugate_iff]
    refine ⟨hbeta', ?_⟩
    dsimp [p, q]
    field_simp [ne_of_gt hbeta0, ne_of_gt hbetam1]
    ring
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (mul_nonneg hbeta0.le hz) _
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg (div_nonneg hbeta0.le hbetam1.le) _
  have hYoung := Real.young_inequality_of_nonneg hA0 hB0 hpq
  have hAp : A ^ p = beta * z := by
    dsimp [A, p]
    rw [← Real.rpow_mul (mul_nonneg hbeta0.le hz)]
    have hexp : (1 / beta) * beta = 1 := by
      field_simp [ne_of_gt hbeta0]
    rw [hexp, Real.rpow_one]
  have hBq : B ^ q = beta / (beta - 1) := by
    dsimp [B, q]
    rw [← Real.rpow_mul (div_nonneg hbeta0.le hbetam1.le)]
    have hexp :
        ((beta - 1) / beta) * (beta / (beta - 1)) = 1 := by
      field_simp [ne_of_gt hbeta0, ne_of_gt hbetam1]
    rw [hexp, Real.rpow_one]
  have hYoung' : A * B ≤ 1 + z := by
    rw [hAp, hBq] at hYoung
    have hfirst : beta * z / beta = z := by
      field_simp [ne_of_gt hbeta0]
    have hsecond :
        (beta / (beta - 1)) / q = 1 := by
      dsimp [q]
      field_simp [ne_of_gt hbeta0, ne_of_gt hbetam1]
    rw [hfirst, hsecond] at hYoung
    linarith
  have hRaised :
      (A * B) ^ beta ≤ (1 + z) ^ beta :=
    Real.rpow_le_rpow
      (mul_nonneg hA0 hB0) hYoung' hbeta0.le
  have hABpow :
      (A * B) ^ beta =
        (beta * z) * (beta / (beta - 1)) ^ (beta - 1) := by
    rw [Real.mul_rpow hA0 hB0, hAp]
    dsimp [B]
    rw [← Real.rpow_mul (div_nonneg hbeta0.le hbetam1.le)]
    have hexp : ((beta - 1) / beta) * beta = beta - 1 := by
      field_simp [ne_of_gt hbeta0]
    rw [hexp]
  rw [hABpow] at hRaised
  have hfactorScale :
      ((beta - 1) ^ (beta - 1) / beta ^ beta) *
          ((beta * z) *
            (beta / (beta - 1)) ^ (beta - 1)) = z := by
    rw [Real.div_rpow hbeta0.le hbetam1.le]
    have hbetaPow :
        beta ^ beta = beta * beta ^ (beta - 1) := by
      calc
        beta ^ beta = beta ^ ((1 : ℝ) + (beta - 1)) := by ring_nf
        _ = beta ^ (1 : ℝ) * beta ^ (beta - 1) :=
          Real.rpow_add hbeta0 1 (beta - 1)
        _ = beta * beta ^ (beta - 1) := by rw [Real.rpow_one]
    rw [hbetaPow]
    field_simp [
      ne_of_gt hbeta0,
      ne_of_gt hbetam1,
      ne_of_gt (Real.rpow_pos_of_pos hbeta0 (beta - 1)),
      ne_of_gt (Real.rpow_pos_of_pos hbetam1 (beta - 1))]
  have hfactorNonneg :
      0 ≤ (beta - 1) ^ (beta - 1) / beta ^ beta :=
    (div_pos
      (Real.rpow_pos_of_pos hbetam1 _)
      (Real.rpow_pos_of_pos hbeta0 _)).le
  have hmain :
      z ≤ ((beta - 1) ^ (beta - 1) / beta ^ beta) *
          (1 + z) ^ beta := by
    calc
      z = ((beta - 1) ^ (beta - 1) / beta ^ beta) *
          ((beta * z) *
            (beta / (beta - 1)) ^ (beta - 1)) := hfactorScale.symm
      _ ≤ ((beta - 1) ^ (beta - 1) / beta ^ beta) *
          (1 + z) ^ beta :=
        mul_le_mul_of_nonneg_left hRaised hfactorNonneg
  have hbase : 0 < 1 + z := by linarith
  rw [Real.rpow_neg hbase.le, ← div_eq_mul_inv]
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hbase beta)]
  simpa [mul_comm] using hmain

#print axioms signal_mul_one_add_rpow_neg_le_factor

end

end ShenWork
