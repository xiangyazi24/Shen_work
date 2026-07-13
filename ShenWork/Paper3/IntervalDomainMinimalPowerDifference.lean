import ShenWork.Paper3.IntervalDomainMinimalPoincare
import ShenWork.Paper2.IntervalDomainL2UEnergyUniformGammaGeOne
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # Power-difference coefficient in the minimal stability argument -/

open Set

namespace ShenWork.Paper3

open ShenWork.Paper2

noncomputable section

/-- The pointwise Lipschitz slope used in Section 8.1. -/
def minimalPowerSlope (p : CM2Params) (uStar uBar : ℝ) : ℝ :=
  if p.γ ≤ 1 then uStar ^ (p.γ - 1) else p.γ * uBar ^ (p.γ - 1)

theorem minimalPowerSlope_pos
    (p : CM2Params) {uStar uBar : ℝ}
    (huStar : 0 < uStar) (huBar : 0 < uBar) :
    0 < minimalPowerSlope p uStar uBar := by
  unfold minimalPowerSlope
  split_ifs
  · exact Real.rpow_pos_of_pos huStar _
  · exact mul_pos p.hγ (Real.rpow_pos_of_pos huBar _)

/-- `GammaMinimalFormula` is the slope times the eventual upper bound. -/
theorem GammaMinimalFormula_eq_slope_mul
    (p : CM2Params) {uStar uBar : ℝ} (huBar : 0 < uBar) :
    GammaMinimalFormula p.γ uStar uBar =
      minimalPowerSlope p uStar uBar * uBar := by
  unfold GammaMinimalFormula minimalPowerSlope
  by_cases hγ : p.γ ≤ 1
  · simp [hγ]
  · simp only [hγ, if_false]
    have hadd := Real.rpow_add huBar (p.γ - 1) 1
    rw [Real.rpow_one] at hadd
    calc
      p.γ * uBar ^ p.γ = p.γ * uBar ^ (p.γ - 1 + 1) := by
        congr 1
        ring
      _ = p.γ * (uBar ^ (p.γ - 1) * uBar) := by rw [hadd]
      _ = p.γ * uBar ^ (p.γ - 1) * uBar := by ring

private theorem rpow_tangent_le
    {γ a b : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hb : 0 < b) (hba : b ≤ a) :
    a ^ γ - b ^ γ ≤ γ * b ^ (γ - 1) * (a - b) := by
  rcases eq_or_lt_of_le hba with rfl | hlt
  · simp
  have hconc : ConcaveOn ℝ (Ici 0) (fun x : ℝ ↦ x ^ γ) :=
    Real.concaveOn_rpow hγ0.le hγ1.le
  have hd : HasDerivAt (fun x : ℝ ↦ x ^ γ)
      (γ * b ^ (γ - 1)) b := by
    simpa [mul_comm] using
      (Real.hasDerivAt_rpow_const (x := b) (p := γ) (Or.inl hb.ne'))
  have hslope := hconc.slope_le_of_hasDerivAt
    (show b ∈ Ici (0 : ℝ) from hb.le)
    (show a ∈ Ici (0 : ℝ) from (hb.trans_le hba).le) hlt hd
  rw [slope_def_field] at hslope
  have hsub : 0 < a - b := sub_pos.mpr hlt
  exact (div_le_iff₀ hsub).mp hslope

/-- For `0 < gamma ≤ 1`, comparison with the fixed positive mass level avoids
the false zero-based Lipschitz estimate. -/
theorem abs_rpow_sub_fixed_le
    {γ z uStar : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hz : 0 ≤ z) (huStar : 0 < uStar) :
    |z ^ γ - uStar ^ γ| ≤
      uStar ^ (γ - 1) * |z - uStar| := by
  rcases le_total z uStar with hzu | huz
  · have hpow : z ^ γ ≤ uStar ^ γ :=
      Real.rpow_le_rpow hz hzu hγ0.le
    let q : ℝ := z / uStar
    have hq0 : 0 ≤ q := div_nonneg hz huStar.le
    have hq1 : q ≤ 1 := (div_le_one huStar).2 hzu
    have hqpow : q ≤ q ^ γ := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge'
          (x := q) (y := 1) (z := γ) hq0 hq1 hγ0.le hγ1)
    have hzrep : z = uStar * q := by
      dsimp [q]
      field_simp [huStar.ne']
    have hzpow : z ^ γ = uStar ^ γ * q ^ γ := by
      rw [hzrep, Real.mul_rpow huStar.le hq0]
    have huadd := Real.rpow_add huStar (γ - 1) 1
    rw [Real.rpow_one] at huadd
    have hscale :
        uStar ^ (γ - 1) * (uStar - z) =
          uStar ^ γ * (1 - q) := by
      calc
        uStar ^ (γ - 1) * (uStar - z) =
            uStar ^ (γ - 1) * uStar * (1 - q) := by
              rw [hzrep]
              ring
        _ = uStar ^ (γ - 1 + 1) * (1 - q) := by rw [huadd]
        _ = uStar ^ γ * (1 - q) := by
          congr 2
          ring
    rw [abs_of_nonpos (sub_nonpos.mpr hpow),
      abs_of_nonpos (sub_nonpos.mpr hzu)]
    rw [show -(z ^ γ - uStar ^ γ) = uStar ^ γ - z ^ γ by ring,
      show -(z - uStar) = uStar - z by ring, hzpow, hscale]
    have hscaled := mul_le_mul_of_nonneg_left hqpow
      (Real.rpow_pos_of_pos huStar γ).le
    nlinarith
  · have hpow : uStar ^ γ ≤ z ^ γ :=
      Real.rpow_le_rpow huStar.le huz hγ0.le
    rw [abs_of_nonneg (sub_nonneg.mpr hpow),
      abs_of_nonneg (sub_nonneg.mpr huz)]
    rcases eq_or_lt_of_le hγ1 with rfl | hγ1lt
    · simp
    · have htan := rpow_tangent_le hγ0 hγ1lt huStar huz
      have hfactor :
          γ * uStar ^ (γ - 1) * (z - uStar) ≤
            uStar ^ (γ - 1) * (z - uStar) := by
        have hpow0 : 0 ≤ uStar ^ (γ - 1) :=
          (Real.rpow_pos_of_pos huStar _).le
        have hsub0 : 0 ≤ z - uStar := sub_nonneg.mpr huz
        nlinarith [mul_nonneg hpow0 hsub0]
      exact htan.trans hfactor

/-- The exact paper coefficient controls every source-power difference on the
eventual box `0 ≤ z ≤ uBar`, provided the conserved mean also lies in it. -/
theorem abs_powerDifference_le_minimalPowerSlope
    (p : CM2Params) {z uStar uBar : ℝ}
    (hz : 0 ≤ z) (hzBar : z ≤ uBar)
    (huStar : 0 < uStar) (huStarBar : uStar ≤ uBar) :
    |z ^ p.γ - uStar ^ p.γ| ≤
      minimalPowerSlope p uStar uBar * |z - uStar| := by
  unfold minimalPowerSlope
  by_cases hγ1 : p.γ ≤ 1
  · rw [if_pos hγ1]
    exact abs_rpow_sub_fixed_le p.hγ hγ1 hz huStar
  · rw [if_neg hγ1]
    exact rpow_lipschitz_on_Icc_zeroM_of_one_le_gamma
      (le_of_not_ge hγ1) (huStar.le.trans huStarBar)
      ⟨hz, hzBar⟩ ⟨huStar.le, huStarBar⟩

/-- Squared form used under the spatial integral. -/
theorem powerDifference_sq_le_minimalPowerSlope_sq
    (p : CM2Params) {z uStar uBar : ℝ}
    (hz : 0 ≤ z) (hzBar : z ≤ uBar)
    (huStar : 0 < uStar) (huStarBar : uStar ≤ uBar) :
    (z ^ p.γ - uStar ^ p.γ) ^ 2 ≤
      minimalPowerSlope p uStar uBar ^ 2 * (z - uStar) ^ 2 := by
  have h := abs_powerDifference_le_minimalPowerSlope
    p hz hzBar huStar huStarBar
  have hslope0 : 0 ≤ minimalPowerSlope p uStar uBar :=
    (minimalPowerSlope_pos p huStar (huStar.trans_le huStarBar)).le
  have hmul0 : 0 ≤ minimalPowerSlope p uStar uBar * |z - uStar| :=
    mul_nonneg hslope0 (abs_nonneg _)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa [sq_abs, mul_pow] using hsq

#print axioms minimalPowerSlope_pos
#print axioms GammaMinimalFormula_eq_slope_mul
#print axioms abs_rpow_sub_fixed_le
#print axioms abs_powerDifference_le_minimalPowerSlope
#print axioms powerDifference_sq_le_minimalPowerSlope_sq

end

end ShenWork.Paper3
