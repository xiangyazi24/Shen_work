import ShenWork.Paper1.WholeLineCauchyNonnegativity
import ShenWork.Paper1.WavePositiveStrictMaximum

open Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Stable-regime ceiling for the whole-line Cauchy problem

At a first contact with a constant upper barrier `M`, the elliptic equation
contributes the exponent `m + gamma - 1` after division by `M`.  Thus the
correct scalar supersolution condition is

`1 + max chi 0 * M^(m + gamma - 1) <= M^alpha`.

The stable negative branch makes the chemotaxis contribution favorable.  In
the nonnegative branch, `alpha = m + gamma - 1` and `chi < 1`, while `MChi`
is the exact positive solution of `(1 - chi) * M^alpha = 1`.
-/

/-- A canonical ceiling above both the initial BUC norm and the stable
constant-state threshold. -/
def wholeLineCauchyStableCeiling
    (p : CMParams) (u₀ : WholeLineBUC) : ℝ :=
  max (‖u₀‖ + 1) (MChi p)

theorem wholeLineCauchyStableCeiling_gt_norm
    (p : CMParams) (u₀ : WholeLineBUC) :
    ‖u₀‖ < wholeLineCauchyStableCeiling p u₀ := by
  unfold wholeLineCauchyStableCeiling
  exact lt_of_lt_of_le (lt_add_one ‖u₀‖) (le_max_left _ _)

theorem wholeLineCauchyStableCeiling_initial_lt
    (p : CMParams) (u₀ : WholeLineBUC) (x : ℝ) :
    u₀.1 x < wholeLineCauchyStableCeiling p u₀ :=
  (WholeLineBUC.apply_le_norm u₀ x).trans_lt
    (wholeLineCauchyStableCeiling_gt_norm p u₀)

theorem wholeLineCauchyStableCeiling_one_le
    {p : CMParams} (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) :
    1 ≤ wholeLineCauchyStableCeiling p u₀ := by
  unfold wholeLineCauchyStableCeiling
  exact hregime.one_le_MChi.trans (le_max_right _ _)

/-- The exact scalar inequality required by the constant upper-barrier
first-contact argument.  In particular, the chemotaxis exponent is
`m + gamma - 1`, not `gamma`. -/
theorem wholeLineCauchyStableCeiling_margin
    {p : CMParams} (hregime : StableWaveParameterRegime p)
    (u₀ : WholeLineBUC) :
    1 + max p.χ 0 *
        (wholeLineCauchyStableCeiling p u₀) ^ (p.m + p.γ - 1) ≤
      (wholeLineCauchyStableCeiling p u₀) ^ p.α := by
  let M := wholeLineCauchyStableCeiling p u₀
  have hM1 : 1 ≤ M := wholeLineCauchyStableCeiling_one_le hregime u₀
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  rcases hregime with hneg | hpos
  · have hpow : 1 ≤ M ^ p.α :=
      Real.one_le_rpow hM1 (zero_le_one.trans p.hα)
    simpa [max_eq_right (le_of_lt hneg.1), M] using hpow
  · have hχ1 : p.χ < 1 :=
      lt_of_lt_of_le hpos.2.1 (chiStar_le_one p)
    have hden : 0 < 1 - p.χ := sub_pos.mpr hχ1
    have hMChi0 : 0 ≤ MChi p :=
      MChi_nonneg_of_chi_lt_one p hχ1
    have hMChiM : MChi p ≤ M := by
      dsimp [M, wholeLineCauchyStableCeiling]
      exact le_max_right _ _
    have hpow_le : (MChi p) ^ p.α ≤ M ^ p.α :=
      Real.rpow_le_rpow hMChi0 hMChiM (zero_le_one.trans p.hα)
    have hthreshold : 1 / (1 - p.χ) ≤ M ^ p.α := by
      rw [← MChi_rpow_alpha_eq_one_div_one_sub_chi p hpos.1 hχ1]
      exact hpow_le
    have hone : 1 ≤ (1 - p.χ) * (M ^ p.α) := by
      calc
        1 = (1 - p.χ) * (1 / (1 - p.χ)) := by
          field_simp
        _ ≤ (1 - p.χ) * (M ^ p.α) :=
          mul_le_mul_of_nonneg_left hthreshold hden.le
    rw [max_eq_left hpos.1, ← hpos.2.2]
    nlinarith

section WholeLineCauchyGlobalBoundsAxiomAudit

#print axioms wholeLineCauchyStableCeiling_initial_lt
#print axioms wholeLineCauchyStableCeiling_one_le
#print axioms wholeLineCauchyStableCeiling_margin

end WholeLineCauchyGlobalBoundsAxiomAudit

end ShenWork.Paper1
