import ShenWork.Paper1.WholeLineChiPosHalfLineTargets

open Real

noncomputable section

namespace ShenWork.Paper1

/-!
# A quantified positive floor at a prescribed ceiling

The target below is an explicit subcritical point for the floor reaction
budget, including the half-kernel tail.  Its size depends only on the equation
parameters and the prescribed ceiling, rather than on the initial datum.
-/

/-- For `m > 1`, the half-kernel floor reserve at a ceiling `Q > 1` has an
explicitly positive target.  The last two conjuncts identify the positive
datum-independent lower floor which will be used by the restarted seed. -/
theorem exists_chiPos_quantified_floor_with_halfKernel_reserve
    (p : CMParams) (hm : 1 < p.m) (hchi : 0 ≤ p.χ)
    (Q : ℝ) (hQ : 1 < Q) :
    ∃ ell : ℝ, 0 < ell ∧ ell < 1 ∧
      0 < chiPosFloorGap p Q ell -
        p.χ * ell ^ (p.m - 1) * (1 / 2 : ℝ) * Q ^ p.γ ∧
      0 <
        min (1 / 4 : ℝ)
            ((1 / (8 * (1 + p.χ * Q ^ p.γ))) ^ (1 / (p.m - 1))) / 2 ∧
      min (1 / 4 : ℝ)
            ((1 / (8 * (1 + p.χ * Q ^ p.γ))) ^ (1 / (p.m - 1))) / 2 < ell := by
  let X : ℝ := p.χ * Q ^ p.γ
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ.le
  have hX : 0 ≤ X := mul_nonneg hchi (Real.rpow_nonneg hQ0 _)
  have hden : 0 < 8 * (1 + X) :=
    mul_pos (by norm_num) (by linarith)
  have hbase : 0 < 1 / (8 * (1 + X)) := one_div_pos.mpr hden
  have hm1 : 0 < p.m - 1 := sub_pos.mpr hm
  let root : ℝ := (1 / (8 * (1 + X))) ^ (1 / (p.m - 1))
  have hroot : 0 < root := by
    dsimp [root]
    exact Real.rpow_pos_of_pos hbase _
  let ell : ℝ := min (1 / 4 : ℝ) root
  have hellpos : 0 < ell := by
    dsimp [ell]
    exact lt_min (by norm_num) hroot
  have hellquarter : ell ≤ 1 / 4 := by
    dsimp [ell]
    exact min_le_left _ _
  have hellroot : ell ≤ root := by
    dsimp [ell]
    exact min_le_right _ _
  have hellone : ell ≤ 1 := hellquarter.trans (by norm_num)
  have hellalpha : ell ^ p.α ≤ ell :=
    Real.rpow_le_self_of_le_one hellpos.le hellone p.hα
  have hrootpow : root ^ (p.m - 1) = 1 / (8 * (1 + X)) := by
    dsimp [root]
    simpa [one_div] using Real.rpow_inv_rpow hbase.le hm1.ne'
  have hellpow : ell ^ (p.m - 1) ≤ 1 / (8 * (1 + X)) := by
    calc
      ell ^ (p.m - 1) ≤ root ^ (p.m - 1) :=
        Real.rpow_le_rpow hellpos.le hellroot hm1.le
      _ = 1 / (8 * (1 + X)) := hrootpow
  have hXbound : X * ell ^ (p.m - 1) ≤ 1 / 8 := by
    have hmul := mul_le_mul_of_nonneg_left hellpow hX
    have hratio : X * (1 / (8 * (1 + X))) ≤ 1 / 8 := by
      have hratio' : X / (8 * (1 + X)) ≤ 1 / 8 := by
        apply (div_le_iff₀ hden).2
        nlinarith
      simpa [div_eq_mul_inv, one_div] using hratio'
    exact hmul.trans hratio
  have hsmall :
      ell ^ p.α + (3 / 2 : ℝ) * X * ell ^ (p.m - 1) < 1 := by
    have ha : ell ^ p.α ≤ 1 / 4 := hellalpha.trans hellquarter
    nlinarith
  have hreserve :
      0 < chiPosFloorGap p Q ell -
        p.χ * ell ^ (p.m - 1) * (1 / 2 : ℝ) * Q ^ p.γ := by
    have hellgamma : 0 ≤ ell ^ p.γ := Real.rpow_nonneg hellpos.le _
    have hcorrection :
        0 ≤ p.χ * (ell ^ (p.m - 1) * ell ^ p.γ) :=
      mul_nonneg hchi
        (mul_nonneg (Real.rpow_nonneg hellpos.le _) hellgamma)
    dsimp [X] at hsmall
    unfold chiPosFloorGap
    nlinarith
  refine ⟨ell, hellpos, hellquarter.trans_lt (by norm_num), hreserve, ?_, ?_⟩
  · change 0 < ell / 2
    exact div_pos hellpos (by norm_num)
  · change ell / 2 < ell
    linarith

section AxiomAudit

#print axioms exists_chiPos_quantified_floor_with_halfKernel_reserve

end AxiomAudit

end ShenWork.Paper1
