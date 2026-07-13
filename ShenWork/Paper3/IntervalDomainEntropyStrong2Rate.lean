import ShenWork.Paper3.IntervalDomainEntropyStrong2

/-! # Positivity of the second strong-logistic entropy rate -/

namespace ShenWork.Paper3

noncomputable section

/-- The second strict formula threshold makes its exact entropy coefficient
positive on the implemented `m = 1` equation. -/
theorem strong2EntropyCoefficient_pos_of_chi_lt
    (p : CM2Params) {uStar : ℝ}
    (hm : p.m = 1) (ha : 0 < p.a) (hb : 0 < p.b)
    (huStar : 0 < uStar)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong2Formula p uStar) :
    0 < strong2EntropyCoefficient p uStar := by
  let factor : ℝ := (1 + vABLowerFormula p) ^ (2 * p.β)
  let upow : ℝ := uStar ^ (2 * p.γ - p.α)
  let source : ℝ := p.ν ^ 2 * CAlphaGamma p.α p.γ * upow
  let scale : ℝ := 16 * factor * p.μ
  let R : ℝ := p.b * (scale / source)
  have hvAB : 0 ≤ vABLowerFormula p := by
    exact (vABLowerFormula_pos p ha hb (by rw [hm])).le
  have hfactor : 0 < factor :=
    Real.rpow_pos_of_pos (by linarith) _
  have hupow : 0 < upow := Real.rpow_pos_of_pos huStar _
  have hsource : 0 < source :=
    mul_pos (mul_pos (sq_pos_of_pos p.hν)
      (CAlphaGamma_pos p.hα p.hγ)) hupow
  have hscale : 0 < scale :=
    mul_pos (mul_pos (by norm_num) hfactor) p.hμ
  have hR : 0 < R := mul_pos hb (div_pos hscale hsource)
  have hroot : p.χ₀ < Real.sqrt R := by
    have hmin : p.χ₀ < Real.sqrt
        (p.b *
          (16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ /
            ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
              uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)))) :=
      lt_of_lt_of_le hχ (min_le_right _ _)
    rw [hm] at hmin
    norm_num at hmin
    simpa [R, scale, source, upow, factor] using hmin
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hχsq : p.χ₀ ^ 2 < R := by
    nlinarith [Real.sqrt_nonneg R]
  have hχsource : p.χ₀ ^ 2 * source < p.b * scale := by
    apply (lt_div_iff₀ hsource).mp
    convert hχsq using 1 <;> dsimp [R] <;>
      field_simp [hsource.ne'] <;> ring
  have hquot : p.χ₀ ^ 2 * source / scale < p.b :=
    (div_lt_iff₀ hscale).2 (by simpa [mul_comm] using hχsource)
  unfold strong2EntropyCoefficient
  dsimp [source, scale, factor, upow] at hquot ⊢
  have hdenEq : 16 * (1 + vABLowerFormula p) ^ (2 * p.β) * p.μ =
      16 * p.μ * (1 + vABLowerFormula p) ^ (2 * p.β) := by ring
  rw [hdenEq] at hquot
  apply sub_pos.mpr
  convert hquot using 1 <;> ring

#print axioms strong2EntropyCoefficient_pos_of_chi_lt

end

end ShenWork.Paper3
