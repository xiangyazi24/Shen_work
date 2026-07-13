import ShenWork.Paper3.IntervalDomainEntropyStrong1

/-!
# Positivity of the first strong-logistic entropy rate

This file turns the strict formula threshold `chiStrong1Formula` into the
strictly positive coefficient occurring in the concrete interval entropy
dissipation inequality.  The reduction is stated for the implemented
`m = 1` equation.
-/

namespace ShenWork.Paper3

noncomputable section

/-- Exact entropy-production coefficient in the implemented first strong
logistic branch. -/
def strong1EntropyCoefficient
    (p : CM2Params) (uStar vStar : ℝ) : ℝ :=
  p.b -
    p.χ₀ ^ 2 * p.ν ^ 2 * CAlphaGamma p.α p.γ *
        uStar ^ (2 * p.γ - p.α) /
      (16 * p.μ * (1 + betaTilde p.β * vStar))

/-- The paper's first strict sensitivity threshold makes the exact entropy
coefficient positive when `m = 1`. -/
theorem strong1EntropyCoefficient_pos_of_chi_lt
    (p : CM2Params) {uStar vStar : ℝ}
    (hm : p.m = 1) (hb : 0 < p.b)
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    (hχpos : 0 < p.χ₀)
    (hχ : p.χ₀ < chiStrong1Formula p uStar vStar) :
    0 < strong1EntropyCoefficient p uStar vStar := by
  let factor : ℝ := 1 + betaTilde p.β * vStar
  let upow : ℝ := uStar ^ (2 * p.γ - p.α)
  let source : ℝ := p.ν ^ 2 * CAlphaGamma p.α p.γ * upow
  let scale : ℝ := 16 * factor * p.μ
  let R : ℝ := p.b * (scale / source)
  have hfactor : 0 < factor := by
    dsimp [factor]
    have hmul := mul_nonneg (betaTilde_nonneg p.β) hvStar
    linarith
  have hupow : 0 < upow := by
    exact Real.rpow_pos_of_pos huStar _
  have hsource : 0 < source := by
    exact mul_pos
      (mul_pos (sq_pos_of_pos p.hν) (CAlphaGamma_pos p.hα p.hγ)) hupow
  have hscale : 0 < scale := by
    exact mul_pos (mul_pos (by norm_num) hfactor) p.hμ
  have hR : 0 < R := mul_pos hb (div_pos hscale hsource)
  have hformula : chiStrong1Formula p uStar vStar = Real.sqrt R := by
    unfold chiStrong1Formula
    dsimp [R, scale, source, upow, factor]
    rw [hm]
    norm_num
  rw [hformula] at hχ
  have hsqrtSq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hχsq : p.χ₀ ^ 2 < R := by
    nlinarith [Real.sqrt_nonneg R]
  have hχsource : p.χ₀ ^ 2 * source < p.b * scale := by
    apply (lt_div_iff₀ hsource).mp
    convert hχsq using 1 <;> dsimp [R] <;> field_simp [hsource.ne'] <;> ring
  have hquot : p.χ₀ ^ 2 * source / scale < p.b :=
    (div_lt_iff₀ hscale).2 (by simpa [mul_comm] using hχsource)
  unfold strong1EntropyCoefficient
  dsimp [source, scale, factor, upow] at hquot ⊢
  have hdenEq :
      16 * (1 + betaTilde p.β * vStar) * p.μ =
        16 * p.μ * (1 + betaTilde p.β * vStar) := by ring
  rw [hdenEq] at hquot
  apply sub_pos.mpr
  convert hquot using 1 <;> ring

#print axioms strong1EntropyCoefficient_pos_of_chi_lt

end

end ShenWork.Paper3
