import ShenWork.Paper1.WholeLineChiPosCrestGradientBound

/-!
# Crest gradient bound with overshoot (`b > 1`)

`crest_gradient_bound` assumed no overshoot (`b ≤ 1`), so that the reaction
`−u(1−u) ≤ 0` only helped.  But the dynamics spontaneously overshoot
(`max u > 1`, verified numerically; Fable R1), so `b = 1 + δ > 1`.  The reaction
then contributes `−u(1−u) = u(u−1) ≤ b(b−1)` (a small positive term for a small
overshoot), and the crest bound acquires the corresponding correction:

`q ≤ [χ b (b−a) + b(b−1)] / (c − χ(b−a))`   (valid for `c > χ(b−a)`).

This removes the `b ≤ 1` hypothesis, making the crest route applicable to the
actual (overshooting) solution.  As `b → 1` the correction `b(b−1) → 0` and the
bound reduces to `crest_gradient_bound`.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- **Crest gradient bound, overshoot version.**  No `b ≤ 1` hypothesis; the
reaction contributes `b(b−1)` to the numerator. -/
theorem crest_gradient_bound_overshoot
    {q c χ u vz vmu a b : ℝ}
    (hrel : q * (c - χ * vz) = χ * u * vmu - u * (1 - u))
    (hq : 0 ≤ q) (hχ : 0 ≤ χ)
    (hvz : |vz| ≤ b - a) (hvmu : vmu ≤ b - a) (hvmu0 : 0 ≤ vmu)
    (hua : a ≤ u) (hub : u ≤ b) (ha0 : 0 < a) (hb1 : 1 ≤ b)
    (hc : χ * (b - a) < c) :
    q ≤ (χ * b * (b - a) + b * (b - 1)) / (c - χ * (b - a)) := by
  have hab : a ≤ b := hua.trans hub
  have hba : 0 ≤ b - a := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  have hu0 : 0 ≤ u := ha0.le.trans hua
  -- denominator
  have hvz_le : vz ≤ b - a := (abs_le.mp hvz).2
  have hD0 : 0 < c - χ * (b - a) := by linarith
  have hden : c - χ * (b - a) ≤ c - χ * vz := by
    have : χ * vz ≤ χ * (b - a) := mul_le_mul_of_nonneg_left hvz_le hχ
    linarith
  have hden_pos : 0 < c - χ * vz := lt_of_lt_of_le hD0 hden
  -- numerator `= q·(c − χ v_z) ≥ 0`
  have hnum_nonneg : 0 ≤ χ * u * vmu - u * (1 - u) := by
    rw [← hrel]; exact mul_nonneg hq hden_pos.le
  -- chemotaxis part `χ u vmu ≤ χ b (b−a)`
  have hchem_le : χ * u * vmu ≤ χ * b * (b - a) := by
    have h1 : χ * u ≤ χ * b := mul_le_mul_of_nonneg_left hub hχ
    have h2 : χ * u * vmu ≤ χ * b * vmu :=
      mul_le_mul_of_nonneg_right h1 hvmu0
    have h3 : χ * b * vmu ≤ χ * b * (b - a) :=
      mul_le_mul_of_nonneg_left hvmu (mul_nonneg hχ hb0.le)
    exact h2.trans h3
  -- reaction part `−u(1−u) = u(u−1) ≤ b(b−1)`
  have hreact_le : -(u * (1 - u)) ≤ b * (b - 1) := by
    have huu : u * (u - 1) ≤ b * (b - 1) := by nlinarith [hub, hua, ha0, hb1]
    nlinarith [huu]
  have hnum_le : χ * u * vmu - u * (1 - u) ≤ χ * b * (b - a) + b * (b - 1) := by
    linarith
  -- q = num / (c − χ v_z) ≤ [χ b(b−a) + b(b−1)] / (c − χ(b−a))
  have hq_eq : q = (χ * u * vmu - u * (1 - u)) / (c - χ * vz) := by
    rw [← hrel]; field_simp
  rw [hq_eq, div_le_div_iff₀ hden_pos hD0]
  nlinarith [hnum_le, hden, hnum_nonneg,
    mul_nonneg (mul_nonneg hχ hb0.le) hba, mul_nonneg hb0.le (by linarith : (0:ℝ) ≤ b - 1)]

section AxiomAudit

#print axioms crest_gradient_bound_overshoot

end AxiomAudit

end ShenWork.Paper1
