import ShenWork.Paper1.WholeLineChiPosHalfLineRectangle

/-!
# The rectangle method's wall at `m = γ = 1`

For `m > 1` the sharp/refined squeeze pushes the contraction threshold from
`chi < 1 / 2` up to `chi < alpha / (alpha + gamma)` and (with an explicit seed
aspect ratio) toward `chi < alpha / (2 * gamma)`.  Both improvements are driven
by the small-endpoint factor `ell ^ (m - 1)`, which is identically `1` when
`m = 1`.

This file records, as a theorem rather than as a remark, that at the degenerate
exponents `m = γ = α = 1` the wall at `chi = 1 / 2` is a genuine property of the
budget system and not an artifact of how the budgets are combined: for every
`chi ≥ 1 / 2`, every slack `delta > 0` and every gap `d`, the pair

`ell = 1 - d / 2`,  `M = 1 + d / 2`

satisfies BOTH budgets with `new = old`.  So the budget system admits
stationary points of arbitrary gap, and no combination of the two scalar
inequalities can force the gap to contract.

This is the `m = 1` case of the general wall `2 * chi * gamma < alpha`: at
`m = γ = α = 1` that reads `chi < 1 / 2`.  Note `chiStar p = 1` there, so the
window genuinely left open by the rectangle method at `m = γ = 1` is the whole
of `[1 / 2, 1)`.  Closing it requires a different mechanism (a near-equilibrium
spectral / Liouville argument), not a better rearrangement of these budgets.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- At `m = γ = α = 1` and `chi ≥ 1 / 2` the two rectangle budgets admit a
STATIONARY pair of arbitrary gap `d`: the same `(ell, M)` serves as both the old
and the new rectangle. -/
theorem chiPos_budget_stationary_of_half_le_chi
    {p : CMParams} (hm : p.m = 1) (hgamma : p.γ = 1) (halpha : p.α = 1)
    (hchi : (1 : ℝ) / 2 ≤ p.χ) {delta d : ℝ} (hdelta : 0 < delta)
    (hd : 0 < d) (hd2 : d < 2) :
    ∃ ell M : ℝ, 0 < ell ∧ ell < 1 ∧ 1 < M ∧ M - ell = d ∧
      1 - ell ^ p.α ≤
        p.χ * (ell ^ (p.m - 1) * (M ^ p.γ - ell ^ p.γ)) + delta ∧
      M ^ p.α - 1 ≤
        p.χ * (M ^ (p.m - 1) * (M ^ p.γ - ell ^ p.γ)) + delta := by
  refine ⟨1 - d / 2, 1 + d / 2, by linarith, by linarith, by linarith,
    by ring, ?_, ?_⟩
  · have hell : (0 : ℝ) < 1 - d / 2 := by linarith
    have hM : (0 : ℝ) < 1 + d / 2 := by linarith
    rw [hm, hgamma, halpha]
    simp only [sub_self, Real.rpow_zero, Real.rpow_one, one_mul]
    nlinarith
  · have hell : (0 : ℝ) < 1 - d / 2 := by linarith
    have hM : (0 : ℝ) < 1 + d / 2 := by linarith
    rw [hm, hgamma, halpha]
    simp only [sub_self, Real.rpow_zero, Real.rpow_one, one_mul]
    nlinarith

/-- Consequently the combined budget inequality carries no information about
the gap once `chi ≥ 1 / 2` at these exponents: the standard combination
`(1 - 2 * chi) * gap ≤ 2 * delta` holds for every gap. -/
theorem chiPos_combined_budget_vacuous_of_half_le_chi
    {chi delta gap : ℝ} (hchi : (1 : ℝ) / 2 ≤ chi) (hdelta : 0 < delta)
    (hgap : 0 ≤ gap) :
    (1 - 2 * chi) * gap ≤ 2 * delta := by
  nlinarith

section AxiomAudit

#print axioms chiPos_budget_stationary_of_half_le_chi
#print axioms chiPos_combined_budget_vacuous_of_half_le_chi

end AxiomAudit

end ShenWork.Paper1
