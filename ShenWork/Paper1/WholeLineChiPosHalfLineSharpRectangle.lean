import ShenWork.Paper1.WholeLineChiPosSharpSqueezeAlgebra

/-!
# Sharp half-line rectangle endgame for `m > 1`

This keeps the small-endpoint factor in the floor budget.  The resulting
affine ratio is

`rho = chi * gamma / (alpha * (1 - chi))`,

so the iteration closes exactly when

`chi * gamma < alpha * (1 - chi)`.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Sharp gap estimate for a buffered half-line rectangle round. -/
theorem ChiPosHalfLineRectangleStep.gap_le_m_gt_one
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ → ℝ} {delta : ℝ}
    {old new : ChiPosHalfLineRectangle p c u}
    (h : ChiPosHalfLineRectangleStep p delta old new)
    (hm : 1 < p.m) (hcritical : p.α = p.m + p.γ - 1)
    (hchi : 0 ≤ p.χ) :
    (1 - p.χ) * (new.M ^ p.α - new.ell ^ p.α) ≤
      p.χ * (p.γ / p.α) *
        (old.M ^ p.α - old.ell ^ p.α) + 2 * delta :=
  chiPos_squeeze_gap_step_m_gt_one hm p.hγ hcritical hchi
    old.ell_pos h.ell_le new.ell_lt_one.le new.one_lt_M.le h.M_le
    h.floor_budget h.ceiling_budget

/-- Endgame for the sharp `m > 1` half-line recurrence.  The product
`chi * gamma` appears only in the numerator of the exact scalar ratio. -/
theorem
    uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_m_gt_one
    (p : CMParams) {c : ℝ} {u : ℝ → ℝ → ℝ}
    (hm : 1 < p.m) (hchi : 0 ≤ p.χ) (hchi_one : p.χ < 1)
    (hcritical : p.α = p.m + p.γ - 1)
    (hcontract : p.χ * p.γ < p.α * (1 - p.χ))
    (seed : ChiPosHalfLineRectangle p c u)
    (hsuccessor : ∀ delta, 0 < delta →
      ∀ old : ChiPosHalfLineRectangle p c u,
        Nonempty {new : ChiPosHalfLineRectangle p c u //
          ChiPosHalfLineRectangleStep p delta old new}) :
    UniformCoMovingLeftEquilibriumConvergence c u := by
  intro epsilon hepsilon
  have halpha : 0 < p.α := zero_lt_one.trans_le p.hα
  have honechi : 0 < 1 - p.χ := sub_pos.mpr hchi_one
  have hden : 0 < p.α * (1 - p.χ) := mul_pos halpha honechi
  let rho : ℝ := p.χ * p.γ / (p.α * (1 - p.χ))
  have hgamma : 0 ≤ p.γ := zero_le_one.trans p.hγ
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    exact div_nonneg (mul_nonneg hchi hgamma) hden.le
  have hrho1 : rho < 1 := by
    dsimp only [rho]
    exact (div_lt_one hden).2 hcontract
  have honeRho : 0 < 1 - rho := sub_pos.mpr hrho1
  let delta : ℝ := epsilon * (1 - p.χ) * (1 - rho) / 4
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  let next : ChiPosHalfLineRectangle p c u →
      ChiPosHalfLineRectangle p c u := fun old =>
    (Classical.choice (hsuccessor delta hdelta old)).1
  have hnext : ∀ old : ChiPosHalfLineRectangle p c u,
      ChiPosHalfLineRectangleStep p delta old (next old) := fun old =>
    (Classical.choice (hsuccessor delta hdelta old)).2
  let rectangles : ℕ → ChiPosHalfLineRectangle p c u := fun n =>
    next^[n] seed
  have hrectangleStep : ∀ n,
      ChiPosHalfLineRectangleStep p delta
        (rectangles n) (rectangles (n + 1)) := by
    intro n
    simpa [rectangles, Function.iterate_succ_apply'] using
      hnext (rectangles n)
  let gap : ℕ → ℝ := fun n =>
    (rectangles n).M ^ p.α - (rectangles n).ell ^ p.α
  have hgapStep : ∀ n,
      gap (n + 1) ≤ rho * gap n + 2 * delta / (1 - p.χ) := by
    intro n
    have hraw := (hrectangleStep n).gap_le_m_gt_one
      hm hcritical hchi
    have hdivide :
        gap (n + 1) ≤
          (p.χ * (p.γ / p.α) * gap n + 2 * delta) /
            (1 - p.χ) := by
      apply (le_div_iff₀ honechi).2
      simpa only [gap, mul_comm (gap (n + 1))] using hraw
    calc
      gap (n + 1) ≤
          (p.χ * (p.γ / p.α) * gap n + 2 * delta) /
            (1 - p.χ) := hdivide
      _ = rho * gap n + 2 * delta / (1 - p.χ) := by
        dsimp only [rho]
        field_simp
  have hc0 : 0 ≤ 2 * delta / (1 - p.χ) := by positivity
  have hstationary :
      (2 * delta / (1 - p.χ)) / (1 - rho) < epsilon := by
    have heq :
        (2 * delta / (1 - p.χ)) / (1 - rho) = epsilon / 2 := by
      dsimp only [delta]
      field_simp
      ring
    rw [heq]
    linarith
  obtain ⟨n, hgap⟩ := exists_index_affine_recurrence_lt
    hrho0 hrho1 hc0 hgapStep hstationary
  refine ⟨-(rectangles n).cut, (rectangles n).start, ?_⟩
  intro t z ht hz
  have hzcut : z ≤ (rectangles n).cut := by
    have := neg_le_neg hz
    simpa using this
  have hrect := (rectangles n).bounds t ht z hzcut
  have habs := abs_sub_one_le_rpow_gap p.hα
    (rectangles n).ell_pos (rectangles n).ell_lt_one.le
    (rectangles n).one_lt_M.le hrect.1 hrect.2
  exact habs.trans_lt hgap

section AxiomAudit

#print axioms ChiPosHalfLineRectangleStep.gap_le_m_gt_one
#print axioms
  uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_m_gt_one

end AxiomAudit

end ShenWork.Paper1
