import ShenWork.Paper1.WholeLineChiPosCeilingRatio
import ShenWork.Paper1.WholeLineChiPosRefinedCeilingSqueeze
import ShenWork.Paper1.WholeLineChiPosHalfLineSharpRectangle

/-!
# Half-line rectangle endgame at the refined ceiling coefficient

Same iteration as `WholeLineChiPosHalfLineSharpRectangle`, but the ceiling
budget is absorbed at a coefficient `c0 ≤ 1` instead of at `1`.  The scalar
recursion becomes

`(1 - chi * c0) * gap (n+1) ≤ chi * (gamma / alpha) * gap n + 2 * delta`,

so the contraction ratio is `rho = chi * (gamma / alpha) / (1 - chi * c0)` and
the iteration closes under

`chi * gamma < alpha * (1 - chi * c0)`,  i.e.  `chi < alpha / (gamma + alpha * c0)`.

At `c0 = 1` this is the existing `chi < alpha / (alpha + gamma)`; as
`c0 ↓ gamma / alpha` it approaches `alpha / (2 * gamma)`.

The ceiling-absorption hypothesis is only ever needed on rectangles lying in
the box cut out by the seed, since `ell` increases and `M` decreases along the
chain — that containment is established here by induction, so the caller need
only supply the absorption for `seed.ell ≤ r.ell` and `r.M ≤ seed.M`.  In
particular a bound depending on the seed aspect ratio `seed.ell / seed.M`
suffices, which is what makes the refinement non-circular.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- Refined gap estimate for a buffered half-line rectangle round. -/
theorem ChiPosHalfLineRectangleStep.gap_le_refined
    {p : CMParams} {c : ℝ} {u : ℝ → ℝ → ℝ} {delta c0 : ℝ}
    {old new : ChiPosHalfLineRectangle p c u}
    (h : ChiPosHalfLineRectangleStep p delta old new)
    (hm : 1 < p.m) (hcritical : p.α = p.m + p.γ - 1)
    (hchi : 0 ≤ p.χ)
    (hceilAbsorb : new.M ^ (p.m - 1) * (new.M ^ p.γ - new.ell ^ p.γ) ≤
      c0 * (new.M ^ p.α - new.ell ^ p.α)) :
    (1 - p.χ * c0) * (new.M ^ p.α - new.ell ^ p.α) ≤
      p.χ * (p.γ / p.α) *
        (old.M ^ p.α - old.ell ^ p.α) + 2 * delta :=
  chiPos_squeeze_gap_step_refined_ceiling hm p.hγ hcritical hchi
    old.ell_pos h.ell_le new.ell_lt_one.le new.one_lt_M.le h.M_le
    hceilAbsorb h.floor_budget h.ceiling_budget

/-- Endgame for the refined `m > 1` half-line recurrence. -/
theorem
    uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_refined
    (p : CMParams) {c : ℝ} {u : ℝ → ℝ → ℝ} {c0 : ℝ}
    (hm : 1 < p.m) (hchi : 0 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (hcontract : p.χ * p.γ < p.α * (1 - p.χ * c0))
    (seed : ChiPosHalfLineRectangle p c u)
    (hceilAbsorb : ∀ r : ChiPosHalfLineRectangle p c u,
      seed.ell ≤ r.ell → r.M ≤ seed.M →
      r.M ^ (p.m - 1) * (r.M ^ p.γ - r.ell ^ p.γ) ≤
        c0 * (r.M ^ p.α - r.ell ^ p.α))
    (hsuccessor : ∀ delta, 0 < delta →
      ∀ old : ChiPosHalfLineRectangle p c u,
        Nonempty {new : ChiPosHalfLineRectangle p c u //
          ChiPosHalfLineRectangleStep p delta old new}) :
    UniformCoMovingLeftEquilibriumConvergence c u := by
  intro epsilon hepsilon
  have halpha : 0 < p.α := zero_lt_one.trans_le p.hα
  have hgamma : 0 ≤ p.γ := zero_le_one.trans p.hγ
  have hchic0 : 0 < 1 - p.χ * c0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg hchi hgamma]
  have hden : 0 < p.α * (1 - p.χ * c0) := mul_pos halpha hchic0
  let rho : ℝ := p.χ * p.γ / (p.α * (1 - p.χ * c0))
  have hrho0 : 0 ≤ rho :=
    div_nonneg (mul_nonneg hchi hgamma) hden.le
  have hrho1 : rho < 1 := (div_lt_one hden).2 hcontract
  have honeRho : 0 < 1 - rho := sub_pos.mpr hrho1
  let delta : ℝ := epsilon * (1 - p.χ * c0) * (1 - rho) / 4
  have hdelta : 0 < delta := by
    dsimp only [delta]; positivity
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
  -- the chain stays inside the seed box, which is what the caller's
  -- absorption hypothesis is stated on
  have hbox : ∀ n, seed.ell ≤ (rectangles n).ell ∧
      (rectangles n).M ≤ seed.M := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, le_rfl⟩
    | succ k ih =>
      exact ⟨ih.1.trans (hrectangleStep k).ell_le,
        (hrectangleStep k).M_le.trans ih.2⟩
  let gap : ℕ → ℝ := fun n =>
    (rectangles n).M ^ p.α - (rectangles n).ell ^ p.α
  have hgapStep : ∀ n,
      gap (n + 1) ≤ rho * gap n + 2 * delta / (1 - p.χ * c0) := by
    intro n
    have hraw := (hrectangleStep n).gap_le_refined hm hcritical hchi
      (hceilAbsorb (rectangles (n + 1)) (hbox (n + 1)).1 (hbox (n + 1)).2)
    have hdivide :
        gap (n + 1) ≤
          (p.χ * (p.γ / p.α) * gap n + 2 * delta) / (1 - p.χ * c0) := by
      apply (le_div_iff₀ hchic0).2
      simpa only [gap, mul_comm (gap (n + 1))] using hraw
    calc
      gap (n + 1) ≤
          (p.χ * (p.γ / p.α) * gap n + 2 * delta) / (1 - p.χ * c0) := hdivide
      _ = rho * gap n + 2 * delta / (1 - p.χ * c0) := by
        dsimp only [rho]
        field_simp
  have hcnst : 0 ≤ 2 * delta / (1 - p.χ * c0) := by positivity
  have hstationary :
      (2 * delta / (1 - p.χ * c0)) / (1 - rho) < epsilon := by
    have heq :
        (2 * delta / (1 - p.χ * c0)) / (1 - rho) = epsilon / 2 := by
      dsimp only [delta]
      field_simp
      ring
    rw [heq]
    linarith
  obtain ⟨n, hgap⟩ := exists_index_affine_recurrence_lt
    hrho0 hrho1 hcnst hgapStep hstationary
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

/-- **The refinement, with the ceiling coefficient discharged.**  The seed's
aspect ratio `t0 = seed.ell / seed.M` alone produces the coefficient
`c0 = (1 - t0 ^ γ) / (1 - t0 ^ α) < 1`, so the caller carries no absorption
hypothesis at all — only the contraction condition at that `c0`. -/
theorem
    uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_seedRatio
    (p : CMParams) {c : ℝ} {u : ℝ → ℝ → ℝ}
    (hm : 1 < p.m) (hchi : 0 ≤ p.χ)
    (hcritical : p.α = p.m + p.γ - 1)
    (seed : ChiPosHalfLineRectangle p c u)
    (hcontract : p.χ * p.γ < p.α *
      (1 - p.χ * ((1 - (seed.ell / seed.M) ^ p.γ) /
        (1 - (seed.ell / seed.M) ^ p.α))))
    (hsuccessor : ∀ delta, 0 < delta →
      ∀ old : ChiPosHalfLineRectangle p c u,
        Nonempty {new : ChiPosHalfLineRectangle p c u //
          ChiPosHalfLineRectangleStep p delta old new}) :
    UniformCoMovingLeftEquilibriumConvergence c u := by
  have hgamma : 0 < p.γ := zero_lt_one.trans_le p.hγ
  have hs : 0 ≤ p.m - 1 := by linarith
  have hsum : (p.m - 1) + p.γ = p.α := by rw [hcritical]; ring
  have hseedM : 0 < seed.M := zero_lt_one.trans seed.one_lt_M
  have ht0 : 0 < seed.ell / seed.M := div_pos seed.ell_pos hseedM
  refine uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_refined
    p hm hchi hcritical hcontract seed ?_ hsuccessor
  intro r hell hM
  have hrM : 0 < r.M := zero_lt_one.trans r.one_lt_M
  have hlt : r.ell < r.M := r.ell_lt_one.trans r.one_lt_M
  have hratio : seed.ell / seed.M ≤ r.ell / r.M := by
    rw [div_le_div_iff₀ hseedM hrM]
    nlinarith [seed.ell_pos, r.ell_pos, hell, hM]
  exact rpow_large_prefactor_gap_le_of_ratio_ge r.ell_pos hlt.le hs hgamma
    hsum ht0 hratio hlt

section AxiomAudit

#print axioms
  uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_seedRatio
#print axioms ChiPosHalfLineRectangleStep.gap_le_refined
#print axioms
  uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors_refined

end AxiomAudit

end ShenWork.Paper1
