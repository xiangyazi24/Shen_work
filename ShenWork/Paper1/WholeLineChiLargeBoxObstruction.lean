import ShenWork.Paper1.WholeLineCauchyGlobalBounds

/-!
# Why the box gluing cannot reach `1 ≤ χ` at the critical exponent

The canonical global orbit is built by a segment/restart recursion whose datum
is kept inside ONE reusable box: `wholeLineCauchyGlobalDatum_segment_bounds`
(WholeLineCauchyCanonicalSegments.lean:199) proves the recursion stays below
`wholeLineCauchyStableCeiling`, and the only thing it needs the ceiling regime
for is the scalar first-contact margin

  `1 + max χ 0 * M ^ (m + γ - 1) ≤ M ^ α`

(`wholeLineCauchyStableCeiling_margin`, WholeLineCauchyGlobalBounds.lean:187).

At the CRITICAL exponent `α = m + γ - 1` that margin reads
`1 + χ M ^ α ≤ M ^ α`, i.e. `1 ≤ (1 - χ) M ^ α`, whose right-hand side is
nonpositive as soon as `χ ≥ 1`.  So for `1 ≤ χ` no admissible box height exists
AT ALL — the obstruction is not that we failed to find one.

This is the machine-checked reason the residual window `1 ≤ χ` needs a different
architecture (a maximal solution plus a blow-up alternative, which the source
itself imports by citation), rather than another estimate inside the present
one.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The scalar first-contact margin used by the box recursion. -/
def wholeLineBoxMargin (p : CMParams) (M : ℝ) : Prop :=
  1 + max p.χ 0 * M ^ (p.m + p.γ - 1) ≤ M ^ p.α

/-- At the critical exponent with `1 ≤ χ`, NO height satisfies the box margin:
the inequality reduces to `1 ≤ (1 - χ) M ^ α`, whose right side is `≤ 0`. -/
theorem not_wholeLineBoxMargin_of_one_le_chi_critical
    (p : CMParams) (hχ : 1 ≤ p.χ) (hcritical : p.α = p.m + p.γ - 1)
    {M : ℝ} (hM : 0 < M) :
    ¬ wholeLineBoxMargin p M := by
  intro h
  unfold wholeLineBoxMargin at h
  rw [← hcritical] at h
  have hχ0 : 0 ≤ p.χ := le_trans zero_le_one hχ
  rw [max_eq_left hχ0] at h
  have hpow : 0 < M ^ p.α := Real.rpow_pos_of_pos hM _
  nlinarith [h, hpow, hχ]

/-- Consequently the ceiling regime itself is unavailable there: its critical
branch demands `χ < 1`. -/
theorem not_wholeLineCauchyCeilingRegime_of_one_le_chi_critical
    (p : CMParams) (hχ : 1 ≤ p.χ) (hcritical : p.α = p.m + p.γ - 1)
    (hsuper : ¬ (p.m + p.γ - 1 < p.α)) :
    ¬ WholeLineCauchyCeilingRegime p := by
  intro h
  rcases h with hneg | hpos
  · linarith
  · rcases hpos.2 with hsup | hcrit
    · exact hsuper hsup
    · linarith [hcrit.1]

/-- The obstruction is sharp in `χ`: below one the margin IS satisfiable at the
critical exponent, by any height with `(1 - χ) M ^ α ≥ 1`.  So `χ = 1` is
exactly where the box architecture stops working. -/
theorem wholeLineBoxMargin_of_chi_lt_one_critical
    (p : CMParams) (hχ0 : 0 ≤ p.χ) (hχ : p.χ < 1)
    (hcritical : p.α = p.m + p.γ - 1)
    {M : ℝ} (hM : 1 ≤ M) (hbig : 1 ≤ (1 - p.χ) * M ^ p.α) :
    wholeLineBoxMargin p M := by
  unfold wholeLineBoxMargin
  rw [← hcritical, max_eq_left hχ0]
  nlinarith [hbig]

section AxiomAudit

#print axioms not_wholeLineBoxMargin_of_one_le_chi_critical
#print axioms not_wholeLineCauchyCeilingRegime_of_one_le_chi_critical
#print axioms wholeLineBoxMargin_of_chi_lt_one_critical

end AxiomAudit

end ShenWork.Paper1
