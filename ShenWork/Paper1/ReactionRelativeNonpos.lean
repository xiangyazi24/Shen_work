import ShenWork.Defs

/-!
# Sign of the reaction relative to the plateau

This file isolates the unconditional sign of the nonlinear reaction relative
to the plateau `u = 1`.  It does not assert nonlinear stability at the sharp
chemotactic threshold: that sharp threshold belongs only to the linearized /
quadratic statement.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- For nonnegative `u` and `alpha >= 1`, the displacement `u - 1` and the
power displacement `u ^ alpha - 1` have the same sign.  This nonlinear
reaction fact is unconditional; the sharp chemotactic threshold is claimed
only for the linearized / quadratic statement, not for nonlinear stability. -/
theorem reaction_relative_nonpos
    (u alpha : ℝ) (hu : 0 ≤ u) (halpha : 1 ≤ alpha) :
    0 ≤ (u - 1) * (u ^ alpha - 1) := by
  have halpha0 : 0 ≤ alpha := le_trans zero_le_one halpha
  rcases le_total u 1 with hu1 | h1u
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hu1)
      (sub_nonpos.mpr (Real.rpow_le_one hu hu1 halpha0))
  · exact mul_nonneg (sub_nonneg.mpr h1u)
      (sub_nonneg.mpr (Real.one_le_rpow h1u halpha0))

/-- Multiplying by the nonnegative population gives the corresponding
nonpositive logistic reaction contribution.  This is unconditional in `chi`;
the sharp chemotactic threshold is a linearized / quadratic claim only and is
not asserted here as a nonlinear stability threshold. -/
theorem reaction_relative_source_nonpos
    (u alpha : ℝ) (hu : 0 ≤ u) (halpha : 1 ≤ alpha) :
    (u - 1) * (u * (1 - u ^ alpha)) ≤ 0 := by
  have hrelative := reaction_relative_nonpos u alpha hu halpha
  calc
    (u - 1) * (u * (1 - u ^ alpha)) =
        -(u * ((u - 1) * (u ^ alpha - 1))) := by ring
    _ ≤ 0 := neg_nonpos.mpr (mul_nonneg hu hrelative)

/-- The relative product itself vanishes only at the plateau `u = 1`.
The source in `reaction_relative_source_nonpos` has the additional zero
`u = 0` because it contains a factor `u`.  This is an unconditional nonlinear
reaction statement; the sharp chemotactic threshold remains a claim only for
the linearized / quadratic form. -/
theorem reaction_relative_eq_zero_iff
    (u alpha : ℝ) (hu : 0 ≤ u) (halpha : 1 ≤ alpha) :
    (u - 1) * (u ^ alpha - 1) = 0 ↔ u = 1 := by
  have halpha_pos : 0 < alpha := lt_of_lt_of_le zero_lt_one halpha
  constructor
  · intro hzero
    by_contra hne
    rcases lt_or_gt_of_ne hne with hu1 | h1u
    · have hpow : u ^ alpha < 1 := Real.rpow_lt_one hu hu1 halpha_pos
      have hprod : 0 < (u - 1) * (u ^ alpha - 1) :=
        mul_pos_of_neg_of_neg (sub_neg.mpr hu1) (sub_neg.mpr hpow)
      exact hprod.ne' hzero
    · have hpow : 1 < u ^ alpha := Real.one_lt_rpow h1u halpha_pos
      have hprod : 0 < (u - 1) * (u ^ alpha - 1) :=
        mul_pos (sub_pos.mpr h1u) (sub_pos.mpr hpow)
      exact hprod.ne' hzero
  · rintro rfl
    simp

section AxiomAudit

#print axioms reaction_relative_nonpos
#print axioms reaction_relative_source_nonpos
#print axioms reaction_relative_eq_zero_iff

end AxiomAudit

end ShenWork.Paper1
