import ShenWork.Paper1.Proposition12PositiveBranchSupercritical

/-!
# Paper 1, Proposition 1.2 — complete

`Proposition12Assembly.lean` reduced the headline to its positive-sensitivity
branch, the negative branch having been discharged by
`Proposition_1_2_negative_branch`.  That remaining branch — `0 < χ < 1/2`,
`m + γ - 1 ≤ α`, uniformly positive datum — is now proved on BOTH exponent
cases: the critical one by the `MChi` rectangle squeeze and the supercritical
one by the exact-equilibrium ceiling.  So the paper's Proposition 1.2 holds
unconditionally.
-/

noncomputable section

namespace ShenWork.Paper1

/-- Paper 1, Proposition 1.2, with no carried hypothesis. -/
theorem Proposition_1_2.unconditional : Proposition_1_2 :=
  Proposition_1_2.of_positive_branch Proposition_1_2_positive_branch

section AxiomAudit

#print axioms Proposition_1_2.unconditional

end AxiomAudit

end ShenWork.Paper1
