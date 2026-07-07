/-
  ShenWork/Paper2/IntervalDomainTheorem11ChiNonposLocalExistenceSplit.lean

  Chi-nonpositive split whose strict-negative branch carries the primitive
  coupled-flux classical local-existence residual.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

open ShenWork.IntervalDomain (intervalDomain)
open ShenWork.Paper2.ChiNegResidual

noncomputable section

namespace ShenWork.Paper2

/-- General chi-nonpositive split with the primitive coupled-flux local-existence
residual restricted to the strict-negative branch.

This is the most direct current PDE-level exit: the zero branch is unconditional,
and the negative branch asks only for the local-existence factory consumed by the
existing chi-negative assembly.  It does not pass through the all-PPID
uniform-floor/Wiener interfaces, which are known dead routes. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_coupledFluxLocalExistence_negative
    (p : CM2Params) (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hnegLocal :
      p.χ₀ < 0 → CoupledFluxClassicalLocalExistenceResidual p) :
    Theorem_1_1 intervalDomain p := by
  rcases lt_or_eq_of_le hchi with hneg | hzero
  · exact theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
      p hneg ha hb halpha hgamma (hnegLocal hneg)
  · exact intervalDomain_theorem_1_1_chiZero_unconditional
      p hzero ha hb halpha hgamma

#print axioms intervalDomain_theorem_1_1_chiNonpos_of_coupledFluxLocalExistence_negative

end ShenWork.Paper2
