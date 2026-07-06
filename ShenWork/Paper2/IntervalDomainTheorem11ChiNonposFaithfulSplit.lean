/-
  ShenWork/Paper2/IntervalDomainTheorem11ChiNonposFaithfulSplit.lean

  Chi-nonpositive split wrapper whose strict-negative branch carries the
  PPID-typed faithful realization frontier rather than the stronger datum-uniform
  construction.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11ChiNonposSplit
import ShenWork.Wiener.EWA.ChiNegStrongFrontierAssembly

open ShenWork.IntervalDomain (intervalDomain)

noncomputable section

namespace ShenWork.Paper2

/-- General chi-nonpositive split with the PPID-typed faithful realization
frontier restricted to the strict-negative branch. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_strongFaithfulFrontier_negative
    (p : CM2Params) (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hnegFrontier :
      p.χ₀ < 0 → ShenWork.EWA.ChiNegStrongFaithfulRealizationFrontier p) :
    Theorem_1_1 intervalDomain p := by
  rcases lt_or_eq_of_le hchi with hneg | hzero
  · exact ShenWork.EWA.chiNeg_theorem_1_1_of_strongFaithfulFrontier
      p hneg ha hb halpha hgamma (hnegFrontier hneg)
  · exact intervalDomain_theorem_1_1_chiZero_unconditional
      p hzero ha hb halpha hgamma

#print axioms intervalDomain_theorem_1_1_chiNonpos_of_strongFaithfulFrontier_negative

end ShenWork.Paper2
