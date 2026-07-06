import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
import ShenWork.Paper2.IntervalDomainTheorem11CorePath
import ShenWork.Paper2.IntervalDomainTheorem11StrongPath

/-!
  # χ₀≤0 split wrappers for Paper 2 Theorem 1.1

  The χ₀=0 interval-domain headline is now unconditional.  These wrappers expose
  the faithful remaining frontier: only the strict-negative branch still carries
  a chi-negative residual.
-/

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2

/-- General χ₀≤0 split with the EWA-free uniform-core residual restricted to the
strict-negative branch. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_uniformCore_negative
    (p : CM2Params) (hχ : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hnegCore : p.χ₀ < 0 → ShenWork.ChiNegDatumUniformCore p) :
    Theorem_1_1 intervalDomain p := by
  rcases lt_or_eq_of_le hχ with hneg | hzero
  · exact ShenWork.chiNeg_theorem_1_1_of_uniformCore
      p hneg ha hb hα hγ (hnegCore hneg)
  · exact intervalDomain_theorem_1_1_chiZero_unconditional
      p hzero ha hb hα hγ

/-- General χ₀≤0 split with the advertised strong EWA residual restricted to the
strict-negative branch. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_strong_negative
    (p : CM2Params) (hχ : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hnegStrong :
      p.χ₀ < 0 → ShenWork.EWA.ChiNegDatumUniformConstructionStrong p) :
    Theorem_1_1 intervalDomain p := by
  rcases lt_or_eq_of_le hχ with hneg | hzero
  · exact StrongPath.chiNeg_theorem_1_1_of_strong
      p hneg ha hb hα hγ (hnegStrong hneg)
  · exact intervalDomain_theorem_1_1_chiZero_unconditional
      p hzero ha hb hα hγ

section AxiomAudit

#print axioms intervalDomain_theorem_1_1_chiNonpos_of_uniformCore_negative
#print axioms intervalDomain_theorem_1_1_chiNonpos_of_strong_negative

end AxiomAudit

end ShenWork.Paper2
