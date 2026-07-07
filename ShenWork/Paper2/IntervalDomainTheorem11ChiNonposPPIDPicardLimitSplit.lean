/-
  ShenWork/Paper2/IntervalDomainTheorem11ChiNonposPPIDPicardLimitSplit.lean

  Chi-nonpositive split wrapper whose strict-negative branch consumes only the
  PPID Picard-limit restart frontier.

  Proof-placeholder free.
-/
import ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
import ShenWork.Paper2.IntervalDomainPPIDPicardLimitFrontier

open ShenWork.IntervalDomain (intervalDomain)

noncomputable section

namespace ShenWork.Paper2

/-- General chi-nonpositive split with the PPID Picard-limit restart frontier
restricted to the strict-negative branch.

The zero branch is the unconditional chi-zero interval-domain theorem.  The
strict-negative branch uses the shortest current PPID Theorem 1.1 wrapper and
does not carry the weak-positive B-form local seed. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_ppid_picardLimitFrontier_negative
    (p : CM2Params) (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hnegPLF : p.χ₀ < 0 → ConeQuantBridge.PicardLimitRestartFrontier p) :
    Theorem_1_1 intervalDomain p := by
  rcases lt_or_eq_of_le hchi with hneg | hzero
  · exact PPIDThresholdReachability.theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNeg
      p hneg ha hb halpha hgamma (hnegPLF hneg)
  · exact intervalDomain_theorem_1_1_chiZero_unconditional
      p hzero ha hb halpha hgamma

#print axioms intervalDomain_theorem_1_1_chiNonpos_of_ppid_picardLimitFrontier_negative

end ShenWork.Paper2
