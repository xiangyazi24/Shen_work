/-
  ShenWork/Paper2/IntervalDomainChiNonposHeadline.lean

  Public chi-nonpositive interval-domain headline wrappers.
  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11ChiNonposLocalExistenceSplit
import ShenWork.Paper2.IntervalDomainTheorem11ChiNonposFaithfulSplit

open ShenWork.IntervalDomain (intervalDomain)

noncomputable section

namespace ShenWork.Paper2

/-- Public PDE-level chi-nonpositive interval-domain theorem in the strict
logistic regime.  The zero branch is unconditional; the strict-negative branch
carries the current primitive coupled-flux local-existence residual.

Scope: `intervalDomain`, chi-nonpositive, `0 < a`, `0 < b`, `1 <= alpha`,
`1 <= gamma`. This is not an unconditional chi-negative theorem. -/
theorem paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_coupledFluxLocalExistence
    (p : CM2Params) (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hnegLocal :
      p.χ₀ < 0 →
        ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_coupledFluxLocalExistence_negative
    p hchi ha hb halpha hgamma hnegLocal

/-- Public route-facing chi-nonpositive interval-domain theorem in the strict
logistic regime.  The zero branch is unconditional; the strict-negative branch
carries the current PPID-typed faithful EWA realization frontier.

Scope: `intervalDomain`, chi-nonpositive, `0 < a`, `0 < b`, `1 <= alpha`,
`1 <= gamma`. This is not an unconditional chi-negative theorem. -/
theorem paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_strongFaithfulFrontier
    (p : CM2Params) (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hnegFrontier :
      p.χ₀ < 0 → ShenWork.EWA.ChiNegStrongFaithfulRealizationFrontier p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_strongFaithfulFrontier_negative
    p hchi ha hb halpha hgamma hnegFrontier

/-- Abstract-core variant of the chi-nonpositive interval-domain split.
This is logically weaker as a theorem hypothesis, but it is EWA-free: it assumes
plain `CoupledDuhamelReducedClassicalCore` data on a uniform lifespan rather than
realized EWA data. -/
theorem paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_uniformCore
    (p : CM2Params) (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hnegCore : p.χ₀ < 0 → ShenWork.ChiNegDatumUniformCore p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_uniformCore_negative
    p hchi ha hb halpha hgamma hnegCore

#print axioms
  paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_coupledFluxLocalExistence
#print axioms
  paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_strongFaithfulFrontier
#print axioms
  paper2_theorem_1_1_intervalDomain_chiNonpos_strictLogistic_of_uniformCore

end ShenWork.Paper2
