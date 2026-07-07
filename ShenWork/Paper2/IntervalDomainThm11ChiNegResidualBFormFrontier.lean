/-
  ShenWork/Paper2/IntervalDomainThm11ChiNegResidualBFormFrontier.lean

  Feed the primitive chi-negative coupled-flux local-existence residual from
  the weak-positive negative-part B-form classical frontier.
-/
import ShenWork.Paper2.IntervalDomainTheorem11ChiNonposLocalExistenceSplit
import ShenWork.Paper2.IntervalDomainBoundaryChemDivLimit

open ShenWork.IntervalDomain (intervalDomain)
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.Paper2.ChiNegResidual

noncomputable section

namespace ShenWork.Paper2.ChiNegResidual

/-- The Picard-restart frontier and weak-positive negative-part B-form frontier
produce the primitive coupled-flux local-existence residual. -/
theorem coupledFluxClassicalLocalExistenceResidual_of_picardFrontier_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  quantitativeLocalExistence_of_picardFrontier_boundary_window_chiNonpos_of_BForm
    p (le_of_lt hχ) ha hb hα hγ hPF hPerDatum

/-- Picard-limit version of the weak-positive negative-part B-form residual
producer. -/
theorem coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_chiNonpos_of_BForm
    p (le_of_lt hχ) ha hb hα hγ hPLF hPerDatum

/-- Strict-negative headline from the Picard-limit frontier and weak-positive
negative-part B-form frontier. -/
theorem theorem_1_1_intervalDomain_chiNeg_of_picardLimitFrontier_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hχ ha hb hα hγ
    (coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BFormFrontier
      p hχ ha hb hα hγ hPLF hPerDatum)

end ShenWork.Paper2.ChiNegResidual

namespace ShenWork.Paper2

/-- Chi-nonpositive split whose strict-negative branch is supplied by the
Picard-limit restart frontier and weak-positive negative-part B-form frontier. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_picardLimitFrontier_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_coupledFluxLocalExistence_negative
    p hχ ha hb hα hγ
    (fun hneg =>
      coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BFormFrontier
        p hneg ha hb hα hγ hPLF hPerDatum)

/-- Chi-nonpositive split whose strict-negative branch is supplied by the
Picard-restart frontier and weak-positive negative-part B-form frontier. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_picardFrontier_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_coupledFluxLocalExistence_negative
    p hχ ha hb hα hγ
    (fun hneg =>
      coupledFluxClassicalLocalExistenceResidual_of_picardFrontier_BFormFrontier
        p hneg ha hb hα hγ hPF hPerDatum)

section AxiomAudit

#print axioms
  coupledFluxClassicalLocalExistenceResidual_of_picardFrontier_BFormFrontier
#print axioms
  coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BFormFrontier
#print axioms
  theorem_1_1_intervalDomain_chiNeg_of_picardLimitFrontier_BFormFrontier
#print axioms intervalDomain_theorem_1_1_chiNonpos_of_picardLimitFrontier_BFormFrontier
#print axioms intervalDomain_theorem_1_1_chiNonpos_of_picardFrontier_BFormFrontier

end AxiomAudit

end ShenWork.Paper2
