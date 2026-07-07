/-
  ShenWork/Paper2/IntervalDomainThm11ChiNegResidualBFormQuant.lean

  Feed the primitive chi-negative coupled-flux local-existence residual from the
  existing B-form quantitative local-existence producers.  The boundary
  min-persistence input is supplied by the committed chi-nonpositive boundary
  limit bridge.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual
import ShenWork.Paper2.IntervalDomainBoundaryChemDivLimit

open ShenWork.IntervalDomain (intervalDomain)
open ShenWork.Paper2.BFormPositiveDatumLocal

noncomputable section

namespace ShenWork.Paper2.ChiNegResidual

/-- The Picard-restart frontier and weak-positive B-form seed produce the
primitive coupled-flux local-existence residual; the boundary-window
min-persistence input is supplied internally from `p.χ₀ ≤ 0`. -/
theorem coupledFluxClassicalLocalExistenceResidual_of_picardFrontier_BForm
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hPF : ThresholdQuantBridge.PicardRestartFrontier p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  quantitativeLocalExistence_of_picardFrontier_boundary_window_chiNonpos_of_BForm
    p (le_of_lt hχ) ha hb hα hγ hPF hBForm

/-- Picard-limit version of the weak-positive B-form residual producer. -/
theorem coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BForm
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  quantitativeLocalExistence_of_picardLimitFrontier_boundary_window_chiNonpos_of_BForm
    p (le_of_lt hχ) ha hb hα hγ hPLF hBForm

/-- Strict-negative headline from the Picard-limit frontier and weak-positive
B-form seed, routed through the primitive coupled-flux local-existence
residual. -/
theorem theorem_1_1_intervalDomain_chiNeg_of_picardLimitFrontier_BForm
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hPLF : ConeQuantBridge.PicardLimitRestartFrontier p)
    (hBForm : PositiveDatumBFormLocalHyp p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hχ ha hb hα hγ
    (coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BForm
      p hχ ha hb hα hγ hPLF hBForm)

section AxiomAudit

#print axioms coupledFluxClassicalLocalExistenceResidual_of_picardFrontier_BForm
#print axioms coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BForm
#print axioms theorem_1_1_intervalDomain_chiNeg_of_picardLimitFrontier_BForm

end AxiomAudit

end ShenWork.Paper2.ChiNegResidual
