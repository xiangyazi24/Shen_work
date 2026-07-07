/-
  ShenWork/Paper2/IntervalDomainThm11ChiNegResidualBFormSourceFrontier.lean

  Source-frontier variants of the weak-positive B-form residual bridge.
-/
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidualBFormFrontier
import ShenWork.Paper2.IntervalDomainPPIDRestartCoreFrontier

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData picardLimit)
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.Paper2.ChiNegResidual
open ShenWork.Paper2.PPIDThresholdReachability

noncomputable section

namespace ShenWork.Paper2.ChiNegResidual

/-- Source-witness spectral frontier plus the weak-positive B-form frontier
produce the primitive coupled-flux local-existence residual. -/
theorem coupledFluxLocalExistenceResidual_of_sourceSpectral_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSourceSpectralFrontier p D)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BFormFrontier
    p hχ ha hb hα hγ
    (picardLimitRestartFrontier_of_sourceSpectralFrontier hSource)
    hPerDatum

/-- Picard-iterate/source-witness spectral frontier version of the primitive
coupled-flux local-existence residual. -/
theorem coupledFluxLocalExistenceResidual_of_iterateSourceSpectral_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hIterSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSourceSpectralFrontier p D)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    CoupledFluxClassicalLocalExistenceResidual p :=
  coupledFluxClassicalLocalExistenceResidual_of_picardLimitFrontier_BFormFrontier
    p hχ ha hb hα hγ
    (picardLimitRestartFrontier_of_iterateSourceSpectralFrontier hIterSource)
    hPerDatum

/-- Strict-negative headline from source-witness spectral data and the
weak-positive B-form frontier. -/
theorem theorem_1_1_intervalDomain_chiNeg_of_sourceSpectral_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSourceSpectralFrontier p D)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hχ ha hb hα hγ
    (coupledFluxLocalExistenceResidual_of_sourceSpectral_BFormFrontier
      p hχ ha hb hα hγ hSource hPerDatum)

/-- Strict-negative headline from iterate/source-witness spectral data and the
weak-positive B-form frontier. -/
theorem theorem_1_1_intervalDomain_chiNeg_of_iterateSourceSpectral_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hIterSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSourceSpectralFrontier p D)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    p hχ ha hb hα hγ
    (coupledFluxLocalExistenceResidual_of_iterateSourceSpectral_BFormFrontier
      p hχ ha hb hα hγ hIterSource hPerDatum)

end ShenWork.Paper2.ChiNegResidual

namespace ShenWork.Paper2

/-- Chi-nonpositive split from source-witness spectral data and the weak-positive
B-form frontier on the strict-negative branch. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_sourceSpectral_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSourceSpectralFrontier p D)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_coupledFluxLocalExistence_negative
    p hχ ha hb hα hγ
    (fun hneg =>
      coupledFluxLocalExistenceResidual_of_sourceSpectral_BFormFrontier
        p hneg ha hb hα hγ hSource hPerDatum)

/-- Chi-nonpositive split from iterate/source-witness spectral data and the
weak-positive B-form frontier on the strict-negative branch. -/
theorem intervalDomain_theorem_1_1_chiNonpos_of_iterateSourceSpectral_BFormFrontier
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hIterSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSourceSpectralFrontier p D)
    (hPerDatum : BFormPositiveLocalFrontier p) :
    Theorem_1_1 intervalDomain p :=
  intervalDomain_theorem_1_1_chiNonpos_of_coupledFluxLocalExistence_negative
    p hχ ha hb hα hγ
    (fun hneg =>
      coupledFluxLocalExistenceResidual_of_iterateSourceSpectral_BFormFrontier
        p hneg ha hb hα hγ hIterSource hPerDatum)

section AxiomAudit

#print axioms
  coupledFluxLocalExistenceResidual_of_sourceSpectral_BFormFrontier
#print axioms
  coupledFluxLocalExistenceResidual_of_iterateSourceSpectral_BFormFrontier
#print axioms
  theorem_1_1_intervalDomain_chiNeg_of_sourceSpectral_BFormFrontier
#print axioms
  theorem_1_1_intervalDomain_chiNeg_of_iterateSourceSpectral_BFormFrontier
#print axioms intervalDomain_theorem_1_1_chiNonpos_of_sourceSpectral_BFormFrontier
#print axioms
  intervalDomain_theorem_1_1_chiNonpos_of_iterateSourceSpectral_BFormFrontier

end AxiomAudit

end ShenWork.Paper2
