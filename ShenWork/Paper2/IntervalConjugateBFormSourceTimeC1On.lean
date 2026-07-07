/-
  B-form source time-regularity for the conjugate Picard limit.

  This is a residual combiner for the `BFormBankedInputs.hsrcBDirect` shape,
  reduced to two genuine source-regularity inputs:
  * a logistic-source `DuhamelSourceTimeC1On` package for the conjugate limit;
  * the existing generic chem-div regularity residual, instantiated at the same
    conjugate limit.

  The chem-div half is discharged through the committed residual chain, not by
  assuming a gradient-solution convenience wrapper.
-/
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalChemDivWinDischarge

open Set

noncomputable section

namespace ShenWork.Paper2.ConjugateBFormSourceTimeC1On

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (conjugatePicardLimit)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalBFormSpectral
  (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledChemDivSourceCoeffs)
open ShenWork.IntervalChemDivWinDischarge
  (ChemDivSolutionRegularityResidual
   coupledChemDivSource_duhamelSourceTimeC1_of_residual)

/-- Chem-div source `DuhamelSourceTimeC1On` for the conjugate Picard limit from
the existing generic chem-div regularity residual. -/
noncomputable def conjugatePicardLimit_chemDivSource_timeC1On_of_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (R : ChemDivSolutionRegularityResidual p (conjugatePicardLimit p u₀ T)) :
    DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ T)) 0 T :=
  ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1.toOn
    (coupledChemDivSource_duhamelSourceTimeC1_of_residual R) 0 T le_rfl

/-- B-form source `DuhamelSourceTimeC1On` for the conjugate Picard limit from a
logistic source package plus the existing chem-div regularity residual.

This does not produce the logistic package from bare Picard data.  It only
removes the chem-div convenience-layer mismatch and exposes the two actual
source frontiers: limit logistic source regularity and chem-div regularity of
the same trajectory. -/
noncomputable def conjugatePicardLimit_bFormSource_timeC1On_of_logistic_and_chemDivResidual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hlog_on : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ T)) 0 T)
    (Rchem : ChemDivSolutionRegularityResidual p (conjugatePicardLimit p u₀ T)) :
    DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T)) 0 T := by
  have hchem_on : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ T)) 0 T :=
    conjugatePicardLimit_chemDivSource_timeC1On_of_residual
      (p := p) (u₀ := u₀) (T := T) Rchem
  exact bFormSource_duhamelSourceTimeC1On hlog_on hchem_on

#print axioms conjugatePicardLimit_chemDivSource_timeC1On_of_residual
#print axioms conjugatePicardLimit_bFormSource_timeC1On_of_logistic_and_chemDivResidual

end ShenWork.Paper2.ConjugateBFormSourceTimeC1On
