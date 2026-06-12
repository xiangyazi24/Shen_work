import ShenWork.PDE.IntervalChemDivFluxFactorFAC

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.IntervalMildSourceDecayHelper

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- End-to-end source-time-`C¹` wiring from the FAC factor producer. -/
noncomputable def coupledChemDivSource_timeC1_of_FACInputs
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (Cchem : ℝ) (hCchem : 0 ≤ Cchem)
    (hH2 : ∀ s, 0 ≤ s →
      IntervalWeakH2Neumann (coupledChemDivSourceLift p u s))
    (hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs (coupledChemDivSourceLift p u s) k|
        ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2)
    (hzero : ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem)
    (H : CoupledChemDivFluxFactorFACInputs p u)
    (hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n))
    (MchemDot : ℝ)
    (hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) :=
  coupledChemDivSource_timeC1_of_factorJointC2Inputs
    Cchem hCchem hH2 hdecay hzero
    (coupledChemDivFluxFactorJointC2Inputs_of_FACInputs H)
    hadotcont MchemDot hMdot

end ShenWork.IntervalCoupledRegularityBootstrap
