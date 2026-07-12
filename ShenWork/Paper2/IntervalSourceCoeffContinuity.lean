import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.PDE.IntervalCoupledSourceTimeC1
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

open Set

noncomputable section

namespace ShenWork.Paper2.IntervalSourceCoeffContinuity

open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)

/-- A `DuhamelSourceTimeC1On` package contains one-sided derivatives of the
source coefficients; this immediately gives continuity of the coefficients. -/
theorem coeff_continuousOn_of_timeC1On
    {a : ℝ → ℕ → ℝ} {lo hi : ℝ}
    (src : DuhamelSourceTimeC1On a lo hi) (k : ℕ) :
    ContinuousOn (fun s : ℝ => a s k) (Icc lo hi) := by
  intro s hs
  exact (src.hderiv s hs k).continuousWithinAt

/-- Logistic source coefficient continuity on a positive window, projected from
the landed window-local source package.  Bare `ConjugateMildSolutionData` only
contains spatial slice continuity, so the time source package is the needed
time-regularity input. -/
theorem logisticSourceCoeff_continuousOn_of_mild
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) (k : ℕ)
    {c T' : ℝ} (hc : 0 < c) (hT' : T' < S.T)
    (hlog_on : DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p S.u) 0 S.T) :
    ContinuousOn (fun s => coupledLogisticSourceCoeffs p S.u s k) (Icc c T') := by
  have hbase :
      ContinuousOn (fun s => coupledLogisticSourceCoeffs p S.u s k)
        (Icc (0 : ℝ) S.T) :=
    coeff_continuousOn_of_timeC1On hlog_on k
  refine hbase.mono ?_
  intro s hs
  exact ⟨le_of_lt (lt_of_lt_of_le hc hs.1), le_of_lt (lt_of_le_of_lt hs.2 hT')⟩

/-- Chem-div source coefficient continuity on a positive window, projected from
the landed window-local source package. -/
theorem chemDivSourceCoeff_continuousOn_of_mild
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) (k : ℕ)
    {c T' : ℝ} (hc : 0 < c) (hT' : T' < S.T)
    (hchem_on : DuhamelSourceTimeC1On
      (coupledChemDivSourceCoeffs p S.u) 0 S.T) :
    ContinuousOn (fun s => coupledChemDivSourceCoeffs p S.u s k) (Icc c T') := by
  have hbase :
      ContinuousOn (fun s => coupledChemDivSourceCoeffs p S.u s k)
        (Icc (0 : ℝ) S.T) :=
    coeff_continuousOn_of_timeC1On hchem_on k
  refine hbase.mono ?_
  intro s hs
  exact ⟨le_of_lt (lt_of_lt_of_le hc hs.1), le_of_lt (lt_of_le_of_lt hs.2 hT')⟩

end ShenWork.Paper2.IntervalSourceCoeffContinuity

