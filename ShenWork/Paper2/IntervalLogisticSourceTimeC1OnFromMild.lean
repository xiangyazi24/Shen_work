import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.PDE.IntervalCoupledSourceTimeC1
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

open Set

noncomputable section

namespace ShenWork.Paper2.IntervalLogisticSourceTimeC1OnFromMild

open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)

/-- Package the logistic source coefficient hypotheses supplied by the mild
solution/ladder machinery into the window-local Duhamel source interface. -/
noncomputable def logisticSource_duhamelSourceTimeC1On_of_mild_and_envelope
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    {c T' : ℝ} (_hc : 0 < c) (_hT' : T' < S.T)
    {envelope : ℕ → ℝ} {adot : ℝ → ℕ → ℝ} {D : ℝ}
    (henv : ∀ k,
      |(fun s => coupledLogisticSourceCoeffs p S.u s k)| ≤
        fun _ => envelope k)
    (henv_sum : Summable envelope)
    (hderiv_exist : ∀ s ∈ Icc c T', ∀ k,
      HasDerivAt (fun t => coupledLogisticSourceCoeffs p S.u t k)
        (adot s k) s)
    (hadot_cont : ∀ k, ContinuousOn (fun s => adot s k) (Icc c T'))
    (hadot_bound : ∀ s ∈ Icc c T', ∀ k, |adot s k| ≤ D) :
    DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p S.u) c T' where
  adot := adot
  hderiv := by
    intro s hs k
    exact (hderiv_exist s hs k).hasDerivWithinAt
  hadotcont := hadot_cont
  envelope := envelope
  henv_summable := henv_sum
  henv_bound := by
    intro s _hs k
    simpa using henv k s
  derivBound := D
  hderivBound := hadot_bound

end ShenWork.Paper2.IntervalLogisticSourceTimeC1OnFromMild
