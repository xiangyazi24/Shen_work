/-
  Conjugate Picard logistic source: positive-window limit passage.

  The conjugate source tower currently contains only the level-0 logistic source
  package.  This file supplies the missing limit-passage theorem: once every
  conjugate iterate has a logistic-source `DuhamelSourceTimeC1On` package on a
  closed window and the source/derivative coefficients converge with common
  summable bounds, the conjugate Picard limit inherits the same package.

  This is intentionally stated on an arbitrary closed window `[lo, hi]`; using
  the canonical limit at `lo = 0` requires a separate endpoint-compatibility
  argument because `conjugatePicardLimit` is defined to be zero at time `0`.
-/
import ShenWork.Paper2.IntervalConjugateIterSourceTower
import ShenWork.Paper2.IntervalMildPicardLimitRegularityOn
import ShenWork.PDE.IntervalCoupledSourceTimeC1

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.ConjugateIterSourceTower

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter conjugatePicardLimit)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledLogisticSourceLift)

/-- Pass conjugate-iterate logistic source time-`C¹` regularity to the Picard
limit on a closed time window.

This is the logistic component of the B-form source package.  It consumes
iterate source packages, pointwise convergence of source coefficients, uniform
convergence of derivative coefficients, and common summable/derivative bounds.
It does not use `hpde_u`, a classical-solution package, or any chem-div endpoint
continuity statement. -/
noncomputable def conjLogSourceTimeC1On_limit_of_uniformLimit
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {T lo hi : ℝ}
    (hsrcSeq : ∀ n : ℕ, ConjLogSourceTimeC1On p u₀ n lo hi)
    (hcoeff_conv : ∀ s ∈ Set.Icc lo hi, ∀ k : ℕ,
      Tendsto
        (fun n : ℕ =>
          cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k)
        atTop
        (nhds
          (cosineCoeffs
            (logisticLifted p (conjugatePicardLimit p u₀ T s)) k)))
    {adot : ℝ → ℕ → ℝ}
    (hadot_unif : ∀ k : ℕ,
      TendstoUniformlyOn
        (fun n s => (hsrcSeq n).adot s k)
        (fun s => adot s k)
        atTop (Set.Icc lo hi))
    (hadot_cont : ∀ k : ℕ,
      ContinuousOn (fun s => adot s k) (Set.Icc lo hi))
    {envelope : ℕ → ℝ}
    (henv_summable : Summable envelope)
    (henv_bound : ∀ n : ℕ, ∀ s ∈ Set.Icc lo hi, ∀ k : ℕ,
      |cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k|
        ≤ envelope k)
    {Ddot : ℝ}
    (hderiv_bound : ∀ n : ℕ, ∀ s ∈ Set.Icc lo hi, ∀ k : ℕ,
      |(hsrcSeq n).adot s k| ≤ Ddot) :
    DuhamelSourceTimeC1On
      (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ T)) lo hi := by
  let aSeq : ℕ → ℝ → ℕ → ℝ :=
    fun n s k => cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k
  let a : ℝ → ℕ → ℝ :=
    fun s k => cosineCoeffs (logisticLifted p (conjugatePicardLimit p u₀ T s)) k
  have hlim : DuhamelSourceTimeC1On a lo hi :=
    ShenWork.IntervalMildPicardLimitRegularityOn.duhamelSourceTimeC1On_of_uniform_limit
      (a := a) (aSeq := aSeq)
      (fun s hs k => hcoeff_conv s hs k)
      (adotSeq := fun n s k => (hsrcSeq n).adot s k)
      (fun n s hs k => (hsrcSeq n).hderiv s hs k)
      (adot := adot)
      hadot_unif
      hadot_cont
      henv_summable
      (fun n s hs k => henv_bound n s hs k)
      hderiv_bound
  simpa [a, aSeq, coupledLogisticSourceCoeffs, coupledLogisticSourceLift,
    logisticLifted] using hlim

#print axioms conjLogSourceTimeC1On_limit_of_uniformLimit

end ShenWork.Paper2.ConjugateIterSourceTower

