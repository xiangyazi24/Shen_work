import ShenWork.Paper2.IntervalWeakPIDUpgrade
import ShenWork.Paper2.IntervalBFormNegPartStrictPosBarrier

open Set
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter)
open ShenWork.Paper2
  (PositiveInitialDatum)

noncomputable section

namespace ShenWork.Paper2.IntervalWeakPIDUpgrade

/-- Weak interval positive initial data are instantly strictly positive under
the full Neumann heat semigroup. -/
theorem intervalFullSemigroupOperator_strictPos_of_weakPID
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {t : ℝ} (ht : 0 < t)
    {x : ℝ} (_hx : x ∈ Icc (0 : ℝ) 1) :
    0 < intervalFullSemigroupOperator t (intervalDomainLift u₀) x := by
  exact
    ShenWork.Paper2.BFormPositiveDatumNegPart.intervalFullSemigroupOperator_pos_of_positiveInitialDatum
      hu₀ ht x

/-- The heat-smoothing input needed for a weak-PID restart. -/
theorem heatStrictPositivityFromWeakPID
    (p : CM2Params) :
    HeatStrictPositivityFromWeakPID p := by
  intro u₀ hu₀ t ht x hx
  have hS :
      0 < intervalFullSemigroupOperator t (intervalDomainLift u₀) x :=
    intervalFullSemigroupOperator_strictPos_of_weakPID
      (u₀ := u₀) hu₀ ht hx
  simpa [conjugatePicardIter, intervalDomainLift, hx] using hS

end ShenWork.Paper2.IntervalWeakPIDUpgrade
