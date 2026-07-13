/-
  Joint positive-time continuity of the faithful conjugate mild solution.

  Fixed-point time continuity is combined with the already proved spatial
  Holder estimate.  The Holder constant is only uniform after a positive time
  cutoff, so the generic local-strip bridge is used rather than a false global
  modulus extending to time zero.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildTimeContinuity
import ShenWork.Paper2.IntervalJointContinuityFromHolder
import ShenWork.Paper2.IntervalDomainMConjugateMildHolderBootstrap

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)

/-- The lifted faithful mild solution is jointly continuous on the whole
strict-positive-time physical slab, including both spatial endpoints. -/
theorem conjugateMildM_jointValue_u
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u0)
    (hu0_bound : ∀ y, |intervalDomainLift u0 y| ≤ D.M)
    (hu0_meas : AEStronglyMeasurable
      (intervalDomainLift u0) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) ↦ intervalDomainLift (D.u t) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply jointContinuousOn_Ioo_of_timeSlices_and_positiveStripHolder
    (theta := (1 : ℝ) / 2) (by norm_num)
  · intro x hx
    have htime := conjugateMildM_timeSlice_continuousOn_Ioc
      D hu0_bound hu0_meas ⟨x, hx⟩
    have htime_open := htime.mono (by
      intro t (ht : t ∈ Set.Ioo (0 : ℝ) D.T)
      exact ⟨ht.1, ht.2.le⟩)
    simpa [intervalDomainLift, hx] using htime_open
  · intro tau htau
    obtain ⟨K, hK, hholder⟩ := conjugateMildM_positiveTime_holder
      D hu0_bound hu0_meas
        (θ := (1 : ℝ) / 2) (τ := tau)
        (by norm_num) (by norm_num) htau
    refine ⟨K, hK, ?_⟩
    intro t ht x hx y hy
    simpa [intervalDomainLift, hx, hy] using
      hholder t ht ⟨x, hx⟩ ⟨y, hy⟩

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_jointValue_u
