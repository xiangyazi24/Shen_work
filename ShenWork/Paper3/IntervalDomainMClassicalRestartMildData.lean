import ShenWork.Paper2.IntervalDomainMClassicalInitialOverlap
import ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit

/-!
# Finite faithful classical restarts as positive-strip mild data

Every compact positive-time window of a faithful general-`m` classical
solution has uniform positive lower and absolute upper bounds.  Together with
the pointwise B-form restart identity, these bounds package the clamped
physical restart as a `ConjugateMildSolutionDataM` object.
-/

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit

noncomputable section

/-- A finite positive-time restart of a faithful general-`m` classical
solution is a positive-strip conjugate mild solution on the exact prescribed
relative horizon. -/
theorem intervalDomainM_classicalRestartMildData_exists
    (p : CM2Params)
    {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 < h) (hahT : a + h < T) :
    ∃ D : ConjugateMildSolutionDataM p (u a),
      D.T = h ∧ D.u = classicalRestartTrajectoryM a h u := by
  obtain ⟨c, M, hc, hcM, htwo⟩ :=
    intervalDomainM_u_two_sided_on_compact hsol ha
      (by linarith : a ≤ a + h) hahT
  let w := classicalRestartTrajectoryM a h u
  refine ⟨
    { T := h
      hT := hh
      M := M
      hM := hc.trans_le hcM
      c := c
      hc := hc
      u := w
      hmild := ?_
      hbound := ?_
      hfloor := ?_
      hcont := ?_
      hmeas := ?_
      datum_bound := ?_ }, rfl, rfl⟩
  · intro r hr0 hrh x
    have hpoint := intervalDomainM_classical_bform_restart_pointwise
      hsol ha hh.le hahT hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact hpoint
  · intro r hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact (htwo (a + r) (by constructor <;> linarith) x).2
  · intro r hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact (htwo (a + r) (by constructor <;> linarith) x).1
  · simpa [w] using classicalRestartTrajectoryM_hasContinuousSlices
      hsol ha hh.le hahT
  · simpa [w] using classicalRestartTrajectoryM_hasJointMeasurability
      hsol ha hh.le hahT
  · intro x
    exact (htwo a (by constructor <;> linarith) x).2

#print axioms intervalDomainM_classicalRestartMildData_exists

end

end ShenWork.Paper3
