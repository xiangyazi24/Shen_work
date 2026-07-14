import ShenWork.Paper2.IntervalDomainMClassicalInitialOverlap
import ShenWork.Paper2.IntervalDomainMConjugateMildHolderBootstrap
import ShenWork.Paper3.IntervalDomainTailHolderCompactness

/-!
# General-power mild restarts on uniformly bounded orbit tails

For each fixed restart window, strict positivity and compactness supply a
positive floor.  The floor may depend on the window; the spatial Holder
constant used below does not.  This is the faithful general-`m` replacement
for the linear-flux tail Lipschitz package.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit

noncomputable section

private theorem intervalDomainM_abs_le_supNorm
    {f : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomainPoint ↦ |f x|)))
    (x : intervalDomainPoint) :
    |f x| ≤ intervalDomainM.supNorm f := by
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

/-- A physical restart of a faithful general-`m` classical solution admits a
positive-strip conjugate mild solution.  Its ceiling is any supplied uniform
tail ceiling; only its floor is selected from the individual compact window. -/
theorem intervalDomainM_tailRestartMildData_exists
    (p : CM2Params)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    {a h M : ℝ} (ha : 0 < a) (hh : 0 < h) (hM : 0 < M)
    (hub : ∀ t, a ≤ t → intervalDomainM.supNorm (u t) ≤ M) :
    ∃ D : ConjugateMildSolutionDataM p (u a), D.T = h ∧ D.M = M := by
  let H : ℝ := a + h + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have hahH : a + h < H := by dsimp [H]; linarith
  have hsol : IsPaper2ClassicalSolution intervalDomainM p H u v :=
    hglobal H hH
  obtain ⟨c, _B, hc, _hcB, htwo⟩ :=
    intervalDomainM_u_two_sided_on_compact hsol ha
      (by linarith : a ≤ a + h) hahH
  have hcM : c ≤ M := by
    let x0 : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
    have hca : c ≤ u a x0 := (htwo a (by constructor <;> linarith) x0).1
    have hbdd := solution_slice_abs_bddAbove hsol
      (t := a) (by constructor <;> linarith : a ∈ Ioo (0 : ℝ) H)
    have hpoint := intervalDomainM_abs_le_supNorm hbdd x0
    exact hca.trans ((le_abs_self _).trans (hpoint.trans (hub a le_rfl)))
  let w := classicalRestartTrajectoryM a h u
  refine ⟨
    { T := h
      hT := hh
      M := M
      hM := hM
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
      hsol ha hh.le hahH hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact hpoint
  · intro r hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have ht : a + r ∈ Ioo (0 : ℝ) H := by
      constructor
      · linarith
      · exact lt_of_le_of_lt (by linarith) hahH
    have hbdd := solution_slice_abs_bddAbove hsol ht
    have hpoint := intervalDomainM_abs_le_supNorm hbdd x
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact hpoint.trans (hub (a + r) (by linarith))
  · intro r hr0 hrh x
    have hrmem : r ∈ Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun (classicalRestartTrajectoryM_eq hrmem) x
    rw [hw]
    exact (htwo (a + r) (by constructor <;> linarith) x).1
  · simpa [w] using classicalRestartTrajectoryM_hasContinuousSlices
      hsol ha hh.le hahH
  · simpa [w] using classicalRestartTrajectoryM_hasJointMeasurability
      hsol ha hh.le hahH
  · intro x
    have hbdd := solution_slice_abs_bddAbove hsol
      (t := a) (by constructor <;> linarith : a ∈ Ioo (0 : ℝ) H)
    exact (intervalDomainM_abs_le_supNorm hbdd x).trans (hub a le_rfl)

#print axioms intervalDomainM_tailRestartMildData_exists

end

end ShenWork.Paper3
