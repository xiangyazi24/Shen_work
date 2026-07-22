import ShenWork.Paper1.WholeLinePhysicalMildClassical

/-!
# Reachable horizons for physical whole-line mild segments

This file supplies a uniform restart window under a BUC norm bound and the
order-theoretic gluing data for bounded and unbounded sets of reachable
horizons.
-/

open Filter MeasureTheory Real Set Topology Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-- A BUC norm ceiling gives one common physical mild lifespan. -/
theorem exists_uniform_wholeLinePhysicalMildSegment
    (p : CMParams) (C : ℝ) :
    ∃ H > 0, ∀ w : WholeLineBUC,
      (∀ x : ℝ, 0 ≤ w.1 x) → ‖w‖ ≤ C →
        Nonempty (WholeLinePhysicalMildSegment p w H) := by
  let M : ℝ := max C 0 + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨H, hH, hsmall, hdisp⟩ :=
    exists_pos_time_wholeLineCauchyBUCRate_and_displacement
      p hM (by norm_num : (0 : ℝ) < 1)
  refine ⟨H, hH, ?_⟩
  intro w hw0 hwC
  let U : WholeLineBUCTrajectory H :=
    wholeLineCauchyBUCMildFixedPoint p hM hH.le w hsmall
  have hnorm : ‖w.1‖ = ‖w‖ := rfl
  have hmargin : ‖w‖ + 1 ≤ M := by
    change ‖w.1‖ + 1 ≤ M
    rw [hnorm]
    dsimp [M]
    linarith [hwC.trans (le_max_left C 0)]
  have hupper : ∀ z : Set.Icc (0 : ℝ) H, ∀ x, (U z).1 x ≤ M := by
    intro z x
    let Q : WholeLineBUC := wholeLineCauchyHeatBUCTotal z.1 w
    have hdist : dist (U z) Q ≤
        wholeLineCauchyBUCMildDisplacement p M H := by
      simpa [U, Q] using
        wholeLineCauchyBUCMildFixedPoint_dist_homogeneous_le
          p hM hH.le w hsmall z
    have hpoint : |(U z).1 x - Q.1 x| ≤
        wholeLineCauchyBUCMildDisplacement p M H :=
      (WholeLineBUC.pointwise_abs_sub_le_dist (U z) Q x).trans hdist
    have hQ : ‖Q‖ ≤ ‖w‖ :=
      wholeLineCauchyHeatBUCTotal_norm_le_of_nonneg z.2.1 w
    exact (show (U z).1 x < M from by
      calc
        (U z).1 x ≤ Q.1 x + |(U z).1 x - Q.1 x| := by
          linarith [le_abs_self ((U z).1 x - Q.1 x)]
        _ ≤ ‖Q‖ + wholeLineCauchyBUCMildDisplacement p M H :=
          add_le_add (WholeLineBUC.apply_le_norm Q x) hpoint
        _ ≤ ‖w‖ + wholeLineCauchyBUCMildDisplacement p M H :=
          add_le_add hQ le_rfl
        _ < ‖w‖ + 1 := by linarith
        _ ≤ M := hmargin).le
  have hnonnegative : ∀ z : Set.Icc (0 : ℝ) H, ∀ x, 0 ≤ (U z).1 x := by
    intro z x
    simpa [U] using wholeLineCauchyBUCMildFixedPoint_nonnegative
      p hM hH w hw0 hsmall z x
  have hstrip : ∀ z : Set.Icc (0 : ℝ) H, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hH.le w hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M := by
    intro z x
    exact ⟨by simpa [U] using hnonnegative z x,
      by simpa [U] using hupper z x⟩
  have hmild :=
    wholeLineCauchyBUCMildFixedPoint_eq_original_mildMap_of_mem_Icc
      p hM hH.le w hsmall hstrip
  refine ⟨
    { T_pos := hH
      traj := U
      nonnegative := hnonnegative
      mild := ?_ }⟩
  simpa [U] using hmild

/-- Reachability of a positive horizon by a physical BUC mild segment. -/
def WholeLinePhysicalMildReachable
    (p : CMParams) (u₀ : WholeLineBUC) (T : ℝ) : Prop :=
  Nonempty (WholeLinePhysicalMildSegment p u₀ T)

def wholeLinePhysicalMildReachableSet
    (p : CMParams) (u₀ : WholeLineBUC) : Set ℝ :=
  {T | WholeLinePhysicalMildReachable p u₀ T}

noncomputable def wholeLinePhysicalMildSegmentOfReach
    {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (h : WholeLinePhysicalMildReachable p u₀ T) :
    WholeLinePhysicalMildSegment p u₀ T :=
  Classical.choice h

theorem wholeLinePhysicalMildReachableSet_nonempty
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x, 0 ≤ u₀.1 x) :
    (wholeLinePhysicalMildReachableSet p u₀).Nonempty := by
  obtain ⟨T, hT⟩ := exists_wholeLinePhysicalMildSegment p u₀ hu₀
  exact ⟨T, hT⟩

theorem wholeLinePhysicalMildReachable_mono
    {p : CMParams} {u₀ : WholeLineBUC} {T h : ℝ}
    (hreach : WholeLinePhysicalMildReachable p u₀ T)
    (hh : 0 < h) (hhT : h ≤ T) :
    WholeLinePhysicalMildReachable p u₀ h := by
  let d := wholeLinePhysicalMildSegmentOfReach hreach
  exact ⟨d.restrict hh hhT⟩

noncomputable def finiteMaximalWholeLinePhysicalMildHorizon
    (p : CMParams) (u₀ : WholeLineBUC) : ℝ :=
  sSup (wholeLinePhysicalMildReachableSet p u₀)

theorem wholeLinePhysicalMildReachable_le_finiteMaximal
    {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (hbdd : BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (hT : WholeLinePhysicalMildReachable p u₀ T) :
    T ≤ finiteMaximalWholeLinePhysicalMildHorizon p u₀ :=
  le_csSup hbdd hT

theorem finiteMaximalWholeLinePhysicalMildHorizon_pos
    {p : CMParams} {u₀ : WholeLineBUC}
    (hbdd : BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (hne : (wholeLinePhysicalMildReachableSet p u₀).Nonempty) :
    0 < finiteMaximalWholeLinePhysicalMildHorizon p u₀ := by
  obtain ⟨T, hT⟩ := hne
  let d := wholeLinePhysicalMildSegmentOfReach hT
  exact d.T_pos.trans_le
    (wholeLinePhysicalMildReachable_le_finiteMaximal hbdd hT)

noncomputable def wholeLinePickReachableAbove
    {p : CMParams} {u₀ : WholeLineBUC}
    (hbdd : BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (hne : (wholeLinePhysicalMildReachableSet p u₀).Nonempty)
    {t : ℝ} (ht : t < finiteMaximalWholeLinePhysicalMildHorizon p u₀) :
    {S : ℝ // WholeLinePhysicalMildReachable p u₀ S ∧ t < S} :=
  let h : ∃ S ∈ wholeLinePhysicalMildReachableSet p u₀, t < S :=
    (lt_csSup_iff hbdd hne).mp ht
  ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

noncomputable def wholeLinePickReachableAboveData
    {p : CMParams} {u₀ : WholeLineBUC}
    (hbdd : BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (hne : (wholeLinePhysicalMildReachableSet p u₀).Nonempty)
    {t : ℝ} (ht : t < finiteMaximalWholeLinePhysicalMildHorizon p u₀) :
    WholeLinePhysicalMildSegment p u₀
      (wholeLinePickReachableAbove hbdd hne ht).1 :=
  wholeLinePhysicalMildSegmentOfReach
    (wholeLinePickReachableAbove hbdd hne ht).2.1

noncomputable def boundedWholeLinePhysicalMildGluedBUC
    {p : CMParams} {u₀ : WholeLineBUC}
    (hbdd : BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (hne : (wholeLinePhysicalMildReachableSet p u₀).Nonempty) :
    ℝ → WholeLineBUC := fun t =>
  if ht : 0 < t ∧ t < finiteMaximalWholeLinePhysicalMildHorizon p u₀ then
    let pick := wholeLinePickReachableAbove hbdd hne ht.2
    let d := wholeLinePickReachableAboveData hbdd hne ht.2
    d.traj ⟨t, ht.1.le, pick.2.2.le⟩
  else u₀

theorem boundedWholeLinePhysicalMildGluedBUC_eq_segment
    {p : CMParams} {u₀ : WholeLineBUC}
    (hbdd : BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (hne : (wholeLinePhysicalMildReachableSet p u₀).Nonempty)
    {S t : ℝ} (d : WholeLinePhysicalMildSegment p u₀ S)
    (ht0 : 0 ≤ t) (htS : t < S) :
    boundedWholeLinePhysicalMildGluedBUC hbdd hne t = d.extend t := by
  have hSmax : S ≤ finiteMaximalWholeLinePhysicalMildHorizon p u₀ :=
    wholeLinePhysicalMildReachable_le_finiteMaximal hbdd ⟨d⟩
  have htmax := htS.trans_le hSmax
  by_cases htzero : t = 0
  · subst t
    simp [boundedWholeLinePhysicalMildGluedBUC, d.extend_zero]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
    let pick := wholeLinePickReachableAbove hbdd hne htmax
    let e := wholeLinePickReachableAboveData hbdd hne htmax
    have heq := e.eq_on_common_Icc d htpos pick.2.2.le htS.le t
      ⟨htpos.le, le_rfl⟩
    have hext : d.extend t = d.traj ⟨t, htpos.le, htS.le⟩ :=
      wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj
        ⟨htpos.le, htS.le⟩
    rw [boundedWholeLinePhysicalMildGluedBUC, dif_pos ⟨htpos, htmax⟩]
    simpa [pick, e, hext] using heq

noncomputable def wholeLinePickUnboundedReachableAbove
    {p : CMParams} {u₀ : WholeLineBUC}
    (hnbdd : ¬ BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (t : ℝ) :
    {S : ℝ // WholeLinePhysicalMildReachable p u₀ S ∧ t < S} :=
  let h := (not_bddAbove_iff.mp hnbdd) t
  ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

noncomputable def wholeLinePickUnboundedReachableAboveData
    {p : CMParams} {u₀ : WholeLineBUC}
    (hnbdd : ¬ BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (t : ℝ) : WholeLinePhysicalMildSegment p u₀
      (wholeLinePickUnboundedReachableAbove hnbdd t).1 :=
  wholeLinePhysicalMildSegmentOfReach
    (wholeLinePickUnboundedReachableAbove hnbdd t).2.1

noncomputable def unboundedWholeLinePhysicalMildGluedBUC
    {p : CMParams} {u₀ : WholeLineBUC}
    (hnbdd : ¬ BddAbove (wholeLinePhysicalMildReachableSet p u₀)) :
    ℝ → WholeLineBUC := fun t =>
  if ht : 0 < t then
    let pick := wholeLinePickUnboundedReachableAbove hnbdd t
    let d := wholeLinePickUnboundedReachableAboveData hnbdd t
    d.traj ⟨t, ht.le, pick.2.2.le⟩
  else u₀

theorem unboundedWholeLinePhysicalMildGluedBUC_eq_segment
    {p : CMParams} {u₀ : WholeLineBUC}
    (hnbdd : ¬ BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    {S t : ℝ} (d : WholeLinePhysicalMildSegment p u₀ S)
    (ht0 : 0 ≤ t) (htS : t < S) :
    unboundedWholeLinePhysicalMildGluedBUC hnbdd t = d.extend t := by
  by_cases htzero : t = 0
  · subst t
    simp [unboundedWholeLinePhysicalMildGluedBUC, d.extend_zero]
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
    let pick := wholeLinePickUnboundedReachableAbove hnbdd t
    let e := wholeLinePickUnboundedReachableAboveData hnbdd t
    have heq := e.eq_on_common_Icc d htpos pick.2.2.le htS.le t
      ⟨htpos.le, le_rfl⟩
    have hext : d.extend t = d.traj ⟨t, htpos.le, htS.le⟩ :=
      wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj
        ⟨htpos.le, htS.le⟩
    rw [unboundedWholeLinePhysicalMildGluedBUC, dif_pos htpos]
    simpa [pick, e, hext] using heq

section AxiomAudit

#print axioms exists_uniform_wholeLinePhysicalMildSegment
#print axioms boundedWholeLinePhysicalMildGluedBUC_eq_segment
#print axioms unboundedWholeLinePhysicalMildGluedBUC_eq_segment

end AxiomAudit

end ShenWork.Paper1
