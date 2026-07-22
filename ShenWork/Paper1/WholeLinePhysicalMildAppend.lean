import ShenWork.Paper1.WholeLinePhysicalMildSegments

/-!
# Appending physical whole-line mild segments

The only nonlocal point in finite continuation is the divergence history.
The positive-time bounded-`C¹` flux theorem and the heat-gradient cocycle
allow a canonical restart segment to be appended to an arbitrary physical
mild segment.
-/

open Filter MeasureTheory Real Set Topology Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-- Continuous concatenation of two BUC trajectories whose seam values
agree. -/
def wholeLineBUCTrajectoryAppend
    {T H : ℝ} (hT : 0 ≤ T) (hH : 0 ≤ H)
    (U : WholeLineBUCTrajectory T) (V : WholeLineBUCTrajectory H)
    (hseam : U ⟨T, hT, le_rfl⟩ = V ⟨0, le_rfl, hH⟩) :
    WholeLineBUCTrajectory (T + H) := by
  let f : ℝ → WholeLineBUC := wholeLineBUCTrajectoryExtend hT U
  let g : ℝ → WholeLineBUC := fun s =>
    wholeLineBUCTrajectoryExtend hH V (s - T)
  have hf : Continuous f := wholeLineBUCTrajectoryExtend_continuous hT U
  have hg : Continuous g :=
    (wholeLineBUCTrajectoryExtend_continuous hH V).comp
      (continuous_id.sub continuous_const)
  have hfg : ∀ s : ℝ, s = T → f s = g s := by
    intro s hs
    subst s
    rw [show f T = U ⟨T, hT, le_rfl⟩ by
      exact wholeLineBUCTrajectoryExtend_eq hT U ⟨hT, le_rfl⟩]
    rw [show g T = V ⟨0, le_rfl, hH⟩ by
      dsimp [g]
      rw [sub_self]
      exact wholeLineBUCTrajectoryExtend_eq hH V ⟨le_rfl, hH⟩]
    exact hseam
  let w : ℝ → WholeLineBUC := fun s => if s ≤ T then f s else g s
  have hw : Continuous w := by
    exact continuous_if_le continuous_id continuous_const
      hf.continuousOn hg.continuousOn hfg
  exact ⟨fun z => w z.1, hw.comp continuous_subtype_val⟩

@[simp] theorem wholeLineBUCTrajectoryAppend_apply_of_le
    {T H : ℝ} (hT : 0 ≤ T) (hH : 0 ≤ H)
    (U : WholeLineBUCTrajectory T) (V : WholeLineBUCTrajectory H)
    (hseam : U ⟨T, hT, le_rfl⟩ = V ⟨0, le_rfl, hH⟩)
    (z : Set.Icc (0 : ℝ) (T + H)) (hz : z.1 ≤ T) :
    wholeLineBUCTrajectoryAppend hT hH U V hseam z =
      wholeLineBUCTrajectoryExtend hT U z.1 := by
  simp [wholeLineBUCTrajectoryAppend, hz]

@[simp] theorem wholeLineBUCTrajectoryAppend_apply_of_not_le
    {T H : ℝ} (hT : 0 ≤ T) (hH : 0 ≤ H)
    (U : WholeLineBUCTrajectory T) (V : WholeLineBUCTrajectory H)
    (hseam : U ⟨T, hT, le_rfl⟩ = V ⟨0, le_rfl, hH⟩)
    (z : Set.Icc (0 : ℝ) (T + H)) (hz : ¬ z.1 ≤ T) :
    wholeLineBUCTrajectoryAppend hT hH U V hseam z =
      wholeLineBUCTrajectoryExtend hH V (z.1 - T) := by
  simp [wholeLineBUCTrajectoryAppend, hz]

/-- The entire post-seam shift of an appended trajectory is its second
factor. -/
theorem wholeLineBUCTrajectoryShift_append_eq_right
    {T H : ℝ} (hT : 0 ≤ T) (hH : 0 ≤ H)
    (U : WholeLineBUCTrajectory T) (V : WholeLineBUCTrajectory H)
    (hseam : U ⟨T, hT, le_rfl⟩ = V ⟨0, le_rfl, hH⟩) :
    wholeLineBUCTrajectoryShift hT hH le_rfl
        (wholeLineBUCTrajectoryAppend hT hH U V hseam) = V := by
  apply ContinuousMap.ext
  intro z
  let zTH : Set.Icc (0 : ℝ) (T + H) :=
    ⟨T + z.1, add_nonneg hT z.2.1, by linarith [z.2.2]⟩
  by_cases hz0 : z.1 = 0
  · have hz : z = ⟨0, le_rfl, hH⟩ := Subtype.ext hz0
    subst z
    simp only [wholeLineBUCTrajectoryShift_apply]
    simp only [add_zero]
    rw [wholeLineBUCTrajectoryAppend_apply_of_le hT hH U V hseam _ le_rfl,
      wholeLineBUCTrajectoryExtend_eq hT U ⟨hT, le_rfl⟩]
    exact hseam
  · have hzpos : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz0)
    change wholeLineBUCTrajectoryAppend hT hH U V hseam zTH = V z
    rw [wholeLineBUCTrajectoryAppend_apply_of_not_le hT hH U V hseam]
    · rw [show (zTH.1 - T) = z.1 by dsimp [zTH]; ring]
      exact wholeLineBUCTrajectoryExtend_eq hH V z.2
    · dsimp [zTH]
      linarith

namespace WholeLinePhysicalMildSegment

/-- A physical mild segment can be continued by any physical mild segment
started from its terminal BUC slice. -/
theorem append
    {p : CMParams} {u₀ : WholeLineBUC} {T H : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T)
    (e : WholeLinePhysicalMildSegment p
      (d.traj ⟨T, d.T_pos.le, le_rfl⟩) H) :
    Nonempty (WholeLinePhysicalMildSegment p u₀ (T + H)) := by
  let zT : Set.Icc (0 : ℝ) T := ⟨T, d.T_pos.le, le_rfl⟩
  let z0 : Set.Icc (0 : ℝ) H := ⟨0, le_rfl, e.T_pos.le⟩
  have hseam : d.traj zT = e.traj z0 := by
    exact e.initial.symm
  let W : WholeLineBUCTrajectory (T + H) :=
    wholeLineBUCTrajectoryAppend d.T_pos.le e.T_pos.le d.traj e.traj hseam
  have hTH : 0 < T + H := add_pos d.T_pos e.T_pos
  obtain ⟨M₁, hM₁, hstrip₁⟩ := d.exists_physical_clamp
  obtain ⟨M₂, hM₂, hstrip₂⟩ := e.exists_physical_clamp
  let M : ℝ := max M₁ M₂
  have hM : 0 ≤ M := hM₁.trans (le_max_left _ _)
  have hstripD : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (d.traj z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro z x
    exact ⟨(hstrip₁ z x).1,
      (hstrip₁ z x).2.trans (by dsimp [M]; exact le_max_left _ _)⟩
  have hstripE : ∀ z : Set.Icc (0 : ℝ) H, ∀ x,
      (e.traj z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro z x
    exact ⟨(hstrip₂ z x).1,
      (hstrip₂ z x).2.trans (by dsimp [M]; exact le_max_right _ _)⟩
  have hstripW : ∀ z : Set.Icc (0 : ℝ) (T + H), ∀ x,
      (W z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro z x
    by_cases hz : z.1 ≤ T
    · have hzT : z.1 ∈ Set.Icc (0 : ℝ) T := ⟨z.2.1, hz⟩
      have hWz : W z = d.traj ⟨z.1, hzT⟩ := by
        dsimp [W]
        rw [wholeLineBUCTrajectoryAppend_apply_of_le
          d.T_pos.le e.T_pos.le d.traj e.traj hseam z hz,
          wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hzT]
      rw [hWz]
      exact hstripD ⟨z.1, hzT⟩ x
    · have hr : z.1 - T ∈ Set.Icc (0 : ℝ) H := by
        constructor
        · linarith
        · linarith [z.2.2]
      have hWz : W z = e.traj ⟨z.1 - T, hr⟩ := by
        dsimp [W]
        rw [wholeLineBUCTrajectoryAppend_apply_of_not_le
          d.T_pos.le e.T_pos.le d.traj e.traj hseam z hz,
          wholeLineBUCTrajectoryExtend_eq e.T_pos.le e.traj hr]
      rw [hWz]
      exact hstripE ⟨z.1 - T, hr⟩ x
  have hfixedD : IsFixedPt
      (wholeLineCauchyBUCMildMap p hM d.T_pos.le u₀) d.traj :=
    d.isFixedPt hM hstripD
  have hfixedE : IsFixedPt
      (wholeLineCauchyBUCMildMap p hM e.T_pos.le (d.traj zT)) e.traj :=
    e.isFixedPt hM hstripE
  have hshift : wholeLineBUCTrajectoryShift d.T_pos.le e.T_pos.le le_rfl W =
      e.traj := by
    simpa [W] using wholeLineBUCTrajectoryShift_append_eq_right
      d.T_pos.le e.T_pos.le d.traj e.traj hseam
  have hsourceOld : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      wholeLineCauchyFluxSourceTrajectory p hM hTH.le W s =
        wholeLineCauchyFluxSourceTrajectory p hM d.T_pos.le d.traj s := by
    intro s hs
    unfold wholeLineCauchyFluxSourceTrajectory
    have hsTH : s ∈ Set.Icc (0 : ℝ) (T + H) :=
      ⟨hs.1.le, hs.2.trans (le_add_of_nonneg_right e.T_pos.le)⟩
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
    rw [wholeLineBUCTrajectoryExtend_eq hTH.le W hsTH,
      wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hsT]
    congr 1
    dsimp [W]
    rw [wholeLineBUCTrajectoryAppend_apply_of_le
      d.T_pos.le e.T_pos.le d.traj e.traj hseam _ hs.2,
      wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hsT]
  have hfluxD := wholeLinePhysicalFixedPoint_fluxSource_spatialC1_positive
    p hM d.T_pos u₀ d.traj hfixedD hstripD
  have hFderiv : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∀ y,
      HasDerivAt
        (wholeLineCauchyFluxSourceTrajectory p hM hTH.le W s).1
        (deriv (wholeLineCauchyFluxSourceTrajectory p hM hTH.le W s).1 y) y := by
    intro s hs y
    rw [hsourceOld s hs]
    exact (hfluxD s hs).1 y
  have hFderiv_cont : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      Continuous
        (deriv (wholeLineCauchyFluxSourceTrajectory p hM hTH.le W s).1) := by
    intro s hs
    rw [hsourceOld s hs]
    exact (hfluxD s hs).2.1
  have hFderiv_bound : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∃ D : ℝ, ∀ y,
      |deriv (wholeLineCauchyFluxSourceTrajectory p hM hTH.le W s).1 y| ≤ D := by
    intro s hs
    rw [hsourceOld s hs]
    exact (hfluxD s hs).2.2
  have hfixedW : IsFixedPt
      (wholeLineCauchyBUCMildMap p hM hTH.le u₀) W := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    by_cases hz : z.1 ≤ T
    · have hzT : z.1 ∈ Set.Icc (0 : ℝ) T := ⟨z.2.1, hz⟩
      have hWz : W z = d.traj ⟨z.1, hzT⟩ := by
        dsimp [W]
        rw [wholeLineBUCTrajectoryAppend_apply_of_le
          d.T_pos.le e.T_pos.le d.traj e.traj hseam z hz,
          wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hzT]
      have hagree : ∀ s ∈ Set.Icc (0 : ℝ) z.1,
          (fun q y => (wholeLineBUCTrajectoryExtend hTH.le W q).1 y) s =
            (fun q y =>
              (wholeLineBUCTrajectoryExtend d.T_pos.le d.traj q).1 y) s := by
        intro s hs
        funext y
        have hsTH : s ∈ Set.Icc (0 : ℝ) (T + H) :=
          ⟨hs.1, (hs.2.trans hz).trans
            (le_add_of_nonneg_right e.T_pos.le)⟩
        have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hz⟩
        change
          (wholeLineBUCTrajectoryExtend hTH.le W s).1 y =
            (wholeLineBUCTrajectoryExtend d.T_pos.le d.traj s).1 y
        rw [wholeLineBUCTrajectoryExtend_eq hTH.le W hsTH,
          wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hsT]
        have hsle : s ≤ T := hs.2.trans hz
        dsimp [W]
        rw [wholeLineBUCTrajectoryAppend_apply_of_le
          d.T_pos.le e.T_pos.le d.traj e.traj hseam _ hsle,
          wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hsT]
      have hcongr := wholeLineCauchyMildMap_congr_on_Icc_segments
        p u₀.1 z.2.1 hagree x
      have hbridge := wholeLineCauchyBUCMildMap_apply_eq_original_of_mem_Icc
        p hM hTH.le u₀ W hstripW z x
      rw [hWz]
      exact hbridge.trans (hcongr.trans (d.mild ⟨z.1, hzT⟩ x).symm)
    · have hrpos : 0 < z.1 - T := sub_pos.mpr (lt_of_not_ge hz)
      have hrH : z.1 - T ≤ H := by linarith [z.2.2]
      let r : ℝ := z.1 - T
      let zr : Set.Icc (0 : ℝ) H := ⟨r, hrpos.le, hrH⟩
      have htime : T + r = z.1 := by dsimp [r]; ring
      have hWz : W z = e.traj zr := by
        dsimp [W]
        rw [wholeLineBUCTrajectoryAppend_apply_of_not_le
          d.T_pos.le e.T_pos.le d.traj e.traj hseam z hz,
          wholeLineBUCTrajectoryExtend_eq e.T_pos.le e.traj zr.2]
      have hWT : W ⟨T, d.T_pos.le,
          le_add_of_nonneg_right e.T_pos.le⟩ = d.traj zT := by
        dsimp [W]
        rw [wholeLineBUCTrajectoryAppend_apply_of_le
          d.T_pos.le e.T_pos.le d.traj e.traj hseam _ le_rfl,
          wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj zT.2]
      have hmapWT :
          wholeLineCauchyBUCMildMap p hM hTH.le u₀ W
              ⟨T, d.T_pos.le, le_add_of_nonneg_right e.T_pos.le⟩ =
            W ⟨T, d.T_pos.le, le_add_of_nonneg_right e.T_pos.le⟩ := by
        apply Subtype.ext
        apply BoundedContinuousFunction.ext
        intro y
        have hagree : ∀ s ∈ Set.Icc (0 : ℝ) T,
            (fun q y => (wholeLineBUCTrajectoryExtend hTH.le W q).1 y) s =
              (fun q y =>
                (wholeLineBUCTrajectoryExtend d.T_pos.le d.traj q).1 y) s := by
          intro s hs
          funext q
          have hsTH : s ∈ Set.Icc (0 : ℝ) (T + H) :=
            ⟨hs.1, hs.2.trans (le_add_of_nonneg_right e.T_pos.le)⟩
          change
            (wholeLineBUCTrajectoryExtend hTH.le W s).1 q =
              (wholeLineBUCTrajectoryExtend d.T_pos.le d.traj s).1 q
          rw [wholeLineBUCTrajectoryExtend_eq hTH.le W hsTH,
            wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hs]
          dsimp [W]
          rw [wholeLineBUCTrajectoryAppend_apply_of_le
            d.T_pos.le e.T_pos.le d.traj e.traj hseam _ hs.2,
            wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hs]
        have hcongr := wholeLineCauchyMildMap_congr_on_Icc_segments
          p u₀.1 d.T_pos.le hagree y
        have hbridge := wholeLineCauchyBUCMildMap_apply_eq_original_of_mem_Icc
          p hM hTH.le u₀ W hstripW
            ⟨T, d.T_pos.le, le_add_of_nonneg_right e.T_pos.le⟩ y
        rw [hWT]
        exact hbridge.trans (hcongr.trans (d.mild zT y).symm)
      have hWTformula :
          W ⟨T, d.T_pos.le, le_add_of_nonneg_right e.T_pos.le⟩ =
            wholeLineCauchyHeatBUCTotal T u₀ +
              (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hTH.le W T +
              wholeLineCauchyValueDuhamelBUC p hM hTH.le W T := by
        have hm := hmapWT.symm
        simpa [wholeLineCauchyBUCMildMap] using hm
      have hEformula : e.traj zr =
          wholeLineCauchyHeatBUCTotal r (d.traj zT) +
            (-p.χ) • wholeLineCauchyGradientDuhamelBUC
              p hM e.T_pos.le e.traj r +
            wholeLineCauchyValueDuhamelBUC p hM e.T_pos.le e.traj r := by
        have hm := congrArg
          (fun Q : WholeLineBUCTrajectory H => Q zr) hfixedE.symm
        simpa [wholeLineCauchyBUCMildMap, zr] using hm
      have hGrestart := wholeLineCauchyGradientDuhamelBUC_restart
        p hM hTH.le W d.T_pos hrpos hFderiv hFderiv_cont hFderiv_bound
      have hRrestart := wholeLineCauchyValueDuhamelBUC_restart
        p hM hTH.le W d.T_pos hrpos
      have hGshift := wholeLineCauchyGradientDuhamelBUC_shift_eq
        p hM hTH.le d.T_pos.le e.T_pos.le le_rfl W zr.2
      have hRshift := wholeLineCauchyValueDuhamelBUC_shift_eq
        p hM hTH.le d.T_pos.le e.T_pos.le le_rfl W zr.2
      rw [hshift] at hGshift hRshift
      have hrposr : 0 < r := by simpa [r] using hrpos
      have heat_add (A B : WholeLineBUC) :
          wholeLineCauchyHeatBUCTotal r (A + B) =
            wholeLineCauchyHeatBUCTotal r A +
              wholeLineCauchyHeatBUCTotal r B := by
        simp only [wholeLineCauchyHeatBUCTotal, dif_pos hrposr]
        exact map_add (wholeLineCauchyHeatBUCCLM r hrposr) A B
      have heat_smul (c : ℝ) (A : WholeLineBUC) :
          wholeLineCauchyHeatBUCTotal r (c • A) =
            c • wholeLineCauchyHeatBUCTotal r A := by
        simp only [wholeLineCauchyHeatBUCTotal, dif_pos hrposr]
        exact map_smul (wholeLineCauchyHeatBUCCLM r hrposr) c A
      have hheatWT :
          wholeLineCauchyHeatBUCTotal r
              (W ⟨T, d.T_pos.le, le_add_of_nonneg_right e.T_pos.le⟩) =
            wholeLineCauchyHeatBUCTotal (T + r) u₀ +
              (-p.χ) • wholeLineCauchyHeatBUCTotal r
                (wholeLineCauchyGradientDuhamelBUC p hM hTH.le W T) +
              wholeLineCauchyHeatBUCTotal r
                (wholeLineCauchyValueDuhamelBUC p hM hTH.le W T) := by
        rw [hWTformula, heat_add, heat_add, heat_smul,
          wholeLineCauchyHeatBUCTotal_add_time hrposr d.T_pos]
        congr 2
        · congr 1
          linarith [htime]
      have hcombine :
          wholeLineCauchyHeatBUCTotal (T + r) u₀ +
              (-p.χ) •
                (wholeLineCauchyHeatBUCTotal r
                    (wholeLineCauchyGradientDuhamelBUC p hM hTH.le W T) +
                  wholeLineCauchyGradientDuhamelBUC
                    p hM e.T_pos.le e.traj r) +
              (wholeLineCauchyHeatBUCTotal r
                    (wholeLineCauchyValueDuhamelBUC p hM hTH.le W T) +
                  wholeLineCauchyValueDuhamelBUC
                    p hM e.T_pos.le e.traj r) =
            wholeLineCauchyHeatBUCTotal r
                (W ⟨T, d.T_pos.le,
                  le_add_of_nonneg_right e.T_pos.le⟩) +
              (-p.χ) • wholeLineCauchyGradientDuhamelBUC
                p hM e.T_pos.le e.traj r +
              wholeLineCauchyValueDuhamelBUC
                p hM e.T_pos.le e.traj r := by
        rw [hheatWT]
        module
      change
        (wholeLineCauchyBUCMildMap p hM hTH.le u₀ W z).1 x = (W z).1 x
      rw [wholeLineCauchyBUCMildMap_apply]
      change
        (wholeLineCauchyHeatBUCTotal z.1 u₀ +
            (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hTH.le W z.1 +
            wholeLineCauchyValueDuhamelBUC p hM hTH.le W z.1).1 x =
          (W z).1 x
      rw [← htime, hGrestart, hRrestart, ← hGshift, ← hRshift,
        hcombine, hWT, hWz, hEformula]
  refine ⟨
    { T_pos := hTH
      traj := W
      nonnegative := fun z x => (hstripW z x).1
      mild := ?_ }⟩
  intro z x
  have hmap := congrArg
    (fun Q : WholeLineBUCTrajectory (T + H) => (Q z).1 x) hfixedW
  have hbridge := wholeLineCauchyBUCMildMap_apply_eq_original_of_mem_Icc
    p hM hTH.le u₀ W hstripW z x
  exact hmap.symm.trans hbridge

section AxiomAudit

#print axioms wholeLineBUCTrajectoryAppend
#print axioms WholeLinePhysicalMildSegment.append

end AxiomAudit

end WholeLinePhysicalMildSegment

end ShenWork.Paper1
