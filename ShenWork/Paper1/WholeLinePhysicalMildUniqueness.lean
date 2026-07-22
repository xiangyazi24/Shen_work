import ShenWork.Paper1.WholeLineCauchyCanonicalRestart
import ShenWork.Paper1.WholeLineCauchyCanonicalSegments
import ShenWork.Paper1.WholeLineCauchyNonnegativity

/-!
# Uniqueness interfaces for physical whole-line BUC mild trajectories

This file supplies the converse of the usual ``fixed point implies original
mild equation`` bridge.  A continuous BUC trajectory which stays in the
physical strip and satisfies the original mild equation is a fixed point of
the truncated BUC map.  On a contraction window it is therefore the
canonical fixed point.
-/

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-- On a physical trajectory, one application of the truncated BUC map is
pointwise the original, untruncated mild map. -/
theorem wholeLineCauchyBUCMildMap_apply_eq_original_of_mem_Icc
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) :
    (wholeLineCauchyBUCMildMap p hM hT u₀ U z).1 x =
      wholeLineCauchyMildMap p u₀.1
        (fun t y => (wholeLineBUCTrajectoryExtend hT U t).1 y) z.1 x := by
  let ue : ℝ → ℝ → ℝ :=
    fun t x => (wholeLineBUCTrajectoryExtend hT U t).1 x
  let F : ℝ → WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U
  let R : ℝ → WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U
  have hextStrip (s x : ℝ) : ue s x ∈ Set.Icc (0 : ℝ) M := by
    dsimp [ue, wholeLineBUCTrajectoryExtend]
    exact hstrip (Set.projIcc 0 T hT s) x
  have hF (s : ℝ) : (F s).1 = wholeLineChemotaxisFlux p (ue s) := by
    apply funext
    intro y
    change wholeLineCauchyTruncatedFlux p M
      (wholeLineBUCTrajectoryExtend hT U s).1 y =
        wholeLineChemotaxisFlux p (ue s) y
    exact congrFun
      (wholeLineCauchyTruncatedFlux_eq_of_mem_Icc p hM (hextStrip s)) y
  have hR (s : ℝ) : (R s).1 = wholeLineCauchyShiftedReaction p (ue s) := by
    apply funext
    intro y
    change wholeLineCauchyTruncatedReaction p M
      (wholeLineBUCTrajectoryExtend hT U s).1 y =
        wholeLineCauchyShiftedReaction p (ue s) y
    exact congrFun
      (wholeLineCauchyTruncatedReaction_eq_of_mem_Icc p hM (hextStrip s)) y
  by_cases hz : z.1 = 0
  · have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hzEq : z = ⟨0, hzero⟩ := Subtype.ext hz
    rw [hzEq]
    simp [wholeLineCauchyBUCMildMap, wholeLineCauchyMildMap,
      wholeLineCauchyGradientDuhamelBUC,
      wholeLineCauchyValueDuhamelBUC,
      wholeLineCauchyHeatBUCTotal]
  · have hzpos : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz)
    have hgradBUC :
        (wholeLineCauchyGradientDuhamelBUC p hM hT U z.1).1 x =
          wholeLineCauchyGradientHistory F z.1 x := by
      rw [wholeLineCauchyGradientDuhamelBUC_apply p hM hT U hzpos.le x]
      unfold wholeLineCauchyGradientHistory
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume z.1] with s hne hs
      rw [Set.uIoc_of_le hzpos.le] at hs
      exact wholeLineCauchyGradientBUCIntegrand_apply_eq_of_lt
        p hM hT U (lt_of_le_of_ne hs.2 hne) x
    have hgrad : wholeLineCauchyGradientHistory F z.1 x =
        wholeLineCauchyGradientDuhamel
          (fun s => wholeLineChemotaxisFlux p (ue s)) z.1 x := by
      unfold wholeLineCauchyGradientHistory wholeLineCauchyGradientDuhamel
      simp_rw [hF]
    have hvalueBUC :
        (wholeLineCauchyValueDuhamelBUC p hM hT U z.1).1 x =
          wholeLineCauchyValueHistory R z.1 x := by
      rw [wholeLineCauchyValueDuhamelBUC_apply p hM hT U hzpos.le x]
      unfold wholeLineCauchyValueHistory
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume z.1] with s hne hs
      rw [Set.uIoc_of_le hzpos.le] at hs
      exact wholeLineCauchyValueBUCIntegrand_apply_eq_of_lt
        p hM hT U (lt_of_le_of_ne hs.2 hne) x
    have hvalue : wholeLineCauchyValueHistory R z.1 x =
        wholeLineCauchyValueDuhamel
          (fun s => wholeLineCauchyShiftedReaction p (ue s)) z.1 x := by
      unfold wholeLineCauchyValueHistory wholeLineCauchyValueDuhamel
      simp_rw [hR]
      rw [intervalIntegral.integral_of_le hzpos.le,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [wholeLineCauchyBUCMildMap_apply]
    change
      (wholeLineCauchyHeatBUCTotal z.1 u₀).1 x +
          (-p.χ) *
            (wholeLineCauchyGradientDuhamelBUC p hM hT U z.1).1 x +
        (wholeLineCauchyValueDuhamelBUC p hM hT U z.1).1 x = _
    rw [hgradBUC, hvalueBUC, hgrad, hvalue]
    simpa [wholeLineCauchyMildMap, hz,
      wholeLineCauchyChemDuhamel, wholeLineCauchyReactionDuhamel,
      wholeLineCauchyHeatBUCTotal, hzpos, ue, smul_eq_mul]

/-- A physical original mild trajectory is a fixed point of the truncated
BUC map. -/
theorem wholeLinePhysicalOriginalMild_isFixedPt
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (hstrip : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (hmild : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x = wholeLineCauchyMildMap p u₀.1
        (fun t y => (wholeLineBUCTrajectoryExtend hT U t).1 y) z.1 x) :
    IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀) U := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  exact (wholeLineCauchyBUCMildMap_apply_eq_original_of_mem_Icc
    p hM hT u₀ U hstrip z x).trans (hmild z x).symm

/-- On a contraction window, every physical solution of the original mild
equation is the canonical BUC fixed point. -/
theorem wholeLinePhysicalOriginalMild_eq_canonical
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (hmild : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x = wholeLineCauchyMildMap p u₀.1
        (fun t y => (wholeLineBUCTrajectoryExtend hT U t).1 y) z.1 x) :
    U = wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall := by
  have hfixed := wholeLinePhysicalOriginalMild_isFixedPt
    p hM hT u₀ U hstrip hmild
  have hcontract := wholeLineCauchyBUCMildMap_contracting
    p hM hT u₀ hsmall
  have huniq := hcontract.fixedPoint_unique hfixed
  simpa [wholeLineCauchyBUCMildFixedPoint] using huniq

/-! ## Short-window continuation of uniqueness -/

/-- If two ambient trajectories agree through time `a`, then the difference
of their full gradient histories at `a+r` is exactly the difference of the
gradient histories of their shifted trajectories at `r`. -/
theorem wholeLineCauchyGradientDuhamelBUC_sub_eq_shift_sub
    (p : CMParams) {M T a h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hah : a + h ≤ T)
    (U W : WholeLineBUCTrajectory T)
    (heq : ∀ z : Set.Icc (0 : ℝ) T, z.1 ≤ a → U z = W z)
    (hr : r ∈ Set.Icc (0 : ℝ) h) :
    wholeLineCauchyGradientDuhamelBUC p hM hT U (a + r) -
        wholeLineCauchyGradientDuhamelBUC p hM hT W (a + r) =
      wholeLineCauchyGradientDuhamelBUC p hM hh
          (wholeLineBUCTrajectoryShift ha hh hah U) r -
        wholeLineCauchyGradientDuhamelBUC p hM hh
          (wholeLineBUCTrajectoryShift ha hh hah W) r := by
  let GU : ℝ → WholeLineBUC :=
    wholeLineCauchyGradientBUCIntegrand p hM hT U (a + r)
  let GW : ℝ → WholeLineBUC :=
    wholeLineCauchyGradientBUCIntegrand p hM hT W (a + r)
  have har0 : 0 ≤ a + r := add_nonneg ha hr.1
  have ha_ar : a ≤ a + r := le_add_of_nonneg_right hr.1
  have hUfull : IntervalIntegrable GU volume 0 (a + r) :=
    wholeLineCauchyGradientBUCIntegrand_intervalIntegrable
      p hM hT U har0
  have hWfull : IntervalIntegrable GW volume 0 (a + r) :=
    wholeLineCauchyGradientBUCIntegrand_intervalIntegrable
      p hM hT W har0
  have hUold : IntervalIntegrable GU volume 0 a := by
    apply hUfull.mono_set
    rw [Set.uIcc_of_le har0, Set.uIcc_of_le ha]
    exact Set.Icc_subset_Icc_right ha_ar
  have hWold : IntervalIntegrable GW volume 0 a := by
    apply hWfull.mono_set
    rw [Set.uIcc_of_le har0, Set.uIcc_of_le ha]
    exact Set.Icc_subset_Icc_right ha_ar
  have hUrecent : IntervalIntegrable GU volume a (a + r) := by
    apply hUfull.mono_set
    rw [Set.uIcc_of_le har0, Set.uIcc_of_le ha_ar]
    exact Set.Icc_subset_Icc_left ha
  have hWrecent : IntervalIntegrable GW volume a (a + r) := by
    apply hWfull.mono_set
    rw [Set.uIcc_of_le har0, Set.uIcc_of_le ha_ar]
    exact Set.Icc_subset_Icc_left ha
  have hold : (∫ s in (0 : ℝ)..a, GU s) = ∫ s in (0 : ℝ)..a, GW s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ha] at hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hs.1, by linarith [hs.2, hr.2, hah]⟩
    have hextU := wholeLineBUCTrajectoryExtend_eq hT U hsT
    have hextW := wholeLineBUCTrajectoryExtend_eq hT W hsT
    have hslice : wholeLineBUCTrajectoryExtend hT U s =
        wholeLineBUCTrajectoryExtend hT W s := by
      rw [hextU, hextW]
      exact heq ⟨s, hsT⟩ hs.2
    dsimp [GU, GW, wholeLineCauchyGradientBUCIntegrand,
      wholeLineCauchyFluxSourceTrajectory]
    rw [hslice]
  have hsplitU :
      wholeLineCauchyGradientDuhamelBUC p hM hT U (a + r) =
        (∫ s in (0 : ℝ)..a, GU s) + ∫ s in a..(a + r), GU s := by
    unfold wholeLineCauchyGradientDuhamelBUC
    exact (intervalIntegral.integral_add_adjacent_intervals
      hUold hUrecent).symm
  have hsplitW :
      wholeLineCauchyGradientDuhamelBUC p hM hT W (a + r) =
        (∫ s in (0 : ℝ)..a, GW s) + ∫ s in a..(a + r), GW s := by
    unfold wholeLineCauchyGradientDuhamelBUC
    exact (intervalIntegral.integral_add_adjacent_intervals
      hWold hWrecent).symm
  have hshiftU := wholeLineCauchyGradientDuhamelBUC_shift_eq
    p hM hT ha hh hah U hr
  have hshiftW := wholeLineCauchyGradientDuhamelBUC_shift_eq
    p hM hT ha hh hah W hr
  rw [hsplitU, hsplitW, hold, hshiftU, hshiftW]
  abel

/-- The analogous recent-history identity for the value Duhamel term. -/
theorem wholeLineCauchyValueDuhamelBUC_sub_eq_shift_sub
    (p : CMParams) {M T a h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hah : a + h ≤ T)
    (U W : WholeLineBUCTrajectory T)
    (heq : ∀ z : Set.Icc (0 : ℝ) T, z.1 ≤ a → U z = W z)
    (hr : r ∈ Set.Icc (0 : ℝ) h) :
    wholeLineCauchyValueDuhamelBUC p hM hT U (a + r) -
        wholeLineCauchyValueDuhamelBUC p hM hT W (a + r) =
      wholeLineCauchyValueDuhamelBUC p hM hh
          (wholeLineBUCTrajectoryShift ha hh hah U) r -
        wholeLineCauchyValueDuhamelBUC p hM hh
          (wholeLineBUCTrajectoryShift ha hh hah W) r := by
  let RU : ℝ → WholeLineBUC :=
    wholeLineCauchyValueBUCIntegrand p hM hT U (a + r)
  let RW : ℝ → WholeLineBUC :=
    wholeLineCauchyValueBUCIntegrand p hM hT W (a + r)
  have har0 : 0 ≤ a + r := add_nonneg ha hr.1
  have ha_ar : a ≤ a + r := le_add_of_nonneg_right hr.1
  have hUfull : IntervalIntegrable RU volume 0 (a + r) :=
    wholeLineCauchyValueBUCIntegrand_intervalIntegrable p hM hT U har0
  have hWfull : IntervalIntegrable RW volume 0 (a + r) :=
    wholeLineCauchyValueBUCIntegrand_intervalIntegrable p hM hT W har0
  have hUold : IntervalIntegrable RU volume 0 a := by
    apply hUfull.mono_set
    rw [Set.uIcc_of_le har0, Set.uIcc_of_le ha]
    exact Set.Icc_subset_Icc_right ha_ar
  have hWold : IntervalIntegrable RW volume 0 a := by
    apply hWfull.mono_set
    rw [Set.uIcc_of_le har0, Set.uIcc_of_le ha]
    exact Set.Icc_subset_Icc_right ha_ar
  have hUrecent : IntervalIntegrable RU volume a (a + r) := by
    apply hUfull.mono_set
    rw [Set.uIcc_of_le har0, Set.uIcc_of_le ha_ar]
    exact Set.Icc_subset_Icc_left ha
  have hWrecent : IntervalIntegrable RW volume a (a + r) := by
    apply hWfull.mono_set
    rw [Set.uIcc_of_le har0, Set.uIcc_of_le ha_ar]
    exact Set.Icc_subset_Icc_left ha
  have hold : (∫ s in (0 : ℝ)..a, RU s) = ∫ s in (0 : ℝ)..a, RW s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ha] at hs
    have hsT : s ∈ Set.Icc (0 : ℝ) T :=
      ⟨hs.1, by linarith [hs.2, hr.2, hah]⟩
    have hextU := wholeLineBUCTrajectoryExtend_eq hT U hsT
    have hextW := wholeLineBUCTrajectoryExtend_eq hT W hsT
    have hslice : wholeLineBUCTrajectoryExtend hT U s =
        wholeLineBUCTrajectoryExtend hT W s := by
      rw [hextU, hextW]
      exact heq ⟨s, hsT⟩ hs.2
    dsimp [RU, RW, wholeLineCauchyValueBUCIntegrand,
      wholeLineCauchyReactionSourceTrajectory]
    rw [hslice]
  have hsplitU :
      wholeLineCauchyValueDuhamelBUC p hM hT U (a + r) =
        (∫ s in (0 : ℝ)..a, RU s) + ∫ s in a..(a + r), RU s := by
    unfold wholeLineCauchyValueDuhamelBUC
    exact (intervalIntegral.integral_add_adjacent_intervals
      hUold hUrecent).symm
  have hsplitW :
      wholeLineCauchyValueDuhamelBUC p hM hT W (a + r) =
        (∫ s in (0 : ℝ)..a, RW s) + ∫ s in a..(a + r), RW s := by
    unfold wholeLineCauchyValueDuhamelBUC
    exact (intervalIntegral.integral_add_adjacent_intervals
      hWold hWrecent).symm
  have hshiftU := wholeLineCauchyValueDuhamelBUC_shift_eq
    p hM hT ha hh hah U hr
  have hshiftW := wholeLineCauchyValueDuhamelBUC_shift_eq
    p hM hT ha hh hah W hr
  rw [hsplitU, hsplitW, hold, hshiftU, hshiftW]
  abel

/-- Equality through `a` propagates across one short contraction window. -/
theorem wholeLinePhysicalMild_eq_on_next_short_window
    (p : CMParams) {M T a h : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hah : a + h ≤ T)
    (hsmall : wholeLineCauchyBUCMildRate p M h < 1)
    (u₀ : WholeLineBUC) (U W : WholeLineBUCTrajectory T)
    (hfixedU : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀) U)
    (hfixedW : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀) W)
    (heq : ∀ z : Set.Icc (0 : ℝ) T, z.1 ≤ a → U z = W z) :
    wholeLineBUCTrajectoryShift ha hh hah U =
      wholeLineBUCTrajectoryShift ha hh hah W := by
  let VU : WholeLineBUCTrajectory h :=
    wholeLineBUCTrajectoryShift ha hh hah U
  let VW : WholeLineBUCTrajectory h :=
    wholeLineBUCTrajectoryShift ha hh hah W
  have hpoint : ∀ z : Set.Icc (0 : ℝ) h,
      dist (VU z) (VW z) ≤
        wholeLineCauchyBUCMildRate p M h * dist VU VW := by
    intro z
    let zT : Set.Icc (0 : ℝ) T :=
      ⟨a + z.1, add_nonneg ha z.2.1,
        by linarith [z.2.2, hah]⟩
    have hfixUz := congrArg
      (fun Q : WholeLineBUCTrajectory T => Q zT) hfixedU
    have hfixWz := congrArg
      (fun Q : WholeLineBUCTrajectory T => Q zT) hfixedW
    have hfixUz' :
        wholeLineCauchyBUCMildMap p hM hT u₀ U zT = U zT := by
      simpa only using hfixUz
    have hfixWz' :
        wholeLineCauchyBUCMildMap p hM hT u₀ W zT = W zT := by
      simpa only using hfixWz
    have hgrad := wholeLineCauchyGradientDuhamelBUC_sub_eq_shift_sub
      p hM hT ha hh hah U W heq z.2
    have hvalue := wholeLineCauchyValueDuhamelBUC_sub_eq_shift_sub
      p hM hT ha hh hah U W heq z.2
    have hsub : VU z - VW z =
        wholeLineCauchyBUCMildMap p hM hh
            (U ⟨a, ha, (le_add_of_nonneg_right hh).trans hah⟩) VU z -
          wholeLineCauchyBUCMildMap p hM hh
            (U ⟨a, ha, (le_add_of_nonneg_right hh).trans hah⟩) VW z := by
      change U zT - W zT = _
      rw [← hfixUz', ← hfixWz']
      simp only [wholeLineCauchyBUCMildMap_apply]
      change
        (wholeLineCauchyHeatBUCTotal (a + z.1) u₀ +
              (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U (a + z.1) +
            wholeLineCauchyValueDuhamelBUC p hM hT U (a + z.1)) -
          (wholeLineCauchyHeatBUCTotal (a + z.1) u₀ +
              (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT W (a + z.1) +
            wholeLineCauchyValueDuhamelBUC p hM hT W (a + z.1)) = _
      calc
        _ = (-p.χ) •
              (wholeLineCauchyGradientDuhamelBUC p hM hT U (a + z.1) -
                wholeLineCauchyGradientDuhamelBUC p hM hT W (a + z.1)) +
              (wholeLineCauchyValueDuhamelBUC p hM hT U (a + z.1) -
                wholeLineCauchyValueDuhamelBUC p hM hT W (a + z.1)) := by
            module
        _ = (-p.χ) •
              (wholeLineCauchyGradientDuhamelBUC p hM hh VU z.1 -
                wholeLineCauchyGradientDuhamelBUC p hM hh VW z.1) +
              (wholeLineCauchyValueDuhamelBUC p hM hh VU z.1 -
                wholeLineCauchyValueDuhamelBUC p hM hh VW z.1) := by
            rw [hgrad, hvalue]
        _ = _ := by module
    rw [WholeLineBUC.dist_eq_norm_sub, hsub,
      ← WholeLineBUC.dist_eq_norm_sub]
    exact wholeLineCauchyBUCMildMap_apply_dist_le
      p hM hh (U ⟨a, ha, (le_add_of_nonneg_right hh).trans hah⟩) VU VW z
  have hdist : dist VU VW ≤
      wholeLineCauchyBUCMildRate p M h * dist VU VW := by
    refine (ContinuousMap.dist_le
      (mul_nonneg (wholeLineCauchyBUCMildRate_nonneg p hM hh) dist_nonneg)).2 ?_
    exact hpoint
  have hzero : dist VU VW = 0 := by
    have hd0 : 0 ≤ dist VU VW := dist_nonneg
    nlinarith
  exact dist_eq_zero.mp hzero

/-- Physical BUC mild trajectories with the same datum are unique on every
finite horizon.  The proof advances by finitely many short contraction
windows; no large-time contraction hypothesis is used. -/
theorem wholeLinePhysicalOriginalMild_unique
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U W : WholeLineBUCTrajectory T)
    (hstripU : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (hstripW : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (W z).1 x ∈ Set.Icc (0 : ℝ) M)
    (hmildU : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x = wholeLineCauchyMildMap p u₀.1
        (fun t y => (wholeLineBUCTrajectoryExtend hT U t).1 y) z.1 x)
    (hmildW : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (W z).1 x = wholeLineCauchyMildMap p u₀.1
        (fun t y => (wholeLineBUCTrajectoryExtend hT W t).1 y) z.1 x) :
    U = W := by
  have hfixedU := wholeLinePhysicalOriginalMild_isFixedPt
    p hM hT u₀ U hstripU hmildU
  have hfixedW := wholeLinePhysicalOriginalMild_isFixedPt
    p hM hT u₀ W hstripW hmildW
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_time_wholeLineCauchyBUCMildRate_lt_one p hM
  have hstep : ∀ n : ℕ, ∀ z : Set.Icc (0 : ℝ) T,
      z.1 ≤ (n : ℝ) * δ → U z = W z := by
    intro n
    induction n with
    | zero =>
        intro z hz
        have hz0 : z.1 = 0 := by
          norm_num at hz
          exact le_antisymm hz z.2.1
        apply Subtype.ext
        apply BoundedContinuousFunction.ext
        intro x
        have hu := hmildU z x
        have hw := hmildW z x
        have hu0 : (U z).1 x = u₀.1 x := by
          simpa [wholeLineCauchyMildMap, hz0] using hu
        have hw0 : (W z).1 x = u₀.1 x := by
          simpa [wholeLineCauchyMildMap, hz0] using hw
        exact hu0.trans hw0.symm
    | succ n ih =>
        intro z hz
        let a : ℝ := min T ((n : ℝ) * δ)
        let b : ℝ := min T (((n + 1 : ℕ) : ℝ) * δ)
        let h : ℝ := b - a
        have ha0 : 0 ≤ a := by
          dsimp [a]
          exact le_min hT (mul_nonneg (Nat.cast_nonneg n) hδ.le)
        have hab : a ≤ b := by
          dsimp [a, b]
          apply min_le_min le_rfl
          push_cast
          nlinarith
        have hbT : b ≤ T := by
          dsimp [b]
          exact min_le_left _ _
        have hh0 : 0 ≤ h := sub_nonneg.mpr hab
        have hah : a + h ≤ T := by
          dsimp [h]
          linarith
        have ha_n : a ≤ (n : ℝ) * δ := by
          dsimp [a]
          exact min_le_right _ _
        have hhδ : h ≤ δ := by
          dsimp [h, a, b]
          by_cases hnT : (n : ℝ) * δ ≤ T
          · rw [min_eq_right hnT]
            have hb : min T (((n + 1 : ℕ) : ℝ) * δ) ≤
                ((n : ℝ) * δ) + δ := by
              apply le_trans (min_le_right _ _)
              push_cast
              ring_nf
              exact le_rfl
            linarith
          · have hTn : T ≤ (n : ℝ) * δ := le_of_not_ge hnT
            rw [min_eq_left hTn]
            have hTsucc : T ≤ (((n + 1 : ℕ) : ℝ) * δ) := by
              apply hTn.trans
              push_cast
              nlinarith [hδ]
            have hTb : min T (((n + 1 : ℕ) : ℝ) * δ) = T :=
              min_eq_left hTsucc
            rw [hTb]
            linarith [hδ]
        have hsmallh : wholeLineCauchyBUCMildRate p M h < 1 :=
          lt_of_le_of_lt
            (wholeLineCauchyBUCMildRate_mono p hM hh0 hhδ) hsmall
        have heqA : ∀ q : Set.Icc (0 : ℝ) T, q.1 ≤ a → U q = W q := by
          intro q hqa
          exact ih q (hqa.trans ha_n)
        have hshift := wholeLinePhysicalMild_eq_on_next_short_window
          p hM hT ha0 hh0 hah hsmallh u₀ U W hfixedU hfixedW heqA
        have hzB : z.1 ≤ b := by
          apply le_min z.2.2
          exact hz
        by_cases hza : z.1 ≤ a
        · exact heqA z hza
        · let r : ℝ := z.1 - a
          have hr0 : 0 ≤ r := sub_nonneg.mpr (le_of_not_ge hza)
          have hrh : r ≤ h := by dsimp [r, h]; linarith
          have happ := congrArg
            (fun Q : WholeLineBUCTrajectory h => Q ⟨r, hr0, hrh⟩) hshift
          simpa [r, wholeLineBUCTrajectoryShift] using happ
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hTn : T ≤ (n : ℝ) * δ := by
    have := (div_lt_iff₀ hδ).mp hn
    exact this.le
  apply ContinuousMap.ext
  intro z
  exact hstep n z (z.2.2.trans hTn)

/-! ## Canonical restart of an arbitrary physical fixed point -/

/-- A positive-time short window of an arbitrary fixed point is canonical as
soon as the already elapsed flux history has the bounded `C¹` regularity
needed by the heat-gradient cocycle. -/
theorem wholeLinePhysicalFixedPoint_shift_eq_of_fluxC1
    (p : CMParams) {M T a h : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀) U)
    (ha : 0 < a) (hh : 0 < h) (hah : a + h ≤ T)
    (hsmallh : wholeLineCauchyBUCMildRate p M h < 1)
    (hFderiv : ∀ s ∈ Set.Ioc (0 : ℝ) a, ∀ y,
      HasDerivAt
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1
        (deriv (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 y) y)
    (hFderiv_cont : ∀ s ∈ Set.Ioc (0 : ℝ) a,
      Continuous
        (deriv (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1))
    (hFderiv_bound : ∀ s ∈ Set.Ioc (0 : ℝ) a, ∃ D : ℝ, ∀ y,
      |deriv (wholeLineCauchyFluxSourceTrajectory p hM hT U s).1 y| ≤ D) :
    let za : Set.Icc (0 : ℝ) T :=
      ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
    wholeLineBUCTrajectoryShift ha.le hh.le hah U =
      wholeLineCauchyBUCMildFixedPoint p hM hh.le (U za) hsmallh := by
  dsimp only
  let za : Set.Icc (0 : ℝ) T :=
    ⟨a, ha.le, (le_add_of_nonneg_right hh.le).trans hah⟩
  let V : WholeLineBUCTrajectory h :=
    wholeLineBUCTrajectoryShift ha.le hh.le hah U
  have hVfixed :
      IsFixedPt (wholeLineCauchyBUCMildMap p hM hh.le (U za)) V := by
    apply ContinuousMap.ext
    intro z
    let r : ℝ := z.1
    have hr : r ∈ Set.Icc (0 : ℝ) h := z.2
    by_cases hr0 : r = 0
    · have hz0 : z = ⟨0, ⟨le_rfl, hh.le⟩⟩ := Subtype.ext hr0
      subst z
      simp [V, za, wholeLineCauchyBUCMildMap,
        wholeLineCauchyGradientDuhamelBUC,
        wholeLineCauchyValueDuhamelBUC,
        wholeLineCauchyHeatBUCTotal]
    · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
      let zar : Set.Icc (0 : ℝ) T :=
        ⟨a + r, add_nonneg ha.le hr.1, by linarith [hr.2, hah]⟩
      have hUa : U za =
          wholeLineCauchyHeatBUCTotal a u₀ +
            (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U a +
            wholeLineCauchyValueDuhamelBUC p hM hT U a := by
        have hf := congrArg (fun Q : WholeLineBUCTrajectory T => Q za)
          hfixed.symm
        simpa [za, wholeLineCauchyBUCMildMap] using hf
      have hUar : U zar =
          wholeLineCauchyHeatBUCTotal (a + r) u₀ +
            (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U (a + r) +
            wholeLineCauchyValueDuhamelBUC p hM hT U (a + r) := by
        have hf := congrArg (fun Q : WholeLineBUCTrajectory T => Q zar)
          hfixed.symm
        simpa [zar, wholeLineCauchyBUCMildMap] using hf
      have hGrestart := wholeLineCauchyGradientDuhamelBUC_restart
        p hM hT U ha hrpos hFderiv hFderiv_cont hFderiv_bound
      have hRrestart := wholeLineCauchyValueDuhamelBUC_restart
        p hM hT U ha hrpos
      have hGshift := wholeLineCauchyGradientDuhamelBUC_shift_eq
        p hM hT ha.le hh.le hah U hr
      have hRshift := wholeLineCauchyValueDuhamelBUC_shift_eq
        p hM hT ha.le hh.le hah U hr
      have heat_add (A B : WholeLineBUC) :
          wholeLineCauchyHeatBUCTotal r (A + B) =
            wholeLineCauchyHeatBUCTotal r A +
              wholeLineCauchyHeatBUCTotal r B := by
        simp only [wholeLineCauchyHeatBUCTotal, dif_pos hrpos]
        change wholeLineCauchyHeatBUCCLM r hrpos (A + B) =
          wholeLineCauchyHeatBUCCLM r hrpos A +
            wholeLineCauchyHeatBUCCLM r hrpos B
        exact map_add (wholeLineCauchyHeatBUCCLM r hrpos) A B
      have heat_smul (c : ℝ) (A : WholeLineBUC) :
          wholeLineCauchyHeatBUCTotal r (c • A) =
            c • wholeLineCauchyHeatBUCTotal r A := by
        simp only [wholeLineCauchyHeatBUCTotal, dif_pos hrpos]
        change wholeLineCauchyHeatBUCCLM r hrpos (c • A) =
          c • wholeLineCauchyHeatBUCCLM r hrpos A
        exact map_smul (wholeLineCauchyHeatBUCCLM r hrpos) c A
      have hheatUa :
          wholeLineCauchyHeatBUCTotal r (U za) =
            wholeLineCauchyHeatBUCTotal (a + r) u₀ +
              (-p.χ) • wholeLineCauchyHeatBUCTotal r
                (wholeLineCauchyGradientDuhamelBUC p hM hT U a) +
              wholeLineCauchyHeatBUCTotal r
                (wholeLineCauchyValueDuhamelBUC p hM hT U a) := by
        rw [hUa, heat_add, heat_add, heat_smul]
        rw [wholeLineCauchyHeatBUCTotal_add_time hrpos ha]
        simpa [add_comm]
      change wholeLineCauchyBUCMildMap p hM hh.le (U za) V z = V z
      change
        wholeLineCauchyHeatBUCTotal r (U za) +
            (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hh.le V r +
          wholeLineCauchyValueDuhamelBUC p hM hh.le V r = U zar
      symm
      rw [hUar, hGrestart, hRrestart, hGshift, hRshift, hheatUa]
      module
  have hcontract := wholeLineCauchyBUCMildMap_contracting
    p hM hh.le (U za) hsmallh
  have huniq := hcontract.fixedPoint_unique hVfixed
  simpa [V, za, wholeLineCauchyBUCMildFixedPoint] using huniq

/-- Restriction of any fixed point to a shorter initial contraction horizon
is the canonical fixed point on that horizon. -/
theorem wholeLineFixedPoint_restrict_eq_canonical
    (p : CMParams) {M T h : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀) U)
    (hh : 0 ≤ h) (hhT : h ≤ T)
    (hsmallh : wholeLineCauchyBUCMildRate p M h < 1) :
    wholeLineBUCTrajectoryShift le_rfl hh (by simpa using hhT) U =
      wholeLineCauchyBUCMildFixedPoint p hM hh u₀ hsmallh := by
  let V : WholeLineBUCTrajectory h :=
    wholeLineBUCTrajectoryShift le_rfl hh (by simpa using hhT) U
  have hVfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hh u₀) V := by
    apply ContinuousMap.ext
    intro z
    let r : ℝ := z.1
    have hr : r ∈ Set.Icc (0 : ℝ) h := z.2
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, hr.1, hr.2.trans hhT⟩
    have hUr : U zr =
        wholeLineCauchyHeatBUCTotal r u₀ +
          (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U r +
          wholeLineCauchyValueDuhamelBUC p hM hT U r := by
      have hf := congrArg (fun Q : WholeLineBUCTrajectory T => Q zr)
        hfixed.symm
      simpa [zr, wholeLineCauchyBUCMildMap] using hf
    have hGshift := wholeLineCauchyGradientDuhamelBUC_shift_eq
      p hM hT le_rfl hh (by simpa using hhT) U hr
    have hRshift := wholeLineCauchyValueDuhamelBUC_shift_eq
      p hM hT le_rfl hh (by simpa using hhT) U hr
    have hG : wholeLineCauchyGradientDuhamelBUC p hM hh V r =
        wholeLineCauchyGradientDuhamelBUC p hM hT U r := by
      simpa [V, wholeLineCauchyGradientDuhamelBUC] using hGshift
    have hR : wholeLineCauchyValueDuhamelBUC p hM hh V r =
        wholeLineCauchyValueDuhamelBUC p hM hT U r := by
      simpa [V, wholeLineCauchyValueDuhamelBUC] using hRshift
    rw [wholeLineCauchyBUCMildMap_apply, hG, hR, ← hUr]
    simp [V, zr, r, wholeLineBUCTrajectoryShift]
  have hcontract := wholeLineCauchyBUCMildMap_contracting
    p hM hh u₀ hsmallh
  have huniq := hcontract.fixedPoint_unique hVfixed
  simpa [V, wholeLineCauchyBUCMildFixedPoint] using huniq

/-- Spatial bounded-`C¹` data in exactly the form needed by the gradient
Duhamel restart identity. -/
def WholeLineBUCSpatialC1 (F : WholeLineBUC) : Prop :=
  (∀ y, HasDerivAt F.1 (deriv F.1 y) y) ∧
    Continuous (deriv F.1) ∧
    ∃ D : ℝ, ∀ y, |deriv F.1 y| ≤ D

/-- Every positive-time flux slice of a physical fixed point has the bounded
`C¹` data required for restart.  The proof propagates canonical charts by
short contraction windows. -/
theorem wholeLinePhysicalFixedPoint_fluxSource_spatialC1_positive
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT.le u₀) U)
    (hstrip : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x ∈ Set.Icc (0 : ℝ) M) :
    ∀ s ∈ Set.Ioc (0 : ℝ) T,
      WholeLineBUCSpatialC1
        (wholeLineCauchyFluxSourceTrajectory p hM hT.le U s) := by
  obtain ⟨δ, hδ, hsmall⟩ :=
    exists_pos_time_wholeLineCauchyBUCMildRate_lt_one p hM
  have hstage : ∀ n : ℕ, ∀ s ∈ Set.Ioc (0 : ℝ)
      (min T ((n : ℝ) * δ)),
      WholeLineBUCSpatialC1
        (wholeLineCauchyFluxSourceTrajectory p hM hT.le U s) := by
    intro n
    induction n with
    | zero =>
        intro s hs
        norm_num at hs
    | succ n ih =>
        let a : ℝ := min T ((n : ℝ) * δ)
        let b : ℝ := min T (((n + 1 : ℕ) : ℝ) * δ)
        let h : ℝ := b - a
        have ha0 : 0 ≤ a := by
          dsimp [a]
          exact le_min hT.le (mul_nonneg (Nat.cast_nonneg n) hδ.le)
        have hab : a ≤ b := by
          dsimp [a, b]
          apply min_le_min le_rfl
          push_cast
          nlinarith
        have hbT : b ≤ T := min_le_left _ _
        have hh0 : 0 ≤ h := sub_nonneg.mpr hab
        have hah : a + h ≤ T := by dsimp [h]; linarith
        have ha_n : a ≤ (n : ℝ) * δ := min_le_right _ _
        have hhδ : h ≤ δ := by
          dsimp [h, a, b]
          by_cases hnT : (n : ℝ) * δ ≤ T
          · rw [min_eq_right hnT]
            have hb : min T (((n + 1 : ℕ) : ℝ) * δ) ≤
                ((n : ℝ) * δ) + δ := by
              apply le_trans (min_le_right _ _)
              push_cast
              ring_nf
              exact le_rfl
            linarith
          · have hTn : T ≤ (n : ℝ) * δ := le_of_not_ge hnT
            rw [min_eq_left hTn]
            have hTb : min T (((n + 1 : ℕ) : ℝ) * δ) = T := by
              apply min_eq_left
              exact hTn.trans (by push_cast; nlinarith)
            rw [hTb]
            linarith [hδ]
        have hsmallh : wholeLineCauchyBUCMildRate p M h < 1 :=
          lt_of_le_of_lt
            (wholeLineCauchyBUCMildRate_mono p hM hh0 hhδ) hsmall
        intro s hs
        by_cases hsa : s ≤ a
        · exact ih s ⟨hs.1, by simpa [a] using hsa⟩
        · have hhpos : 0 < h := by
            have has : a < s := lt_of_not_ge hsa
            have hsb : s ≤ b := by simpa [b] using hs.2
            dsimp [h]
            linarith
          have hchart :
              wholeLineBUCTrajectoryShift ha0 hh0 hah U =
                wholeLineCauchyBUCMildFixedPoint p hM hh0
                  (U ⟨a, ha0, (le_add_of_nonneg_right hh0).trans hah⟩)
                  hsmallh := by
            by_cases haZero : a = 0
            ·
              let z0 : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
              have hU0 : U z0 = u₀ := by
                have hf := congrArg
                  (fun Q : WholeLineBUCTrajectory T => Q z0) hfixed
                simpa [z0, wholeLineCauchyBUCMildMap,
                  wholeLineCauchyGradientDuhamelBUC,
                  wholeLineCauchyValueDuhamelBUC,
                  wholeLineCauchyHeatBUCTotal] using hf.symm
              have hrestrict := wholeLineFixedPoint_restrict_eq_canonical
                p hM hT.le u₀ U hfixed hh0 (by linarith) hsmallh
              have hUa :
                  U ⟨a, ha0, (le_add_of_nonneg_right hh0).trans hah⟩ = u₀ := by
                have hza :
                    (⟨a, ha0,
                      (le_add_of_nonneg_right hh0).trans hah⟩ :
                        Set.Icc (0 : ℝ) T) = z0 := by
                  apply Subtype.ext
                  exact haZero
                rw [hza]
                exact hU0
              convert hrestrict using 1 <;> simp only [haZero]
              congr 1
            · have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haZero)
              apply wholeLinePhysicalFixedPoint_shift_eq_of_fluxC1
                p hM hT.le u₀ U hfixed hapos hhpos hah hsmallh
              · intro q hq y
                exact (ih q ⟨hq.1, by simpa [a] using hq.2⟩).1 y
              · intro q hq
                exact (ih q ⟨hq.1, by simpa [a] using hq.2⟩).2.1
              · intro q hq
                exact (ih q ⟨hq.1, by simpa [a] using hq.2⟩).2.2
          let r : ℝ := s - a
          have hr0 : 0 < r := sub_pos.mpr (lt_of_not_ge hsa)
          have hrh : r ≤ h := by
            have hsb : s ≤ b := by simpa [b] using hs.2
            dsimp [r, h]
            linarith
          let zr : Set.Icc (0 : ℝ) h := ⟨r, hr0.le, hrh⟩
          let V : WholeLineBUCTrajectory h :=
            wholeLineBUCTrajectoryShift ha0 hh0 hah U
          have hVeq : V = wholeLineCauchyBUCMildFixedPoint p hM hh0
              (U ⟨a, ha0, (le_add_of_nonneg_right hh0).trans hah⟩)
              hsmallh := by simpa [V] using hchart
          have hstripCanonical : ∀ x,
              (wholeLineCauchyBUCMildFixedPoint p hM hh0
                (U ⟨a, ha0, (le_add_of_nonneg_right hh0).trans hah⟩)
                hsmallh zr).1 x ∈ Set.Icc (0 : ℝ) M := by
            intro x
            rw [← hVeq]
            change (U ⟨a + r, add_nonneg ha0 hr0.le,
              (by linarith [hrh, hah] : a + r ≤ T)⟩).1 x ∈ _
            simpa [r] using hstrip
              ⟨s, hs.1.le, (by exact hs.2.trans hbT)⟩ x
          have hcanonical :=
            wholeLineCauchyFluxSourceTrajectory_restartC1Data_positive
              p hM hh0
              (U ⟨a, ha0, (le_add_of_nonneg_right hh0).trans hah⟩)
              hsmallh zr hr0
              (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
              (by norm_num) (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) hstripCanonical
          have hsourceShift := wholeLineCauchyFluxSourceTrajectory_shift_eq
            p hM hT.le ha0 hh0 hah U ⟨hr0.le, hrh⟩
          have hsource :
              wholeLineCauchyFluxSourceTrajectory p hM hT.le U s =
                wholeLineCauchyFluxSourceTrajectory p hM hh0
                  (wholeLineCauchyBUCMildFixedPoint p hM hh0
                    (U ⟨a, ha0, (le_add_of_nonneg_right hh0).trans hah⟩)
                    hsmallh) r := by
            rw [← hVeq]
            rw [hsourceShift]
            congr 1
            dsimp [r]
            ring
          rw [hsource]
          exact hcanonical
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hTn : T ≤ (n : ℝ) * δ := by
    exact ((div_lt_iff₀ hδ).mp hn).le
  exact hstage n s ⟨hs.1, by rw [min_eq_left hTn]; exact hs.2⟩

/-- A canonical restart chart containing a prescribed ambient time in its
strict interior. -/
def WholeLinePhysicalCanonicalChart
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T) (t : ℝ) : Prop :=
  ∃ a h q : ℝ,
    ∃ ha : 0 < a, ∃ hh : 0 < h,
      ∃ hq : q ∈ Set.Ioo (0 : ℝ) h,
        ∃ hah : a + h ≤ T,
          t = a + q ∧
            ∃ hsmall : wholeLineCauchyBUCMildRate p M h < 1,
              wholeLineBUCTrajectoryShift ha.le hh.le hah U =
                wholeLineCauchyBUCMildFixedPoint p hM hh.le
                  (U ⟨a, ha.le,
                    (le_add_of_nonneg_right hh.le).trans hah⟩) hsmall

/-- Every interior positive time lies strictly inside a canonical restart
chart of an arbitrary physical fixed point. -/
theorem wholeLinePhysicalFixedPoint_exists_canonical_chart
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT.le u₀) U)
    (hstrip : ∀ (z : Set.Icc (0 : ℝ) T) (x : ℝ),
      (U z).1 x ∈ Set.Icc (0 : ℝ) M)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    WholeLinePhysicalCanonicalChart p hM u₀ U t := by
  obtain ⟨d, hd, hsmalld⟩ :=
    exists_pos_time_wholeLineCauchyBUCMildRate_lt_one p hM
  let q : ℝ := min (t / 2) (min ((T - t) / 2) (d / 4))
  let a : ℝ := t - q
  let h : ℝ := 2 * q
  have hq : 0 < q := by
    dsimp [q]
    apply lt_min
    · linarith [ht.1]
    · apply lt_min
      · linarith [ht.2]
      · linarith [hd]
  have hqt : q ≤ t / 2 := by dsimp [q]; exact min_le_left _ _
  have hqT : q ≤ (T - t) / 2 := by
    dsimp [q]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hqd : q ≤ d / 4 := by
    dsimp [q]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have ha : 0 < a := by dsimp [a]; linarith
  have hh : 0 < h := by dsimp [h]; linarith
  have hqh : q ∈ Set.Ioo (0 : ℝ) h := by
    constructor
    · exact hq
    · dsimp [h]; linarith
  have hah : a + h ≤ T := by dsimp [a, h]; linarith
  have htime : t = a + q := by dsimp [a]; ring
  have hhd : h ≤ d := by dsimp [h]; linarith
  have hsmallh : wholeLineCauchyBUCMildRate p M h < 1 :=
    lt_of_le_of_lt
      (wholeLineCauchyBUCMildRate_mono p hM hh.le hhd) hsmalld
  have hflux := wholeLinePhysicalFixedPoint_fluxSource_spatialC1_positive
    p hM hT u₀ U hfixed hstrip
  refine ⟨a, h, q, ha, hh, hqh, hah, htime, hsmallh, ?_⟩
  exact wholeLinePhysicalFixedPoint_shift_eq_of_fluxC1
      p hM hT.le u₀ U hfixed ha hh hah hsmallh
        (fun s hs y => (hflux s ⟨hs.1, hs.2.trans
          ((le_add_of_nonneg_right hh.le).trans hah)⟩).1 y)
        (fun s hs => (hflux s ⟨hs.1, hs.2.trans
          ((le_add_of_nonneg_right hh.le).trans hah)⟩).2.1)
        (fun s hs => (hflux s ⟨hs.1, hs.2.trans
          ((le_add_of_nonneg_right hh.le).trans hah)⟩).2.2)

section AxiomAudit

#print axioms wholeLineCauchyBUCMildMap_apply_eq_original_of_mem_Icc
#print axioms wholeLinePhysicalOriginalMild_isFixedPt
#print axioms wholeLinePhysicalOriginalMild_eq_canonical
#print axioms wholeLineCauchyGradientDuhamelBUC_sub_eq_shift_sub
#print axioms wholeLineCauchyValueDuhamelBUC_sub_eq_shift_sub
#print axioms wholeLinePhysicalMild_eq_on_next_short_window
#print axioms wholeLinePhysicalOriginalMild_unique
#print axioms wholeLinePhysicalFixedPoint_shift_eq_of_fluxC1
#print axioms wholeLineFixedPoint_restrict_eq_canonical
#print axioms wholeLinePhysicalFixedPoint_fluxSource_spatialC1_positive
#print axioms wholeLinePhysicalFixedPoint_exists_canonical_chart

end AxiomAudit

end ShenWork.Paper1
