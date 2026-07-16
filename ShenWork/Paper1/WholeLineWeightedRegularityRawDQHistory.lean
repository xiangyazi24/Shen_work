import ShenWork.Paper1.WholeLineWeightedRegularityActualL2History
import ShenWork.Paper1.WholeLineWeightedRegularityCoMovingMatchedSource
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQIdentity

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical raw-DQ histories on a positive restart window

The histories in this file compare a canonical BUC trajectory with a fixed
co-moving profile.  The fixed profile is realized in laboratory coordinates
by `wholeLineBUCTranslateTrajectory`; consequently both nonlinear legs are
handled by the same already-continuous BUC Duhamel integrands.  Applying the
bounded raw-DQ map only after taking their difference avoids any derivative
assumption on the canonical trajectory.
-/

/-- Cap-weighted raw-DQ flux history before terminal-zero totalization. -/
def capWeightedCoMovingFluxRawDQBUCHistory
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (r s : ℝ) : WholeLineBUC :=
  capWeightSqrtMulBUC eta R heta
    (wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
      (wholeLineBUCTranslate (c * r)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyGradientBUCIntegrand p hM hT Traj r s)
          (wholeLineCauchyGradientBUCIntegrand p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) r s))))

/-- Cap-weighted raw-DQ reaction history before terminal-zero totalization. -/
def capWeightedCoMovingReactionRawDQBUCHistory
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (r s : ℝ) : WholeLineBUC :=
  capWeightSqrtMulBUC eta R heta
    (wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
      (wholeLineBUCTranslate (c * r)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyValueBUCIntegrand p hM hT Traj r s)
          (wholeLineCauchyValueBUCIntegrand p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) r s))))

/-- Terminal-zero totalization of the raw-DQ flux history. -/
def capWeightedCoMovingFluxRawDQBUCHistoryIio
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (r s : ℝ) : WholeLineBUC :=
  if s < r then
    capWeightedCoMovingFluxRawDQBUCHistory
      p hM hT eta R c h heta Traj W r s
  else 0

/-- Terminal-zero totalization of the raw-DQ reaction history. -/
def capWeightedCoMovingReactionRawDQBUCHistoryIio
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (r s : ℝ) : WholeLineBUC :=
  if s < r then
    capWeightedCoMovingReactionRawDQBUCHistory
      p hM hT eta R c h heta Traj W r s
  else 0

theorem capWeightedCoMovingFluxRawDQBUCHistory_apply_of_lt
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hsr : s < r) (x : ℝ) :
    (capWeightedCoMovingFluxRawDQBUCHistory
        p hM hT eta R c h heta Traj W r s).1 x =
      capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c (r - s)
          (rawSpatialDifferenceQuotient eta h (fun y =>
            wholeLineCauchyCoMovingFluxSource p c hM hT Traj s y -
              wholeLineCauchyCoMovingFluxSource p c hM hT
                (wholeLineBUCTranslateTrajectory hT c W) s y)) x := by
  have hlag : 0 < r - s := sub_pos.mpr hsr
  let Fc : WholeLineBUC :=
    wholeLineCauchyCoMovingFluxSourceBUC p c hM hT Traj s
  let Fw : WholeLineBUC :=
    wholeLineCauchyCoMovingFluxSourceBUC p c hM hT
      (wholeLineBUCTranslateTrajectory hT c W) s
  let D : WholeLineBUC := wholeLineBUCPointwiseSub Fc Fw
  have hinner :
      (wholeLineBUCTranslate (c * r)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyGradientBUCIntegrand p hM hT Traj r s)
          (wholeLineCauchyGradientBUCIntegrand p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) r s))).1 =
        fun y => paper5MovingFrameHeatGradOp c (r - s) D.1 y := by
    funext y
    have hcan :
        (wholeLineCauchyGradientBUCIntegrand p hM hT Traj r s).1
            (y + c * r) =
          paper5MovingFrameHeatGradOp c (r - s) Fc.1 y := by
      simp only [wholeLineCauchyGradientBUCIntegrand,
        wholeLineCauchyHeatGradientBUCTotal, dif_pos hlag,
        wholeLineCauchyHeatGradientBUC_apply]
      unfold paper5MovingFrameHeatGradOp Fc
      rw [show y + c * r = (y + c * (r - s)) + c * s by ring]
      exact wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift
        (r - s) (c * s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT Traj s).1
          (y + c * (r - s))
    have hwave :
        (wholeLineCauchyGradientBUCIntegrand p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) r s).1
            (y + c * r) =
          paper5MovingFrameHeatGradOp c (r - s) Fw.1 y := by
      simp only [wholeLineCauchyGradientBUCIntegrand,
        wholeLineCauchyHeatGradientBUCTotal, dif_pos hlag,
        wholeLineCauchyHeatGradientBUC_apply]
      unfold paper5MovingFrameHeatGradOp Fw
      rw [show y + c * r = (y + c * (r - s)) + c * s by ring]
      exact wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift
        (r - s) (c * s)
          (wholeLineCauchyFluxSourceTrajectory p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) s).1
          (y + c * (r - s))
    rw [wholeLineBUCTranslate_apply, wholeLineBUCPointwiseSub_apply,
      hcan, hwave]
    simpa only [D, wholeLineBUCPointwiseSub_apply,
      paper5MovingFrameHeatGradOp] using
      (wholeLineCauchyHeatGradOp_sub_buc hlag Fc Fw
        (y + c * (r - s))).symm
  have hcomm := rawSpatialDifferenceQuotient_movingFrameHeatGradOp
    hlag c h eta D x
  simp only [capWeightedCoMovingFluxRawDQBUCHistory,
    capWeightSqrtMulBUC_apply,
    wholeLineBUCRawSpatialDifferenceQuotientCLM_coe]
  rw [hinner]
  rw [hcomm]
  rfl

theorem capWeightedCoMovingReactionRawDQBUCHistory_apply_of_lt
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hsr : s < r) (x : ℝ) :
    (capWeightedCoMovingReactionRawDQBUCHistory
        p hM hT eta R c h heta Traj W r s).1 x =
      capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c (r - s)
          (rawSpatialDifferenceQuotient eta h (fun y =>
            wholeLineCauchyCoMovingReactionSource p c hM hT Traj s y -
              wholeLineCauchyCoMovingReactionSource p c hM hT
                (wholeLineBUCTranslateTrajectory hT c W) s y)) x := by
  have hlag : 0 < r - s := sub_pos.mpr hsr
  let Rc : WholeLineBUC :=
    wholeLineCauchyCoMovingReactionSourceBUC p c hM hT Traj s
  let Rw : WholeLineBUC :=
    wholeLineCauchyCoMovingReactionSourceBUC p c hM hT
      (wholeLineBUCTranslateTrajectory hT c W) s
  let D : WholeLineBUC := wholeLineBUCPointwiseSub Rc Rw
  have hinner :
      (wholeLineBUCTranslate (c * r)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyValueBUCIntegrand p hM hT Traj r s)
          (wholeLineCauchyValueBUCIntegrand p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) r s))).1 =
        fun y => paper5MovingFrameHeatOp c (r - s) D.1 y := by
    funext y
    have hcan :
        (wholeLineCauchyValueBUCIntegrand p hM hT Traj r s).1
            (y + c * r) =
          paper5MovingFrameHeatOp c (r - s) Rc.1 y := by
      simp only [wholeLineCauchyValueBUCIntegrand,
        wholeLineCauchyHeatBUCTotal, dif_pos hlag,
        wholeLineCauchyHeatBUC_apply]
      unfold paper5MovingFrameHeatOp Rc
      rw [show y + c * r = (y + c * (r - s)) + c * s by ring]
      exact wholeLineCauchyHeatOp_eval_shift_eq_input_shift
        (r - s) (c * s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT Traj s).1
          (y + c * (r - s))
    have hwave :
        (wholeLineCauchyValueBUCIntegrand p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) r s).1
            (y + c * r) =
          paper5MovingFrameHeatOp c (r - s) Rw.1 y := by
      simp only [wholeLineCauchyValueBUCIntegrand,
        wholeLineCauchyHeatBUCTotal, dif_pos hlag,
        wholeLineCauchyHeatBUC_apply]
      unfold paper5MovingFrameHeatOp Rw
      rw [show y + c * r = (y + c * (r - s)) + c * s by ring]
      exact wholeLineCauchyHeatOp_eval_shift_eq_input_shift
        (r - s) (c * s)
          (wholeLineCauchyReactionSourceTrajectory p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) s).1
          (y + c * (r - s))
    rw [wholeLineBUCTranslate_apply, wholeLineBUCPointwiseSub_apply,
      hcan, hwave]
    simpa only [D, wholeLineBUCPointwiseSub_apply,
      paper5MovingFrameHeatOp] using
      (wholeLineCauchyHeatOp_sub_buc hlag Rc Rw
        (y + c * (r - s))).symm
  have hcomm := rawSpatialDifferenceQuotient_movingFrameHeatOp
    hlag c h eta D x
  simp only [capWeightedCoMovingReactionRawDQBUCHistory,
    capWeightSqrtMulBUC_apply,
    wholeLineBUCRawSpatialDifferenceQuotientCLM_coe]
  rw [hinner]
  rw [hcomm]
  rfl

theorem wholeLineBUCTranslateTrajectory_coMovingFluxSource_eq
    (p : CMParams) {M T c s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    wholeLineCauchyCoMovingFluxSource p c hM hT
        (wholeLineBUCTranslateTrajectory hT c W) s =
      wholeLineChemotaxisFlux p W.1 := by
  let Wave : WholeLineBUCTrajectory T :=
    wholeLineBUCTranslateTrajectory hT c W
  have hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Wave z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro z x
    simpa only [Wave, wholeLineBUCTranslateTrajectory_apply] using
      hWmem (x - c * z.1)
  have hsource :=
    wholeLineCauchyCoMovingFluxSource_eq_genuineFlux_of_strip
      p c hM hT Wave hstrip s
  have hpath : (fun x =>
      (wholeLineBUCTrajectoryExtend hT Wave s).1 (x + c * s)) = W.1 := by
    funext x
    rw [wholeLineBUCTrajectoryExtend_eq hT Wave hs]
    simp only [Wave, wholeLineBUCTranslateTrajectory_apply]
    congr 1
    ring
  rw [hpath] at hsource
  exact hsource

theorem wholeLineBUCTranslateTrajectory_coMovingReactionSource_eq
    (p : CMParams) {M T c s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    wholeLineCauchyCoMovingReactionSource p c hM hT
        (wholeLineBUCTranslateTrajectory hT c W) s =
      wholeLineCauchyShiftedReaction p W.1 := by
  let Wave : WholeLineBUCTrajectory T :=
    wholeLineBUCTranslateTrajectory hT c W
  have hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Wave z).1 x ∈ Set.Icc (0 : ℝ) M := by
    intro z x
    simpa only [Wave, wholeLineBUCTranslateTrajectory_apply] using
      hWmem (x - c * z.1)
  have hsource :=
    wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
      p c hM hT Wave hstrip s
  have hpath : (fun x =>
      (wholeLineBUCTrajectoryExtend hT Wave s).1 (x + c * s)) = W.1 := by
    funext x
    rw [wholeLineBUCTrajectoryExtend_eq hT Wave hs]
    simp only [Wave, wholeLineBUCTranslateTrajectory_apply]
    congr 1
    ring
  rw [hpath] at hsource
  exact hsource

theorem capWeightedCoMovingFluxRawDQBUCHistory_apply_physical_of_lt
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hsT : s ∈ Set.Icc (0 : ℝ) T) (hsr : s < r) (x : ℝ) :
    (capWeightedCoMovingFluxRawDQBUCHistory
        p hM hT eta R c h heta Traj W r s).1 x =
      capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c (r - s)
          (rawSpatialDifferenceQuotient eta h (fun y =>
            wholeLineChemotaxisFlux p (fun z =>
              (wholeLineBUCTrajectoryExtend hT Traj s).1
                (z + c * s)) y -
              wholeLineChemotaxisFlux p W.1 y)) x := by
  rw [capWeightedCoMovingFluxRawDQBUCHistory_apply_of_lt
    p hM hT heta Traj W hsr x]
  rw [wholeLineCauchyCoMovingFluxSource_eq_genuineFlux_of_strip
    p c hM hT Traj hstrip s]
  rw [wholeLineBUCTranslateTrajectory_coMovingFluxSource_eq
    p hM hT W hWmem hsT]

theorem capWeightedCoMovingReactionRawDQBUCHistory_apply_physical_of_lt
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hsT : s ∈ Set.Icc (0 : ℝ) T) (hsr : s < r) (x : ℝ) :
    (capWeightedCoMovingReactionRawDQBUCHistory
        p hM hT eta R c h heta Traj W r s).1 x =
      capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c (r - s)
          (rawSpatialDifferenceQuotient eta h (fun y =>
            wholeLineCauchyShiftedReaction p (fun z =>
              (wholeLineBUCTrajectoryExtend hT Traj s).1
                (z + c * s)) y -
              wholeLineCauchyShiftedReaction p W.1 y)) x := by
  rw [capWeightedCoMovingReactionRawDQBUCHistory_apply_of_lt
    p hM hT heta Traj W hsr x]
  rw [wholeLineCauchyCoMovingReactionSource_eq_genuineReaction_of_strip
    p c hM hT Traj hstrip s]
  rw [wholeLineBUCTranslateTrajectory_coMovingReactionSource_eq
    p hM hT W hWmem hsT]

theorem capWeightedCoMovingFluxRawDQBUCHistory_apply_fixedWave_of_lt
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hsT : s ∈ Set.Icc (0 : ℝ) T) (hsr : s < r) (x : ℝ) :
    (capWeightedCoMovingFluxRawDQBUCHistory
        p hM hT eta R c h heta Traj W r s).1 x =
      capWeightSqrt eta R x *
        paper5MovingFrameHeatGradOp c (r - s)
          (rawSpatialDifferenceQuotient eta h (fun y =>
            wholeLineCauchyCoMovingFluxSource p c hM hT Traj s y -
              wholeLineChemotaxisFlux p W.1 y)) x := by
  rw [capWeightedCoMovingFluxRawDQBUCHistory_apply_of_lt
    p hM hT heta Traj W hsr x]
  rw [wholeLineBUCTranslateTrajectory_coMovingFluxSource_eq
    p hM hT W hWmem hsT]

theorem capWeightedCoMovingReactionRawDQBUCHistory_apply_fixedWave_of_lt
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hsT : s ∈ Set.Icc (0 : ℝ) T) (hsr : s < r) (x : ℝ) :
    (capWeightedCoMovingReactionRawDQBUCHistory
        p hM hT eta R c h heta Traj W r s).1 x =
      capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c (r - s)
          (rawSpatialDifferenceQuotient eta h (fun y =>
            wholeLineCauchyCoMovingReactionSource p c hM hT Traj s y -
              wholeLineCauchyShiftedReaction p W.1 y)) x := by
  rw [capWeightedCoMovingReactionRawDQBUCHistory_apply_of_lt
    p hM hT heta Traj W hsr x]
  rw [wholeLineBUCTranslateTrajectory_coMovingReactionSource_eq
    p hM hT W hWmem hsT]

/-- Clamp the history time below by zero.  On the physical integration
window `[0,r)` this is definitionally the original history; before time zero
it is frozen at the integrable initial slice. -/
def capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (r s : ℝ) : WholeLineBUC :=
  if s < r then
    capWeightedCoMovingFluxRawDQBUCHistory
      p hM hT eta R c h heta Traj W r (max 0 s)
  else 0

def capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (r s : ℝ) : WholeLineBUC :=
  if s < r then
    capWeightedCoMovingReactionRawDQBUCHistory
      p hM hT eta R c h heta Traj W r (max 0 s)
  else 0

theorem capWeightedCoMovingFluxRawDQBUCHistory_continuousOn_Iio
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    ContinuousOn
      (capWeightedCoMovingFluxRawDQBUCHistory
        p hM hT eta R c h heta Traj W r) (Set.Iio r) := by
  have hsub : ContinuousOn
      (fun s => wholeLineBUCPointwiseSub
        (wholeLineCauchyGradientBUCIntegrand p hM hT Traj r s)
        (wholeLineCauchyGradientBUCIntegrand p hM hT
          (wholeLineBUCTranslateTrajectory hT c W) r s))
      (Set.Iio r) :=
    wholeLineBUCPointwiseSub_continuousOn
      (wholeLineCauchyGradientBUCIntegrand_continuousOn_Iio
        p hM hT Traj)
      (wholeLineCauchyGradientBUCIntegrand_continuousOn_Iio
        p hM hT (wholeLineBUCTranslateTrajectory hT c W))
  have htrans : ContinuousOn
      (fun s => wholeLineBUCTranslate (c * r)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyGradientBUCIntegrand p hM hT Traj r s)
          (wholeLineCauchyGradientBUCIntegrand p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) r s)))
      (Set.Iio r) := by
    simpa only [Function.comp_def] using
      (wholeLineBUCTranslate_lipschitz' (c * r)).continuous.comp_continuousOn
        hsub
  have hraw : ContinuousOn
      (fun s => wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
        (wholeLineBUCTranslate (c * r)
          (wholeLineBUCPointwiseSub
            (wholeLineCauchyGradientBUCIntegrand p hM hT Traj r s)
            (wholeLineCauchyGradientBUCIntegrand p hM hT
              (wholeLineBUCTranslateTrajectory hT c W) r s))))
      (Set.Iio r) :=
    (wholeLineBUCRawSpatialDifferenceQuotientCLM eta h).continuous.comp_continuousOn
      htrans
  simpa only [capWeightedCoMovingFluxRawDQBUCHistory, Function.comp_def] using
    (capWeightSqrtMulBUC_lipschitz eta R heta).continuous.comp_continuousOn hraw

theorem capWeightedCoMovingReactionRawDQBUCHistory_continuousOn_Iio
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    ContinuousOn
      (capWeightedCoMovingReactionRawDQBUCHistory
        p hM hT eta R c h heta Traj W r) (Set.Iio r) := by
  have hsub : ContinuousOn
      (fun s => wholeLineBUCPointwiseSub
        (wholeLineCauchyValueBUCIntegrand p hM hT Traj r s)
        (wholeLineCauchyValueBUCIntegrand p hM hT
          (wholeLineBUCTranslateTrajectory hT c W) r s))
      (Set.Iio r) :=
    wholeLineBUCPointwiseSub_continuousOn
      (wholeLineCauchyValueBUCIntegrand_continuousOn_Iio
        p hM hT Traj)
      (wholeLineCauchyValueBUCIntegrand_continuousOn_Iio
        p hM hT (wholeLineBUCTranslateTrajectory hT c W))
  have htrans : ContinuousOn
      (fun s => wholeLineBUCTranslate (c * r)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyValueBUCIntegrand p hM hT Traj r s)
          (wholeLineCauchyValueBUCIntegrand p hM hT
            (wholeLineBUCTranslateTrajectory hT c W) r s)))
      (Set.Iio r) := by
    simpa only [Function.comp_def] using
      (wholeLineBUCTranslate_lipschitz' (c * r)).continuous.comp_continuousOn
        hsub
  have hraw : ContinuousOn
      (fun s => wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
        (wholeLineBUCTranslate (c * r)
          (wholeLineBUCPointwiseSub
            (wholeLineCauchyValueBUCIntegrand p hM hT Traj r s)
            (wholeLineCauchyValueBUCIntegrand p hM hT
              (wholeLineBUCTranslateTrajectory hT c W) r s))))
      (Set.Iio r) :=
    (wholeLineBUCRawSpatialDifferenceQuotientCLM eta h).continuous.comp_continuousOn
      htrans
  simpa only [capWeightedCoMovingReactionRawDQBUCHistory, Function.comp_def] using
    (capWeightSqrtMulBUC_lipschitz eta R heta).continuous.comp_continuousOn hraw

theorem capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_continuousOn_Iio
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    ContinuousOn
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r) (Set.Iio r) := by
  have hmax : ContinuousOn (fun s : ℝ => max 0 s) (Set.Iio r) :=
    (continuous_const.max continuous_id).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => max 0 s) (Set.Iio r) (Set.Iio r) := by
    intro s hs
    exact max_lt hr hs
  have hcomp := (capWeightedCoMovingFluxRawDQBUCHistory_continuousOn_Iio
    p hM hT (R := R) (c := c) (h := h) heta Traj W).comp hmax hmaps
  refine hcomp.congr ?_
  intro s hs
  have hsr : s < r := hs
  rw [capWeightedCoMovingFluxRawDQBUCHistoryClampedIio, if_pos hsr]
  rfl

theorem capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_continuousOn_Iio
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    ContinuousOn
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r) (Set.Iio r) := by
  have hmax : ContinuousOn (fun s : ℝ => max 0 s) (Set.Iio r) :=
    (continuous_const.max continuous_id).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => max 0 s) (Set.Iio r) (Set.Iio r) := by
    intro s hs
    exact max_lt hr hs
  have hcomp := (capWeightedCoMovingReactionRawDQBUCHistory_continuousOn_Iio
    p hM hT (R := R) (c := c) (h := h) heta Traj W).comp hmax hmaps
  refine hcomp.congr ?_
  intro s hs
  have hsr : s < r := hs
  rw [capWeightedCoMovingReactionRawDQBUCHistoryClampedIio, if_pos hsr]
  rfl

theorem capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_aestronglyMeasurable
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    AEStronglyMeasurable
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r) volume := by
  let F := capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
    p hM hT eta R c h heta Traj W r
  have hFIio : AEStronglyMeasurable F (volume.restrict (Set.Iio r)) :=
    (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_continuousOn_Iio
      p hM hT heta hr Traj W).aestronglyMeasurable measurableSet_Iio
  have hind : AEStronglyMeasurable ((Set.Iio r).indicator F) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hFIio
  exact hind.congr (Eventually.of_forall fun s => by
    simp only [Set.indicator_apply, Set.mem_Iio]
    by_cases hsr : s < r
    · simp [F, capWeightedCoMovingFluxRawDQBUCHistoryClampedIio, hsr]
    · simp [F, capWeightedCoMovingFluxRawDQBUCHistoryClampedIio, hsr])

theorem capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_aestronglyMeasurable
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    AEStronglyMeasurable
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r) volume := by
  let F := capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
    p hM hT eta R c h heta Traj W r
  have hFIio : AEStronglyMeasurable F (volume.restrict (Set.Iio r)) :=
    (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_continuousOn_Iio
      p hM hT heta hr Traj W).aestronglyMeasurable measurableSet_Iio
  have hind : AEStronglyMeasurable ((Set.Iio r).indicator F) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hFIio
  exact hind.congr (Eventually.of_forall fun s => by
    simp only [Set.indicator_apply, Set.mem_Iio]
    by_cases hsr : s < r
    · simp [F, capWeightedCoMovingReactionRawDQBUCHistoryClampedIio, hsr]
    · simp [F, capWeightedCoMovingReactionRawDQBUCHistoryClampedIio, hsr])

theorem capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_sq_integrable
    (p : CMParams) {M T Brel DU eta R h c r X F : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    (hr : 0 < r) (hrT : r ≤ T) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hWpos : ∀ x, 0 < W.1 x)
    (hbase : ∀ x, |(W.1 (x + h) - W.1 x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      |(W.1 (x + h) - W.1 x) / h| ≤
        Brel * (theta * W.1 (x + h) + (1 - theta) * W.1 x))
    (hvalue : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x =>
      capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2))
    (hraw : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x =>
      capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2))
    (hraw_energy : ∀ s ∈ Set.Icc (0 : ℝ) r,
      (∫ x : ℝ, capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2) ≤ X ^ 2)
    (hvalue_energy : ∀ s ∈ Set.Icc (0 : ℝ) r,
      (∫ x : ℝ, capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2) ≤ F ^ 2) :
    ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta0 Traj W r s).1 x ^ 2) volume := by
  intro s
  by_cases hsr : s < r
  · let q : ℝ := max 0 s
    have hq0 : 0 ≤ q := le_max_left 0 s
    have hqr : q < r := by
      dsimp only [q]
      exact max_lt hr hsr
    have hqIcc : q ∈ Set.Icc (0 : ℝ) r := ⟨hq0, hqr.le⟩
    have hqT : q ∈ Set.Icc (0 : ℝ) T :=
      ⟨hq0, hqr.le.trans hrT⟩
    have hlag : 0 < r - q := sub_pos.mpr hqr
    have hlagT : r - q ≤ T := by linarith
    rcases
        exists_capWeightedMovingHeatGradient_coMovingFluxRawDQL2_le_kernel
          p hM hT hBrel hDU heta0 heta1 hh hlag hlagT hX hF Traj
          hstrip (WholeLineBUC.isCUnifBdd W) hWmem hWpos hbase hrelative
          (hvalue q hqIcc) (hraw q hqIcc)
          (hraw_energy q hqIcc) (hvalue_energy q hqIcc)
          (s := q) (R := R) (c := c) (tau := r - q) (L := T) with
      ⟨Z, hZrep, _hZnorm⟩
    have hZsq : Integrable (fun x : ℝ => Z x ^ 2) volume :=
      (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
    refine hZsq.congr ?_
    filter_upwards [hZrep] with x hx
    rw [hx]
    rw [capWeightedCoMovingFluxRawDQBUCHistoryClampedIio, if_pos hsr]
    exact congrArg (fun z : ℝ => z ^ 2)
      (capWeightedCoMovingFluxRawDQBUCHistory_apply_fixedWave_of_lt
        p hM hT heta0 Traj W hWmem hqT hqr x).symm
  · simp [capWeightedCoMovingFluxRawDQBUCHistoryClampedIio, hsr]

theorem capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_sq_integrable
    (p : CMParams) {M T DU eta R h c r X F : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (hh : h ≠ 0)
    (hr : 0 < r) (hrT : r ≤ T) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hWquot : ∀ x, |spatialDifferenceQuotient h W.1 x| ≤ DU)
    (hvalue : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x =>
      capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2))
    (hraw : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x =>
      capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2))
    (hraw_energy : ∀ s ∈ Set.Icc (0 : ℝ) r,
      (∫ x : ℝ, capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2) ≤ X ^ 2)
    (hvalue_energy : ∀ s ∈ Set.Icc (0 : ℝ) r,
      (∫ x : ℝ, capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2) ≤ F ^ 2) :
    ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta0 Traj W r s).1 x ^ 2) volume := by
  intro s
  by_cases hsr : s < r
  · let q : ℝ := max 0 s
    have hq0 : 0 ≤ q := le_max_left 0 s
    have hqr : q < r := by
      dsimp only [q]
      exact max_lt hr hsr
    have hqIcc : q ∈ Set.Icc (0 : ℝ) r := ⟨hq0, hqr.le⟩
    have hqT : q ∈ Set.Icc (0 : ℝ) T :=
      ⟨hq0, hqr.le.trans hrT⟩
    have hlag : 0 < r - q := sub_pos.mpr hqr
    have hlagT : r - q ≤ T := by linarith
    rcases exists_capWeightedMovingHeat_coMovingReactionRawDQL2_le_kernel
        p hM hT heta0 hDU hh hlag hlagT hX hF Traj hstrip
          (WholeLineBUC.isCUnifBdd W) hWmem hWquot
          (hvalue q hqIcc) (hraw q hqIcc)
          (hraw_energy q hqIcc) (hvalue_energy q hqIcc)
          (s := q) (R := R) (c := c) (tau := r - q) (L := T) with
      ⟨Z, hZrep, _hZnorm⟩
    have hZsq : Integrable (fun x : ℝ => Z x ^ 2) volume :=
      (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
    refine hZsq.congr ?_
    filter_upwards [hZrep] with x hx
    rw [hx]
    rw [capWeightedCoMovingReactionRawDQBUCHistoryClampedIio, if_pos hsr]
    exact congrArg (fun z : ℝ => z ^ 2)
      (capWeightedCoMovingReactionRawDQBUCHistory_apply_fixedWave_of_lt
        p hM hT heta0 Traj W hWmem hqT hqr x).symm
  · simp [capWeightedCoMovingReactionRawDQBUCHistoryClampedIio, hsr]

/-- Canonical `L²(ℝ)` realization of the clamped flux raw-DQ history. -/
def capWeightedCoMovingFluxRawDQL2History
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) (r : ℝ)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume)
    (s : ℝ) : WholeLineRealL2 :=
  if s < r then
    wholeLineRealL2Section
      (fun q x =>
        (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
          p hM hT eta R c h heta Traj W r q).1 x)
      (fun q =>
        (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
          p hM hT eta R c h heta Traj W r q).1.continuous.aestronglyMeasurable)
      hF2 s
  else 0

/-- Canonical `L²(ℝ)` realization of the clamped reaction raw-DQ history. -/
def capWeightedCoMovingReactionRawDQL2History
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) (r : ℝ)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume)
    (s : ℝ) : WholeLineRealL2 :=
  if s < r then
    wholeLineRealL2Section
      (fun q x =>
        (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
          p hM hT eta R c h heta Traj W r q).1 x)
      (fun q =>
        (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
          p hM hT eta R c h heta Traj W r q).1.continuous.aestronglyMeasurable)
      hF2 s
  else 0

theorem capWeightedCoMovingFluxRawDQL2History_aestronglyMeasurable
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume) :
    AEStronglyMeasurable
      (capWeightedCoMovingFluxRawDQL2History
        p hM hT eta R c h heta Traj W r hF2) volume := by
  simpa only [capWeightedCoMovingFluxRawDQL2History] using
    wholeLineRealL2Section_Iio_totalized_aestronglyMeasurable
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_continuousOn_Iio
        p hM hT heta hr Traj W) hF2

theorem capWeightedCoMovingReactionRawDQL2History_aestronglyMeasurable
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume) :
    AEStronglyMeasurable
      (capWeightedCoMovingReactionRawDQL2History
        p hM hT eta R c h heta Traj W r hF2) volume := by
  simpa only [capWeightedCoMovingReactionRawDQL2History] using
    wholeLineRealL2Section_Iio_totalized_aestronglyMeasurable
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_continuousOn_Iio
        p hM hT heta hr Traj W) hF2

theorem capWeightedCoMovingFluxRawDQL2History_coe_ae_of_lt
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hF2 : ∀ q, Integrable (fun x : ℝ =>
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r q).1 x ^ 2) volume)
    (hsr : s < r) :
    (((capWeightedCoMovingFluxRawDQL2History
        p hM hT eta R c h heta Traj W r hF2 s : WholeLineRealL2) :
          ℝ → ℝ) =ᵐ[volume]
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1) := by
  rw [capWeightedCoMovingFluxRawDQL2History, if_pos hsr]
  exact wholeLineRealL2Section_coe_ae _ _ _ s

theorem capWeightedCoMovingReactionRawDQL2History_coe_ae_of_lt
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hF2 : ∀ q, Integrable (fun x : ℝ =>
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r q).1 x ^ 2) volume)
    (hsr : s < r) :
    (((capWeightedCoMovingReactionRawDQL2History
        p hM hT eta R c h heta Traj W r hF2 s : WholeLineRealL2) :
          ℝ → ℝ) =ᵐ[volume]
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1) := by
  rw [capWeightedCoMovingReactionRawDQL2History, if_pos hsr]
  exact wholeLineRealL2Section_coe_ae _ _ _ s

theorem capWeightedCoMovingFluxRawDQL2History_norm_le
    (p : CMParams) {M T Brel DU eta R h c r s X F : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hBrel : 0 ≤ Brel) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hh : h ≠ 0)
    (hrT : r ≤ T) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hWpos : ∀ x, 0 < W.1 x)
    (hbase : ∀ x, |(W.1 (x + h) - W.1 x) / h| ≤ DU)
    (hrelative : ∀ x, ∀ theta ∈ Set.Icc (0 : ℝ) 1,
      |(W.1 (x + h) - W.1 x) / h| ≤
        Brel * (theta * W.1 (x + h) + (1 - theta) * W.1 x))
    (hvalue : Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
        W.1 x| ^ 2))
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x) +
        spatialDifferenceQuotient h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
            W.1 y) x| ^ 2))
    (hraw_energy :
      (∫ x : ℝ, capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2) ≤ X ^ 2)
    (hvalue_energy :
      (∫ x : ℝ, capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2) ≤ F ^ 2)
    (hF2 : ∀ q, Integrable (fun x : ℝ =>
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta0 Traj W r q).1 x ^ 2) volume)
    (hs : s ∈ Set.Ico (0 : ℝ) r) :
    ‖capWeightedCoMovingFluxRawDQL2History
        p hM hT eta R c h heta0 Traj W r hF2 s‖ ≤
      (2 * capMildGrowthBound eta c T * eta +
        (2 * capMildGrowthBound eta c T *
          (2 / Real.sqrt (4 * Real.pi))) *
            (r - s) ^ (-(1 / 2 : ℝ))) *
        (Real.sqrt (matchedFluxRawQSquareConstant p M eta) * X +
          Real.sqrt
            (matchedFluxRawWSquareConstant p M Brel DU eta h) * F) := by
  have hsT : s ∈ Set.Icc (0 : ℝ) T :=
    ⟨hs.1, hs.2.le.trans hrT⟩
  have hlag : 0 < r - s := sub_pos.mpr hs.2
  have hlagT : r - s ≤ T := by linarith [hs.1]
  rcases
      exists_capWeightedMovingHeatGradient_coMovingFluxRawDQL2_le_kernel
        p hM hT hBrel hDU heta0 heta1 hh hlag hlagT hX hF Traj
        hstrip (WholeLineBUC.isCUnifBdd W) hWmem hWpos hbase hrelative
        hvalue hraw hraw_energy hvalue_energy
        (R := R) (c := c) (tau := r - s) (L := T) with
    ⟨Z, hZrep, hZnorm⟩
  have hcoe := capWeightedCoMovingFluxRawDQL2History_coe_ae_of_lt
    p hM hT heta0 Traj W hF2 hs.2
  have hhist : ∀ x,
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta0 Traj W r s).1 x =
        capWeightSqrt eta R x *
          paper5MovingFrameHeatGradOp c (r - s)
            (rawSpatialDifferenceQuotient eta h (fun y =>
              wholeLineCauchyCoMovingFluxSource p c hM hT Traj s y -
                wholeLineChemotaxisFlux p W.1 y)) x := by
    intro x
    rw [capWeightedCoMovingFluxRawDQBUCHistoryClampedIio, if_pos hs.2]
    rw [max_eq_right hs.1]
    exact capWeightedCoMovingFluxRawDQBUCHistory_apply_fixedWave_of_lt
      p hM hT heta0 Traj W hWmem hsT hs.2 x
  have hEq : capWeightedCoMovingFluxRawDQL2History
      p hM hT eta R c h heta0 Traj W r hF2 s = Z := by
    apply Lp.ext
    filter_upwards [hcoe, hZrep] with x hx hzx
    rw [hx, hzx, hhist x]
    rfl
  rw [hEq]
  exact hZnorm

theorem capWeightedCoMovingReactionRawDQL2History_norm_le
    (p : CMParams) {M T DU eta R h c r s X F : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hDU : 0 ≤ DU)
    (heta0 : 0 ≤ eta) (hh : h ≠ 0)
    (hrT : r ≤ T) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (Traj : WholeLineBUCTrajectory T)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (Traj z).1 x ∈ Set.Icc (0 : ℝ) M)
    (W : WholeLineBUC)
    (hWmem : ∀ x, W.1 x ∈ Set.Icc (0 : ℝ) M)
    (hWquot : ∀ x, |spatialDifferenceQuotient h W.1 x| ≤ DU)
    (hvalue : Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
        W.1 x| ^ 2))
    (hraw : Integrable (fun x => capWeight eta R x *
      |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x) +
        spatialDifferenceQuotient h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
            W.1 y) x| ^ 2))
    (hraw_energy :
      (∫ x : ℝ, capWeight eta R x *
        |eta * ((wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
            W.1 x) +
          spatialDifferenceQuotient h (fun y =>
            (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) -
              W.1 y) x| ^ 2) ≤ X ^ 2)
    (hvalue_energy :
      (∫ x : ℝ, capWeight eta R x *
        |(wholeLineBUCTrajectoryExtend hT Traj s).1 (x + c * s) -
          W.1 x| ^ 2) ≤ F ^ 2)
    (hF2 : ∀ q, Integrable (fun x : ℝ =>
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta0 Traj W r q).1 x ^ 2) volume)
    (hs : s ∈ Set.Ico (0 : ℝ) r) :
    ‖capWeightedCoMovingReactionRawDQL2History
        p hM hT eta R c h heta0 Traj W r hF2 s‖ ≤
      2 * capMildGrowthBound eta c T *
        (Real.sqrt (matchedShiftedReactionRawQSquareConstant p M) * X +
          Real.sqrt
            (matchedShiftedReactionRawWSquareConstant p M eta DU) * F) := by
  have hsT : s ∈ Set.Icc (0 : ℝ) T :=
    ⟨hs.1, hs.2.le.trans hrT⟩
  have hlag : 0 < r - s := sub_pos.mpr hs.2
  have hlagT : r - s ≤ T := by linarith [hs.1]
  rcases exists_capWeightedMovingHeat_coMovingReactionRawDQL2_le_kernel
      p hM hT heta0 hDU hh hlag hlagT hX hF Traj hstrip
        (WholeLineBUC.isCUnifBdd W) hWmem hWquot
        hvalue hraw hraw_energy hvalue_energy
        (R := R) (c := c) (tau := r - s) (L := T) with
    ⟨Z, hZrep, hZnorm⟩
  have hcoe := capWeightedCoMovingReactionRawDQL2History_coe_ae_of_lt
    p hM hT heta0 Traj W hF2 hs.2
  have hhist : ∀ x,
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta0 Traj W r s).1 x =
        capWeightSqrt eta R x *
          paper5MovingFrameHeatOp c (r - s)
            (rawSpatialDifferenceQuotient eta h (fun y =>
              wholeLineCauchyCoMovingReactionSource p c hM hT Traj s y -
                wholeLineCauchyShiftedReaction p W.1 y)) x := by
    intro x
    rw [capWeightedCoMovingReactionRawDQBUCHistoryClampedIio, if_pos hs.2]
    rw [max_eq_right hs.1]
    exact capWeightedCoMovingReactionRawDQBUCHistory_apply_fixedWave_of_lt
      p hM hT heta0 Traj W hWmem hsT hs.2 x
  have hEq : capWeightedCoMovingReactionRawDQL2History
      p hM hT eta R c h heta0 Traj W r hF2 s = Z := by
    apply Lp.ext
    filter_upwards [hcoe, hZrep] with x hx hzx
    rw [hx, hzx, hhist x]
    rfl
  rw [hEq]
  exact hZnorm

theorem capWeightedCoMovingFluxRawDQL2History_intervalIntegrable_of_majorant
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume)
    {q : ℝ → ℝ} (hq_int : IntervalIntegrable q volume 0 r)
    (hq_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) r, 0 ≤ q s)
    (hmajor : ∀ s ∈ Set.Icc (0 : ℝ) r, s < r →
      ‖capWeightedCoMovingFluxRawDQL2History
        p hM hT eta R c h heta Traj W r hF2 s‖ ≤ q s) :
    IntervalIntegrable
      (capWeightedCoMovingFluxRawDQL2History
        p hM hT eta R c h heta Traj W r hF2) volume 0 r := by
  have hmajor' : ∀ s ∈ Set.Icc (0 : ℝ) r, s < r →
      ‖wholeLineRealL2Section
        (fun q x =>
          (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
            p hM hT eta R c h heta Traj W r q).1 x)
        (fun q =>
          (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
            p hM hT eta R c h heta Traj W r q).1.continuous.aestronglyMeasurable)
        hF2 s‖ ≤ q s := by
    intro s hs hsr
    simpa only [capWeightedCoMovingFluxRawDQL2History, if_pos hsr] using
      hmajor s hs hsr
  simpa only [capWeightedCoMovingFluxRawDQL2History] using
    wholeLineRealL2Section_Iio_totalized_intervalIntegrable_of_majorant
      hr.le
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_continuousOn_Iio
        p hM hT heta hr Traj W)
      hF2 hq_int hq_nonneg hmajor'

theorem capWeightedCoMovingReactionRawDQL2History_intervalIntegrable_of_majorant
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume)
    {q : ℝ → ℝ} (hq_int : IntervalIntegrable q volume 0 r)
    (hq_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) r, 0 ≤ q s)
    (hmajor : ∀ s ∈ Set.Icc (0 : ℝ) r, s < r →
      ‖capWeightedCoMovingReactionRawDQL2History
        p hM hT eta R c h heta Traj W r hF2 s‖ ≤ q s) :
    IntervalIntegrable
      (capWeightedCoMovingReactionRawDQL2History
        p hM hT eta R c h heta Traj W r hF2) volume 0 r := by
  have hmajor' : ∀ s ∈ Set.Icc (0 : ℝ) r, s < r →
      ‖wholeLineRealL2Section
        (fun q x =>
          (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
            p hM hT eta R c h heta Traj W r q).1 x)
        (fun q =>
          (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
            p hM hT eta R c h heta Traj W r q).1.continuous.aestronglyMeasurable)
        hF2 s‖ ≤ q s := by
    intro s hs hsr
    simpa only [capWeightedCoMovingReactionRawDQL2History, if_pos hsr] using
      hmajor s hs hsr
  simpa only [capWeightedCoMovingReactionRawDQL2History] using
    wholeLineRealL2Section_Iio_totalized_intervalIntegrable_of_majorant
      hr.le
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_continuousOn_Iio
        p hM hT heta hr Traj W)
      hF2 hq_int hq_nonneg hmajor'

theorem wholeLineBUCRawSpatialDifferenceQuotientCLM_norm_le
    (eta h : ℝ) (u : WholeLineBUC) :
    ‖wholeLineBUCRawSpatialDifferenceQuotientCLM eta h u‖ ≤
      (|eta| + 2 * |h⁻¹|) * ‖u‖ := by
  change ‖eta • u + h⁻¹ • (wholeLineBUCTranslate h u - u)‖ ≤ _
  calc
    ‖eta • u + h⁻¹ • (wholeLineBUCTranslate h u - u)‖ ≤
        ‖eta • u‖ + ‖h⁻¹ • (wholeLineBUCTranslate h u - u)‖ :=
      by
        simpa only using
          (norm_add_le (eta • u) (h⁻¹ • (wholeLineBUCTranslate h u - u)))
    _ = |eta| * ‖u‖ + |h⁻¹| * ‖wholeLineBUCTranslate h u - u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |eta| * ‖u‖ + |h⁻¹| * (2 * ‖u‖) := by
      gcongr
      calc
        ‖wholeLineBUCTranslate h u - u‖ ≤
            ‖wholeLineBUCTranslate h u‖ + ‖u‖ := by
          simpa only using (norm_sub_le (wholeLineBUCTranslate h u) u)
        _ ≤ ‖u‖ + ‖u‖ :=
          add_le_add (wholeLineBUCTranslate_norm_le h u) le_rfl
        _ = 2 * ‖u‖ := by ring
    _ = (|eta| + 2 * |h⁻¹|) * ‖u‖ := by ring

theorem capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_norm_le
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hs : s ∈ Set.Ioo (0 : ℝ) r) :
    ‖capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s‖ ≤
      (Real.exp (eta * R) *
        (|eta| + 2 * |h⁻¹|) *
          ((2 / Real.sqrt (4 * Real.pi)) *
            (wholeLineCauchyFluxLip p M *
              dist Traj (wholeLineBUCTranslateTrajectory hT c W)))) *
        (r - s) ^ (-(1 / 2 : ℝ)) := by
  have hsr : s < r := hs.2
  let I₂ := wholeLineCauchyGradientBUCIntegrand p hM hT Traj r s
  let I₁ := wholeLineCauchyGradientBUCIntegrand p hM hT
    (wholeLineBUCTranslateTrajectory hT c W) r s
  let D := wholeLineBUCPointwiseSub I₂ I₁
  have hI : ‖I₂ - I₁‖ ≤
      ((2 / Real.sqrt (4 * Real.pi)) *
        (wholeLineCauchyFluxLip p M *
          dist Traj (wholeLineBUCTranslateTrajectory hT c W))) *
        (r - s) ^ (-(1 / 2 : ℝ)) := by
    simpa only [I₂, I₁] using
      wholeLineCauchyGradientBUCIntegrand_sub_norm_le
        p hM hT Traj (wholeLineBUCTranslateTrajectory hT c W) hsr
  rw [capWeightedCoMovingFluxRawDQBUCHistoryClampedIio, if_pos hsr,
    max_eq_right hs.1.le]
  calc
    ‖capWeightedCoMovingFluxRawDQBUCHistory
        p hM hT eta R c h heta Traj W r s‖ ≤
        Real.exp (eta * R) *
          ‖wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
            (wholeLineBUCTranslate (c * r) D)‖ :=
      capWeightSqrtMulBUC_norm_le eta R heta _
    _ ≤ Real.exp (eta * R) *
        ((|eta| + 2 * |h⁻¹|) *
          ‖wholeLineBUCTranslate (c * r) D‖) := by
      gcongr
      exact wholeLineBUCRawSpatialDifferenceQuotientCLM_norm_le eta h _
    _ ≤ Real.exp (eta * R) *
        ((|eta| + 2 * |h⁻¹|) * ‖D‖) := by
      gcongr
      exact wholeLineBUCTranslate_norm_le' (c * r) D
    _ ≤ Real.exp (eta * R) *
        ((|eta| + 2 * |h⁻¹|) * ‖I₂ - I₁‖) := by
      gcongr
      exact (wholeLineBUCPointwiseSub_norm_le_dist I₂ I₁).trans_eq
        (WholeLineBUC.dist_eq_norm_sub I₂ I₁)
    _ ≤ _ := by
      have hexp : 0 ≤ Real.exp (eta * R) := (Real.exp_pos _).le
      have hop : 0 ≤ |eta| + 2 * |h⁻¹| := by positivity
      calc
        Real.exp (eta * R) *
            ((|eta| + 2 * |h⁻¹|) *
              ‖I₂ - I₁‖) ≤
            Real.exp (eta * R) *
              ((|eta| + 2 * |h⁻¹|) *
                (((2 / Real.sqrt (4 * Real.pi)) *
                  (wholeLineCauchyFluxLip p M *
                    dist Traj (wholeLineBUCTranslateTrajectory hT c W))) *
                  (r - s) ^ (-(1 / 2 : ℝ)))) := by
          gcongr
        _ = _ := by ring

theorem capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_norm_le
    (p : CMParams) {M T eta R c h r s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hs : s ∈ Set.Ioo (0 : ℝ) r) :
    ‖capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s‖ ≤
      Real.exp (eta * R) *
        (|eta| + 2 * |h⁻¹|) *
          ((1 + reactionLip p.α M) *
            dist Traj (wholeLineBUCTranslateTrajectory hT c W)) := by
  have hsr : s < r := hs.2
  let I₂ := wholeLineCauchyValueBUCIntegrand p hM hT Traj r s
  let I₁ := wholeLineCauchyValueBUCIntegrand p hM hT
    (wholeLineBUCTranslateTrajectory hT c W) r s
  let D := wholeLineBUCPointwiseSub I₂ I₁
  have hI : ‖I₂ - I₁‖ ≤
      (1 + reactionLip p.α M) *
        dist Traj (wholeLineBUCTranslateTrajectory hT c W) := by
    simpa only [I₂, I₁] using
      wholeLineCauchyValueBUCIntegrand_sub_norm_le
        p hM hT Traj (wholeLineBUCTranslateTrajectory hT c W) hsr.le
  rw [capWeightedCoMovingReactionRawDQBUCHistoryClampedIio, if_pos hsr,
    max_eq_right hs.1.le]
  calc
    ‖capWeightedCoMovingReactionRawDQBUCHistory
        p hM hT eta R c h heta Traj W r s‖ ≤
        Real.exp (eta * R) *
          ‖wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
            (wholeLineBUCTranslate (c * r) D)‖ :=
      capWeightSqrtMulBUC_norm_le eta R heta _
    _ ≤ Real.exp (eta * R) *
        ((|eta| + 2 * |h⁻¹|) *
          ‖wholeLineBUCTranslate (c * r) D‖) := by
      gcongr
      exact wholeLineBUCRawSpatialDifferenceQuotientCLM_norm_le eta h _
    _ ≤ Real.exp (eta * R) *
        ((|eta| + 2 * |h⁻¹|) * ‖D‖) := by
      gcongr
      exact wholeLineBUCTranslate_norm_le' (c * r) D
    _ ≤ Real.exp (eta * R) *
        ((|eta| + 2 * |h⁻¹|) * ‖I₂ - I₁‖) := by
      gcongr
      exact (wholeLineBUCPointwiseSub_norm_le_dist I₂ I₁).trans_eq
        (WholeLineBUC.dist_eq_norm_sub I₂ I₁)
    _ ≤ _ := by
      have hexp : 0 ≤ Real.exp (eta * R) := (Real.exp_pos _).le
      have hop : 0 ≤ |eta| + 2 * |h⁻¹| := by positivity
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hI hop) hexp)

/-- The terminal-zero, lower-clamped flux raw-DQ history is Bochner
integrable in `BUC(ℝ)` on every positive restart window.  Its only
terminal singularity is the integrable heat-gradient factor
`(r-s)⁻¹ᐟ²`. -/
theorem capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_norm_integrable
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    Integrable (fun s =>
      ‖capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s‖)
      (volume.restrict (Set.Ioc (0 : ℝ) r)) := by
  let C : ℝ := Real.exp (eta * R) *
    (|eta| + 2 * |h⁻¹|) *
      ((2 / Real.sqrt (4 * Real.pi)) *
        (wholeLineCauchyFluxLip p M *
          dist Traj (wholeLineBUCTranslateTrajectory hT c W)))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (by positivity))
      (mul_nonneg
        (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (mul_nonneg (wholeLineCauchyFluxLip_nonneg p hM) dist_nonneg))
  have hdomII : IntervalIntegrable
      (fun s : ℝ => C * (r - s) ^ (-(1 / 2 : ℝ))) volume 0 r :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half
      r).const_mul C
  have hdom : Integrable
      (fun s : ℝ => C * (r - s) ^ (-(1 / 2 : ℝ)))
      (volume.restrict (Set.Ioc (0 : ℝ) r)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp hdomII
  refine Integrable.mono' hdom
    ((capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_aestronglyMeasurable
      p hM hT heta hr Traj W).norm.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (Measure.ae_ne volume r)] with s hs hne
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hsr : s < r := lt_of_le_of_ne hs.2 hne
  simpa only [C, mul_assoc] using
    capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_norm_le
      p hM hT heta Traj W ⟨hs.1, hsr⟩

/-- The terminal-zero, lower-clamped reaction raw-DQ history is Bochner
integrable in `BUC(ℝ)` on every positive restart window. -/
theorem capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_norm_integrable
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    Integrable (fun s =>
      ‖capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s‖)
      (volume.restrict (Set.Ioc (0 : ℝ) r)) := by
  let C : ℝ := Real.exp (eta * R) *
    (|eta| + 2 * |h⁻¹|) *
      ((1 + reactionLip p.α M) *
        dist Traj (wholeLineBUCTranslateTrajectory hT c W))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (by positivity))
      (mul_nonneg
        (add_nonneg zero_le_one (reactionLip_nonneg p.hα hM)) dist_nonneg)
  have hdomII : IntervalIntegrable (fun _s : ℝ => C) volume 0 r :=
    intervalIntegrable_const
  have hdom : Integrable (fun _s : ℝ => C)
      (volume.restrict (Set.Ioc (0 : ℝ) r)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mp hdomII
  refine Integrable.mono' hdom
    ((capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_aestronglyMeasurable
      p hM hT heta hr Traj W).norm.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (Measure.ae_ne volume r)] with s hs hne
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hsr : s < r := lt_of_le_of_ne hs.2 hne
  simpa only [C, mul_assoc] using
    capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_norm_le
      p hM hT heta Traj W ⟨hs.1, hsr⟩

theorem capWeightedCoMovingFluxRawDQL2History_integral_rep
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume)
    (hFnorm : Integrable (fun s =>
      ‖capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s‖)
      (volume.restrict (Set.Ioc (0 : ℝ) r)))
    (hZint : IntervalIntegrable
      (capWeightedCoMovingFluxRawDQL2History
        p hM hT eta R c h heta Traj W r hF2) volume 0 r) :
    ((((∫ s in (0 : ℝ)..r,
        capWeightedCoMovingFluxRawDQL2History
          p hM hT eta R c h heta Traj W r hF2 s) : WholeLineRealL2) :
          ℝ → ℝ) =ᵐ[volume] fun x =>
      ∫ s in (0 : ℝ)..r,
        (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
          p hM hT eta R c h heta Traj W r s).1 x) := by
  let Fh := capWeightedCoMovingFluxRawDQBUCHistoryClampedIio
    p hM hT eta R c h heta Traj W r
  let Zbase := wholeLineRealL2Section
    (fun s x => (Fh s).1 x)
    (fun s => (Fh s).1.continuous.aestronglyMeasurable) hF2
  let Ztot := capWeightedCoMovingFluxRawDQL2History
    p hM hT eta R c h heta Traj W r hF2
  have hEq : Ztot =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) r)] Zbase := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume r)] with s hs hne
    rw [Set.uIoc_of_le hr.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hne
    simp only [Ztot, Zbase, capWeightedCoMovingFluxRawDQL2History,
      if_pos hsr, Fh]
  have hZbaseInt : IntervalIntegrable Zbase volume 0 r :=
    hZint.congr_ae hEq
  have hFmeas : AEStronglyMeasurable Fh
      (volume.restrict (Set.Ioc (0 : ℝ) r)) :=
    (capWeightedCoMovingFluxRawDQBUCHistoryClampedIio_aestronglyMeasurable
      p hM hT heta hr Traj W).restrict
  have hrep := wholeLineRealL2_intervalIntegral_coe_ae_of_buc_history
    hr.le hFmeas (by simpa only [Fh] using hFnorm) hF2 hZbaseInt
  have hintEq : (∫ s in (0 : ℝ)..r, Ztot s) =
      ∫ s in (0 : ℝ)..r, Zbase s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume r] with s hne hs
    rw [Set.uIoc_of_le hr.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hne
    simp only [Ztot, Zbase, capWeightedCoMovingFluxRawDQL2History,
      if_pos hsr, Fh]
  simpa only [Ztot, Zbase, Fh, hintEq] using hrep

theorem capWeightedCoMovingReactionRawDQL2History_integral_rep
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hr : 0 < r)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hF2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s).1 x ^ 2) volume)
    (hFnorm : Integrable (fun s =>
      ‖capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
        p hM hT eta R c h heta Traj W r s‖)
      (volume.restrict (Set.Ioc (0 : ℝ) r)))
    (hZint : IntervalIntegrable
      (capWeightedCoMovingReactionRawDQL2History
        p hM hT eta R c h heta Traj W r hF2) volume 0 r) :
    ((((∫ s in (0 : ℝ)..r,
        capWeightedCoMovingReactionRawDQL2History
          p hM hT eta R c h heta Traj W r hF2 s) : WholeLineRealL2) :
          ℝ → ℝ) =ᵐ[volume] fun x =>
      ∫ s in (0 : ℝ)..r,
        (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
          p hM hT eta R c h heta Traj W r s).1 x) := by
  let Fh := capWeightedCoMovingReactionRawDQBUCHistoryClampedIio
    p hM hT eta R c h heta Traj W r
  let Zbase := wholeLineRealL2Section
    (fun s x => (Fh s).1 x)
    (fun s => (Fh s).1.continuous.aestronglyMeasurable) hF2
  let Ztot := capWeightedCoMovingReactionRawDQL2History
    p hM hT eta R c h heta Traj W r hF2
  have hEq : Ztot =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) r)] Zbase := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      ae_restrict_of_ae (Measure.ae_ne volume r)] with s hs hne
    rw [Set.uIoc_of_le hr.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hne
    simp only [Ztot, Zbase, capWeightedCoMovingReactionRawDQL2History,
      if_pos hsr, Fh]
  have hZbaseInt : IntervalIntegrable Zbase volume 0 r :=
    hZint.congr_ae hEq
  have hFmeas : AEStronglyMeasurable Fh
      (volume.restrict (Set.Ioc (0 : ℝ) r)) :=
    (capWeightedCoMovingReactionRawDQBUCHistoryClampedIio_aestronglyMeasurable
      p hM hT heta hr Traj W).restrict
  have hrep := wholeLineRealL2_intervalIntegral_coe_ae_of_buc_history
    hr.le hFmeas (by simpa only [Fh] using hFnorm) hF2 hZbaseInt
  have hintEq : (∫ s in (0 : ℝ)..r, Ztot s) =
      ∫ s in (0 : ℝ)..r, Zbase s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume r] with s hne hs
    rw [Set.uIoc_of_le hr.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hne
    simp only [Ztot, Zbase, capWeightedCoMovingReactionRawDQL2History,
      if_pos hsr, Fh]
  simpa only [Ztot, Zbase, Fh, hintEq] using hrep

theorem capWeightedCoMovingFluxRawDQBUCHistoryIio_continuousOn_Iio
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    ContinuousOn
      (capWeightedCoMovingFluxRawDQBUCHistoryIio
        p hM hT eta R c h heta Traj W r) (Set.Iio r) := by
  refine (capWeightedCoMovingFluxRawDQBUCHistory_continuousOn_Iio
    p hM hT (R := R) (c := c) (h := h) heta Traj W).congr ?_
  intro s hs
  have hsr : s < r := hs
  rw [capWeightedCoMovingFluxRawDQBUCHistoryIio, if_pos hsr]

theorem capWeightedCoMovingReactionRawDQBUCHistoryIio_continuousOn_Iio
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    ContinuousOn
      (capWeightedCoMovingReactionRawDQBUCHistoryIio
        p hM hT eta R c h heta Traj W r) (Set.Iio r) := by
  refine (capWeightedCoMovingReactionRawDQBUCHistory_continuousOn_Iio
    p hM hT (R := R) (c := c) (h := h) heta Traj W).congr ?_
  intro s hs
  have hsr : s < r := hs
  rw [capWeightedCoMovingReactionRawDQBUCHistoryIio, if_pos hsr]

theorem capWeightedCoMovingFluxRawDQBUCHistoryIio_aestronglyMeasurable
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    AEStronglyMeasurable
      (capWeightedCoMovingFluxRawDQBUCHistoryIio
        p hM hT eta R c h heta Traj W r) volume := by
  let F := capWeightedCoMovingFluxRawDQBUCHistory
    p hM hT eta R c h heta Traj W r
  have hFIio : AEStronglyMeasurable F (volume.restrict (Set.Iio r)) :=
    (capWeightedCoMovingFluxRawDQBUCHistory_continuousOn_Iio
      p hM hT heta Traj W).aestronglyMeasurable measurableSet_Iio
  have hind : AEStronglyMeasurable ((Set.Iio r).indicator F) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hFIio
  exact hind.congr (Eventually.of_forall fun s => by
    simp only [Set.indicator_apply, Set.mem_Iio]
    by_cases hsr : s < r
    · simp [capWeightedCoMovingFluxRawDQBUCHistoryIio, F, hsr]
    · simp [capWeightedCoMovingFluxRawDQBUCHistoryIio, F, hsr])

theorem capWeightedCoMovingReactionRawDQBUCHistoryIio_aestronglyMeasurable
    (p : CMParams) {M T eta R c h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    AEStronglyMeasurable
      (capWeightedCoMovingReactionRawDQBUCHistoryIio
        p hM hT eta R c h heta Traj W r) volume := by
  let F := capWeightedCoMovingReactionRawDQBUCHistory
    p hM hT eta R c h heta Traj W r
  have hFIio : AEStronglyMeasurable F (volume.restrict (Set.Iio r)) :=
    (capWeightedCoMovingReactionRawDQBUCHistory_continuousOn_Iio
      p hM hT heta Traj W).aestronglyMeasurable measurableSet_Iio
  have hind : AEStronglyMeasurable ((Set.Iio r).indicator F) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hFIio
  exact hind.congr (Eventually.of_forall fun s => by
    simp only [Set.indicator_apply, Set.mem_Iio]
    by_cases hsr : s < r
    · simp [capWeightedCoMovingReactionRawDQBUCHistoryIio, F, hsr]
    · simp [capWeightedCoMovingReactionRawDQBUCHistoryIio, F, hsr])

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.capWeightedCoMovingFluxRawDQBUCHistoryIio_continuousOn_Iio
#print axioms
  ShenWork.Paper1.capWeightedCoMovingReactionRawDQBUCHistoryIio_continuousOn_Iio
#print axioms
  ShenWork.Paper1.capWeightedCoMovingFluxRawDQBUCHistoryIio_aestronglyMeasurable
#print axioms
  ShenWork.Paper1.capWeightedCoMovingReactionRawDQBUCHistoryIio_aestronglyMeasurable
