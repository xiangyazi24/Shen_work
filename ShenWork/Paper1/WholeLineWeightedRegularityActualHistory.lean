import ShenWork.Paper1.WholeLineWeightedRegularityMild
import ShenWork.Paper1.WholeLineWeightedRegularityL2History
import ShenWork.Paper1.WholeLineWeightedRegularityRestart

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

/-- The cap-conjugated chemotaxis slice in a moving-frame Picard comparison. -/
def capWeightedPicardChemotaxisHistoryRaw
    (p : CMParams) {M T : ℝ} (_hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c : ℝ) (U₂ U₁ : WholeLineBUCTrajectory T)
    (t s x : ℝ) : ℝ :=
  capWeightSqrt eta R x *
    paper5MovingFrameHeatGradOp c (t - s)
      (coMovingTruncatedChemotaxisDifference p M c s
        (wholeLineBUCTrajectoryExtend hT U₂ s).1
        (wholeLineBUCTrajectoryExtend hT U₁ s).1) x

/-- The cap-conjugated reaction slice in the same comparison. -/
def capWeightedPicardReactionHistoryRaw
    (p : CMParams) {M T : ℝ} (_hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c : ℝ) (U₂ U₁ : WholeLineBUCTrajectory T)
    (t s x : ℝ) : ℝ :=
  capWeightSqrt eta R x *
    paper5MovingFrameHeatOp c (t - s)
      (coMovingTruncatedReactionDifference p M c s
        (wholeLineBUCTrajectoryExtend hT U₂ s).1
        (wholeLineBUCTrajectoryExtend hT U₁ s).1) x

/-- Scalar heat convolution preserves pointwise differences of BUC inputs.
This is stated at the scalar operator level to avoid the duplicate additive
instances carried by the reducible BUC submodule abbreviation. -/
theorem wholeLineCauchyHeatOp_sub_buc
    {t : ℝ} (ht : 0 < t) (u₂ u₁ : WholeLineBUC) (x : ℝ) :
    wholeLineCauchyHeatOp t (fun y => u₂.1 y - u₁.1 y) x =
      wholeLineCauchyHeatOp t u₂.1 x -
        wholeLineCauchyHeatOp t u₁.1 x := by
  let D : WholeLineBUC := ⟨u₂.1 - u₁.1, u₂.2.sub u₁.2⟩
  have hconv := kernelConvVal_sub
    (wholeLineModifiedHeatKernel_continuous ht)
    (wholeLineModifiedHeatKernel_integrable ht) u₂.1 u₁.1 x
  have hD := kernelConvVal_wholeLineModifiedHeatKernel_eq ht D x
  have h₂ := kernelConvVal_wholeLineModifiedHeatKernel_eq ht u₂ x
  have h₁ := kernelConvVal_wholeLineModifiedHeatKernel_eq ht u₁ x
  rw [hD, h₂, h₁] at hconv
  simpa [D] using hconv

/-- Scalar heat-gradient convolution preserves pointwise differences of BUC
inputs. -/
theorem wholeLineCauchyHeatGradOp_sub_buc
    {t : ℝ} (ht : 0 < t) (u₂ u₁ : WholeLineBUC) (x : ℝ) :
    wholeLineCauchyHeatGradOp t (fun y => u₂.1 y - u₁.1 y) x =
      wholeLineCauchyHeatGradOp t u₂.1 x -
        wholeLineCauchyHeatGradOp t u₁.1 x := by
  let D : WholeLineBUC := ⟨u₂.1 - u₁.1, u₂.2.sub u₁.2⟩
  have hconv := kernelConvVal_sub
    (wholeLineModifiedHeatGradientKernel_continuous ht)
    (wholeLineModifiedHeatGradientKernel_integrable ht) u₂.1 u₁.1 x
  have hD := kernelConvVal_wholeLineModifiedHeatGradientKernel_eq ht D x
  have h₂ := kernelConvVal_wholeLineModifiedHeatGradientKernel_eq ht u₂ x
  have h₁ := kernelConvVal_wholeLineModifiedHeatGradientKernel_eq ht u₁ x
  rw [hD, h₂, h₁] at hconv
  simpa [D] using hconv

/-- The heat-gradient convolution commutes with scalar multiplication for a
BUC input. -/
theorem wholeLineCauchyHeatGradOp_const_mul_buc
    {t : ℝ} (a : ℝ) (u : WholeLineBUC) (x : ℝ) :
    wholeLineCauchyHeatGradOp t (fun y => a * u.1 y) x =
      a * wholeLineCauchyHeatGradOp t u.1 x := by
  unfold wholeLineCauchyHeatGradOp
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem capWeightedPicardChemotaxisHistoryRaw_eq_gradientBUCIntegrand
    (p : CMParams) {M T eta R c t s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U₂ U₁ : WholeLineBUCTrajectory T) (hst : s < t) (x : ℝ) :
    capWeightedPicardChemotaxisHistoryRaw
        p hM hT eta R c U₂ U₁ t s x =
      capWeightSqrt eta R x * (-p.χ) *
        ((wholeLineCauchyGradientBUCIntegrand p hM hT U₂ t s).1
            (x + c * t) -
          (wholeLineCauchyGradientBUCIntegrand p hM hT U₁ t s).1
            (x + c * t)) := by
  have htau : 0 < t - s := sub_pos.mpr hst
  let F₂ : WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U₂ s
  let F₁ : WholeLineBUC := wholeLineCauchyFluxSourceTrajectory p hM hT U₁ s
  have hshift := wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift
    (t - s) (c * s) (fun y => (-p.χ) * (F₂.1 y - F₁.1 y))
      (x + c * (t - s))
  have hpoint :
      wholeLineCauchyHeatGradOp (t - s)
          (fun y => (-p.χ) * (F₂.1 y - F₁.1 y))
          (x + c * t) =
        wholeLineCauchyHeatGradOp (t - s)
          (fun y => (-p.χ) *
            (F₂.1 (y + c * s) - F₁.1 (y + c * s)))
          (x + c * (t - s)) := by
    simpa only [show x + c * (t - s) + c * s = x + c * t by ring]
      using hshift
  have hlinx : wholeLineCauchyHeatGradOp (t - s)
        (fun y => (-p.χ) * (F₂.1 y - F₁.1 y)) (x + c * t) =
      (-p.χ) *
        (wholeLineCauchyHeatGradOp (t - s) F₂.1 (x + c * t) -
          wholeLineCauchyHeatGradOp (t - s) F₁.1 (x + c * t)) := by
    let D : WholeLineBUC := ⟨F₂.1 - F₁.1, F₂.2.sub F₁.2⟩
    calc
      wholeLineCauchyHeatGradOp (t - s)
          (fun y => (-p.χ) * (F₂.1 y - F₁.1 y)) (x + c * t) =
          (-p.χ) * wholeLineCauchyHeatGradOp (t - s) D.1
            (x + c * t) := by
        simpa [D] using wholeLineCauchyHeatGradOp_const_mul_buc
          (t := t - s) (-p.χ) D (x + c * t)
      _ = _ := by
        have hDsub :
            wholeLineCauchyHeatGradOp (t - s) D.1 (x + c * t) =
              wholeLineCauchyHeatGradOp (t - s) F₂.1 (x + c * t) -
                wholeLineCauchyHeatGradOp (t - s) F₁.1 (x + c * t) := by
          simpa [D] using
            wholeLineCauchyHeatGradOp_sub_buc htau F₂ F₁ (x + c * t)
        rw [hDsub]
  unfold capWeightedPicardChemotaxisHistoryRaw
    paper5MovingFrameHeatGradOp coMovingTruncatedChemotaxisDifference
  change capWeightSqrt eta R x *
      wholeLineCauchyHeatGradOp (t - s)
        (fun y => (-p.χ) * (F₂.1 (y + c * s) - F₁.1 (y + c * s)))
        (x + c * (t - s)) = _
  rw [← hpoint, hlinx]
  have hI₂ :
      (wholeLineCauchyGradientBUCIntegrand p hM hT U₂ t s).1
          (x + c * t) =
        wholeLineCauchyHeatGradOp (t - s) F₂.1 (x + c * t) := by
    simp [wholeLineCauchyGradientBUCIntegrand,
      wholeLineCauchyHeatGradientBUCTotal, htau, F₂]
  have hI₁ :
      (wholeLineCauchyGradientBUCIntegrand p hM hT U₁ t s).1
          (x + c * t) =
        wholeLineCauchyHeatGradOp (t - s) F₁.1 (x + c * t) := by
    simp [wholeLineCauchyGradientBUCIntegrand,
      wholeLineCauchyHeatGradientBUCTotal, htau, F₁]
  rw [hI₂, hI₁]
  ring

theorem capWeightedPicardReactionHistoryRaw_eq_valueBUCIntegrand
    (p : CMParams) {M T eta R c t s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U₂ U₁ : WholeLineBUCTrajectory T) (hst : s < t) (x : ℝ) :
    capWeightedPicardReactionHistoryRaw
        p hM hT eta R c U₂ U₁ t s x =
      capWeightSqrt eta R x *
        ((wholeLineCauchyValueBUCIntegrand p hM hT U₂ t s).1
            (x + c * t) -
          (wholeLineCauchyValueBUCIntegrand p hM hT U₁ t s).1
            (x + c * t)) := by
  have htau : 0 < t - s := sub_pos.mpr hst
  let F₂ : WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U₂ s
  let F₁ : WholeLineBUC := wholeLineCauchyReactionSourceTrajectory p hM hT U₁ s
  have hshift := wholeLineCauchyHeatOp_eval_shift_eq_input_shift
    (t - s) (c * s) (fun y => F₂.1 y - F₁.1 y)
      (x + c * (t - s))
  have hpoint :
      wholeLineCauchyHeatOp (t - s) (fun y => F₂.1 y - F₁.1 y)
          (x + c * t) =
        wholeLineCauchyHeatOp (t - s)
          (fun y => F₂.1 (y + c * s) - F₁.1 (y + c * s))
          (x + c * (t - s)) := by
    simpa only [show x + c * (t - s) + c * s = x + c * t by ring]
      using hshift
  have hlinx : wholeLineCauchyHeatOp (t - s)
        (fun y => F₂.1 y - F₁.1 y) (x + c * t) =
      wholeLineCauchyHeatOp (t - s) F₂.1 (x + c * t) -
        wholeLineCauchyHeatOp (t - s) F₁.1 (x + c * t) := by
    exact wholeLineCauchyHeatOp_sub_buc htau F₂ F₁ (x + c * t)
  unfold capWeightedPicardReactionHistoryRaw
    paper5MovingFrameHeatOp coMovingTruncatedReactionDifference
  change capWeightSqrt eta R x *
      wholeLineCauchyHeatOp (t - s)
        (fun y => F₂.1 (y + c * s) - F₁.1 (y + c * s))
        (x + c * (t - s)) = _
  rw [← hpoint, hlinx]
  have hI₂ :
      (wholeLineCauchyValueBUCIntegrand p hM hT U₂ t s).1
          (x + c * t) =
        wholeLineCauchyHeatOp (t - s) F₂.1 (x + c * t) := by
    simp [wholeLineCauchyValueBUCIntegrand,
      wholeLineCauchyHeatBUCTotal, htau, F₂]
  have hI₁ :
      (wholeLineCauchyValueBUCIntegrand p hM hT U₁ t s).1
          (x + c * t) =
        wholeLineCauchyHeatOp (t - s) F₁.1 (x + c * t) := by
    simp [wholeLineCauchyValueBUCIntegrand,
      wholeLineCauchyHeatBUCTotal, htau, F₁]
  rw [hI₂, hI₁]

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.capWeightedPicardChemotaxisHistoryRaw_eq_gradientBUCIntegrand
#print axioms
  ShenWork.Paper1.capWeightedPicardReactionHistoryRaw_eq_valueBUCIntegrand
