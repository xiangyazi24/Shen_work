import ShenWork.Paper1.WholeLineWeightedRegularityRawDQCommutation

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-- The conjugated raw spatial quotient used in the cap exhaustion. -/
def rawSpatialDifferenceQuotient
    (eta h : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  eta * f x + spatialDifferenceQuotient h f x

/-- Linear BUC realization of the conjugated raw spatial quotient. -/
def wholeLineBUCRawSpatialDifferenceQuotientLinearMap (eta h : ℝ) :
    WholeLineBUC →ₗ[ℝ] WholeLineBUC where
  toFun := fun u => eta • u + h⁻¹ • (wholeLineBUCTranslate h u - u)
  map_add' := by
    intro u v
    rw [wholeLineBUCTranslate_add]
    module
  map_smul' := by
    intro r u
    rw [wholeLineBUCTranslate_smul]
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    simp [smul_eq_mul]
    ring

/-- Continuous BUC realization of the conjugated raw spatial quotient. -/
def wholeLineBUCRawSpatialDifferenceQuotientCLM (eta h : ℝ) :
    WholeLineBUC →L[ℝ] WholeLineBUC :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (σ := RingHom.id ℝ) (E := WholeLineBUC) (F := WholeLineBUC)
    (wholeLineBUCRawSpatialDifferenceQuotientLinearMap eta h)
    (|eta| + 2 * |h⁻¹|) (fun u => by
      change ‖eta • u + h⁻¹ • (wholeLineBUCTranslate h u - u)‖ ≤
        (|eta| + 2 * |h⁻¹|) * ‖u‖
      calc
        ‖eta • u + h⁻¹ • (wholeLineBUCTranslate h u - u)‖ ≤
            ‖eta • u‖ + ‖h⁻¹ • (wholeLineBUCTranslate h u - u)‖ :=
          by simpa only using
            (norm_add_le (eta • u)
              (h⁻¹ • (wholeLineBUCTranslate h u - u)))
        _ = |eta| * ‖u‖ + |h⁻¹| *
            ‖wholeLineBUCTranslate h u - u‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ |eta| * ‖u‖ + |h⁻¹| * (2 * ‖u‖) := by
          gcongr
          calc
            ‖wholeLineBUCTranslate h u - u‖ ≤
                ‖wholeLineBUCTranslate h u‖ + ‖u‖ := by
              simpa only using
                (norm_sub_le (wholeLineBUCTranslate h u) u)
            _ ≤ ‖u‖ + ‖u‖ :=
              add_le_add (wholeLineBUCTranslate_norm_le h u) le_rfl
            _ = 2 * ‖u‖ := by ring
        _ = (|eta| + 2 * |h⁻¹|) * ‖u‖ := by ring)

@[simp] theorem wholeLineBUCRawSpatialDifferenceQuotientCLM_coe
    (eta h : ℝ) (u : WholeLineBUC) :
    (wholeLineBUCRawSpatialDifferenceQuotientCLM eta h u).1 =
      rawSpatialDifferenceQuotient eta h u.1 := by
  funext x
  change (eta • u + h⁻¹ • (wholeLineBUCTranslate h u - u)).1 x = _
  simp [rawSpatialDifferenceQuotient, spatialDifferenceQuotient,
    div_eq_mul_inv, smul_eq_mul]
  ring

theorem rawSpatialDifferenceQuotient_add
    (eta h : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    rawSpatialDifferenceQuotient eta h (fun y => f y + g y) x =
      rawSpatialDifferenceQuotient eta h f x +
        rawSpatialDifferenceQuotient eta h g x := by
  unfold rawSpatialDifferenceQuotient spatialDifferenceQuotient
  ring

theorem rawSpatialDifferenceQuotient_sub
    (eta h : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    rawSpatialDifferenceQuotient eta h (fun y => f y - g y) x =
      rawSpatialDifferenceQuotient eta h f x -
        rawSpatialDifferenceQuotient eta h g x := by
  unfold rawSpatialDifferenceQuotient spatialDifferenceQuotient
  ring

theorem rawSpatialDifferenceQuotient_const_mul
    (eta h a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    rawSpatialDifferenceQuotient eta h (fun y => a * f y) x =
      a * rawSpatialDifferenceQuotient eta h f x := by
  unfold rawSpatialDifferenceQuotient spatialDifferenceQuotient
  ring

/-- The BUC raw-quotient map commutes with interval integration. -/
theorem wholeLineBUCRawSpatialDifferenceQuotientCLM_intervalIntegral
    {a b eta h : ℝ} {F : ℝ → WholeLineBUC}
    (hF : IntervalIntegrable F volume a b) :
    wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
        (∫ s in a..b, F s) =
      ∫ s in a..b, wholeLineBUCRawSpatialDifferenceQuotientCLM eta h (F s) := by
  have hcomm :
      (∫ s in a..b, wholeLineBUCRawSpatialDifferenceQuotientCLM eta h (F s)) =
        wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
          (∫ s in a..b, F s) :=
    @ContinuousLinearMap.intervalIntegral_comp_comm
      ℝ WholeLineBUC WholeLineBUC
      WholeLineBUC.normedAddCommGroup inferInstance
      a b volume F
      inferInstance inferInstance WholeLineBUC.normedAddCommGroup
      inferInstance inferInstance
      wholeLineBUCMetricCompleteSpace wholeLineBUCMetricCompleteSpace
      (wholeLineBUCRawSpatialDifferenceQuotientCLM eta h) hF
  exact hcomm.symm

/-- Value moving heat flow commutes with the raw quotient, in the named raw
interface. -/
theorem rawSpatialDifferenceQuotient_movingFrameHeatOp
    {t : ℝ} (ht : 0 < t) (c h eta : ℝ)
    (u : WholeLineBUC) (x : ℝ) :
    rawSpatialDifferenceQuotient eta h
        (paper5MovingFrameHeatOp c t u.1) x =
      paper5MovingFrameHeatOp c t
        (rawSpatialDifferenceQuotient eta h u.1) x := by
  exact rawSpatialDifferenceQuotient_paper5MovingFrameHeatOp_buc
    ht c h eta u x

/-- Gradient moving heat flow commutes with the raw quotient. -/
theorem rawSpatialDifferenceQuotient_movingFrameHeatGradOp
    {t : ℝ} (ht : 0 < t) (c h eta : ℝ)
    (u : WholeLineBUC) (x : ℝ) :
    rawSpatialDifferenceQuotient eta h
        (paper5MovingFrameHeatGradOp c t u.1) x =
      paper5MovingFrameHeatGradOp c t
        (rawSpatialDifferenceQuotient eta h u.1) x := by
  exact rawSpatialDifferenceQuotient_paper5MovingFrameHeatGradOp_buc
    ht c h eta u x

#print axioms wholeLineBUCRawSpatialDifferenceQuotientCLM_intervalIntegral
#print axioms rawSpatialDifferenceQuotient_movingFrameHeatOp
#print axioms rawSpatialDifferenceQuotient_movingFrameHeatGradOp

end ShenWork.Paper1
