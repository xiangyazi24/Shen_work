import ShenWork.Paper1.WholeLineWeightedRegularityBUCTranslate
import ShenWork.Paper1.WholeLineWeightedRegularitySpatialDifference

open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace ShenWork.Paper1

theorem wholeLineBUCTranslate_norm_le (a : ℝ) (u : WholeLineBUC) :
    ‖wholeLineBUCTranslate a u‖ ≤ ‖u‖ := by
  change ‖(wholeLineBUCTranslate a u).1‖ ≤ ‖u.1‖
  apply (BoundedContinuousFunction.norm_le (norm_nonneg u.1)).2
  intro x
  exact WholeLineBUC.abs_apply_le_norm u (x + a)

theorem wholeLineBUCTranslate_add (a : ℝ) (u v : WholeLineBUC) :
    wholeLineBUCTranslate a (u + v) =
      wholeLineBUCTranslate a u + wholeLineBUCTranslate a v := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  rfl

theorem wholeLineBUCTranslate_smul (a r : ℝ) (u : WholeLineBUC) :
    wholeLineBUCTranslate a (r • u) = r • wholeLineBUCTranslate a u := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  rfl

def wholeLineBUCTranslateLinearMap (a : ℝ) :
    WholeLineBUC →ₗ[ℝ] WholeLineBUC where
  toFun := wholeLineBUCTranslate a
  map_add' := wholeLineBUCTranslate_add a
  map_smul' := wholeLineBUCTranslate_smul a

def wholeLineBUCTranslateCLM (a : ℝ) :
    WholeLineBUC →L[ℝ] WholeLineBUC :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (σ := RingHom.id ℝ) (E := WholeLineBUC) (F := WholeLineBUC)
    (wholeLineBUCTranslateLinearMap a) 1 (fun u => by
    change ‖wholeLineBUCTranslate a u‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using wholeLineBUCTranslate_norm_le a u)

@[simp] theorem wholeLineBUCTranslateCLM_apply
    (a : ℝ) (u : WholeLineBUC) :
    wholeLineBUCTranslateCLM a u = wholeLineBUCTranslate a u := by
  change wholeLineBUCTranslate a u = _
  rfl

def wholeLineBUCSpatialDifferenceQuotientLinearMap (h : ℝ) :
    WholeLineBUC →ₗ[ℝ] WholeLineBUC where
  toFun := fun u => h⁻¹ • (wholeLineBUCTranslate h u - u)
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

def wholeLineBUCSpatialDifferenceQuotientCLM (h : ℝ) :
    WholeLineBUC →L[ℝ] WholeLineBUC :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (σ := RingHom.id ℝ) (E := WholeLineBUC) (F := WholeLineBUC)
    (wholeLineBUCSpatialDifferenceQuotientLinearMap h)
    (2 * |h⁻¹|) (fun u => by
      change ‖h⁻¹ • (wholeLineBUCTranslate h u - u)‖ ≤
        2 * |h⁻¹| * ‖u‖
      rw [norm_smul, Real.norm_eq_abs]
      have hsub : ‖wholeLineBUCTranslate h u - u‖ ≤ 2 * ‖u‖ := by
        calc
          ‖wholeLineBUCTranslate h u - u‖ ≤
              ‖wholeLineBUCTranslate h u‖ + ‖u‖ := by
            simpa only using
              (norm_sub_le (wholeLineBUCTranslate h u) u)
          _ ≤ ‖u‖ + ‖u‖ :=
            add_le_add (wholeLineBUCTranslate_norm_le h u) le_rfl
          _ = 2 * ‖u‖ := by ring
      calc
        |h⁻¹| * ‖wholeLineBUCTranslate h u - u‖ ≤
            |h⁻¹| * (2 * ‖u‖) :=
          mul_le_mul_of_nonneg_left hsub (abs_nonneg _)
        _ = (2 * |h⁻¹|) * ‖u‖ := by ring)

@[simp] theorem wholeLineBUCSpatialDifferenceQuotientCLM_apply
    (h : ℝ) (u : WholeLineBUC) (x : ℝ) :
    (wholeLineBUCSpatialDifferenceQuotientCLM h u).1 x =
      spatialDifferenceQuotient h u.1 x := by
  change (h⁻¹ • (wholeLineBUCTranslate h u - u)).1 x = _
  simp [
    spatialDifferenceQuotient, div_eq_mul_inv]
  ring

@[simp] theorem wholeLineBUCSpatialDifferenceQuotientCLM_coe
    (h : ℝ) (u : WholeLineBUC) :
    (wholeLineBUCSpatialDifferenceQuotientCLM h u).1 =
      spatialDifferenceQuotient h u.1 := by
  funext x
  exact wholeLineBUCSpatialDifferenceQuotientCLM_apply h u x

theorem wholeLineBUCSpatialDifferenceQuotientCLM_intervalIntegral
    {a b h : ℝ} {F : ℝ → WholeLineBUC}
    (hF : IntervalIntegrable F volume a b) :
    wholeLineBUCSpatialDifferenceQuotientCLM h (∫ s in a..b, F s) =
      ∫ s in a..b, wholeLineBUCSpatialDifferenceQuotientCLM h (F s) := by
  have hcomm :
      (∫ s in a..b, wholeLineBUCSpatialDifferenceQuotientCLM h (F s)) =
        wholeLineBUCSpatialDifferenceQuotientCLM h (∫ s in a..b, F s) :=
    @ContinuousLinearMap.intervalIntegral_comp_comm
      ℝ WholeLineBUC WholeLineBUC
      WholeLineBUC.normedAddCommGroup inferInstance
      a b volume F
      inferInstance inferInstance WholeLineBUC.normedAddCommGroup
      inferInstance inferInstance
      wholeLineBUCMetricCompleteSpace wholeLineBUCMetricCompleteSpace
      (wholeLineBUCSpatialDifferenceQuotientCLM h) hF
  exact hcomm.symm

def wholeLineCauchyHeatGradientBUCCLM (t : ℝ) (ht : 0 < t) :
    WholeLineBUC →L[ℝ] WholeLineBUC :=
  kernelConvBUCCLM (wholeLineModifiedHeatGradientKernel_continuous ht)
    (wholeLineModifiedHeatGradientKernel_integrable ht)

@[simp] theorem wholeLineCauchyHeatGradientBUCCLM_apply
    (t : ℝ) (ht : 0 < t) (u : WholeLineBUC) :
    wholeLineCauchyHeatGradientBUCCLM t ht u =
      wholeLineCauchyHeatGradientBUC t ht u := by
  rfl

theorem spatialDifferenceQuotient_paper5MovingFrameHeatOp_buc
    {t : ℝ} (ht : 0 < t) (c h : ℝ) (u : WholeLineBUC) (x : ℝ) :
    spatialDifferenceQuotient h
        (paper5MovingFrameHeatOp c t u.1) x =
      paper5MovingFrameHeatOp c t
        (wholeLineBUCSpatialDifferenceQuotientCLM h u).1 x := by
  have hlin :
      wholeLineCauchyHeatBUC t ht
          (wholeLineBUCSpatialDifferenceQuotientCLM h u) =
        h⁻¹ • (wholeLineCauchyHeatBUC t ht
            (wholeLineBUCTranslate h u) -
          wholeLineCauchyHeatBUC t ht u) := by
    rw [← wholeLineCauchyHeatBUCCLM_apply,
      ← wholeLineCauchyHeatBUCCLM_apply,
      ← wholeLineCauchyHeatBUCCLM_apply]
    change wholeLineCauchyHeatBUCCLM t ht
        (h⁻¹ • (wholeLineBUCTranslate h u - u)) = _
    rw [map_smul]
    exact congrArg (fun z : WholeLineBUC => h⁻¹ • z)
      (map_sub (wholeLineCauchyHeatBUCCLM t ht)
        (wholeLineBUCTranslate h u) u)
  have hlinval :
      wholeLineCauchyHeatOp t
          (wholeLineBUCSpatialDifferenceQuotientCLM h u).1
          (x + c * t) =
        h⁻¹ * (wholeLineCauchyHeatOp t
            (wholeLineBUCTranslate h u).1 (x + c * t) -
          wholeLineCauchyHeatOp t u.1 (x + c * t)) := by
    simpa only [wholeLineCauchyHeatBUC_apply,
      Submodule.coe_smul, Submodule.coe_sub,
      BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.coe_sub,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using
      congrArg (fun w : WholeLineBUC => w.1 (x + c * t)) hlin
  change spatialDifferenceQuotient h
      (paper5MovingFrameHeatOp c t u.1) x = _
  rw [spatialDifferenceQuotient,
    paper5MovingFrameHeatOp_eval_shift_eq_input_shift]
  change
    (wholeLineCauchyHeatOp t (wholeLineBUCTranslate h u).1
          (x + c * t) -
        wholeLineCauchyHeatOp t u.1 (x + c * t)) / h = _
  rw [div_eq_mul_inv]
  simpa [paper5MovingFrameHeatOp, mul_comm] using hlinval.symm

theorem spatialDifferenceQuotient_paper5MovingFrameHeatGradOp_buc
    {t : ℝ} (ht : 0 < t) (c h : ℝ) (u : WholeLineBUC) (x : ℝ) :
    spatialDifferenceQuotient h
        (paper5MovingFrameHeatGradOp c t u.1) x =
      paper5MovingFrameHeatGradOp c t
        (wholeLineBUCSpatialDifferenceQuotientCLM h u).1 x := by
  have hlin :
      wholeLineCauchyHeatGradientBUC t ht
          (wholeLineBUCSpatialDifferenceQuotientCLM h u) =
        h⁻¹ • (wholeLineCauchyHeatGradientBUC t ht
            (wholeLineBUCTranslate h u) -
          wholeLineCauchyHeatGradientBUC t ht u) := by
    rw [← wholeLineCauchyHeatGradientBUCCLM_apply,
      ← wholeLineCauchyHeatGradientBUCCLM_apply,
      ← wholeLineCauchyHeatGradientBUCCLM_apply]
    change wholeLineCauchyHeatGradientBUCCLM t ht
        (h⁻¹ • (wholeLineBUCTranslate h u - u)) = _
    rw [map_smul]
    exact congrArg (fun z : WholeLineBUC => h⁻¹ • z)
      (map_sub (wholeLineCauchyHeatGradientBUCCLM t ht)
        (wholeLineBUCTranslate h u) u)
  have hlinval :
      wholeLineCauchyHeatGradOp t
          (wholeLineBUCSpatialDifferenceQuotientCLM h u).1
          (x + c * t) =
        h⁻¹ * (wholeLineCauchyHeatGradOp t
            (wholeLineBUCTranslate h u).1 (x + c * t) -
          wholeLineCauchyHeatGradOp t u.1 (x + c * t)) := by
    simpa only [wholeLineCauchyHeatGradientBUC_apply,
      Submodule.coe_smul, Submodule.coe_sub,
      BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.coe_sub,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using
      congrArg (fun w : WholeLineBUC => w.1 (x + c * t)) hlin
  change spatialDifferenceQuotient h
      (paper5MovingFrameHeatGradOp c t u.1) x = _
  rw [spatialDifferenceQuotient,
    paper5MovingFrameHeatGradOp_eval_shift_eq_input_shift]
  change
    (wholeLineCauchyHeatGradOp t (wholeLineBUCTranslate h u).1
          (x + c * t) -
        wholeLineCauchyHeatGradOp t u.1 (x + c * t)) / h = _
  rw [div_eq_mul_inv]
  simpa [paper5MovingFrameHeatGradOp, mul_comm] using hlinval.symm

theorem spatialDifferenceQuotient_paper5MovingFrameHeatOp
    {t : ℝ} (ht : 0 < t) (c h : ℝ) (u : WholeLineBUC) (x : ℝ) :
    spatialDifferenceQuotient h
        (paper5MovingFrameHeatOp c t u.1) x =
      paper5MovingFrameHeatOp c t
        (spatialDifferenceQuotient h u.1) x := by
  simpa only [wholeLineBUCSpatialDifferenceQuotientCLM_coe] using
    spatialDifferenceQuotient_paper5MovingFrameHeatOp_buc
      ht c h u x

theorem spatialDifferenceQuotient_paper5MovingFrameHeatGradOp
    {t : ℝ} (ht : 0 < t) (c h : ℝ) (u : WholeLineBUC) (x : ℝ) :
    spatialDifferenceQuotient h
        (paper5MovingFrameHeatGradOp c t u.1) x =
      paper5MovingFrameHeatGradOp c t
        (spatialDifferenceQuotient h u.1) x := by
  simpa only [wholeLineBUCSpatialDifferenceQuotientCLM_coe] using
    spatialDifferenceQuotient_paper5MovingFrameHeatGradOp_buc
      ht c h u x

#print axioms wholeLineBUCSpatialDifferenceQuotientCLM_intervalIntegral
#print axioms spatialDifferenceQuotient_paper5MovingFrameHeatOp
#print axioms spatialDifferenceQuotient_paper5MovingFrameHeatGradOp

end ShenWork.Paper1
