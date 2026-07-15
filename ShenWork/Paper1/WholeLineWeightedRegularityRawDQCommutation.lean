import ShenWork.Paper1.WholeLineWeightedRegularityDQCommutation

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Commutation of conjugated raw quotients with the moving heat operators

The raw quotient is `eta * f + D_h f`.  Both moving heat operators are
linear and commute with translations, so the whole raw quotient commutes in
one step.  Keeping this identity at the BUC level is what permits the later
Bochner-history argument without differentiating a clamp.
-/

/-- The conjugated raw quotient commutes with the moving value heat flow. -/
theorem rawSpatialDifferenceQuotient_paper5MovingFrameHeatOp_buc
    {t : ℝ} (ht : 0 < t) (c h eta : ℝ)
    (u : WholeLineBUC) (x : ℝ) :
    eta * paper5MovingFrameHeatOp c t u.1 x +
        spatialDifferenceQuotient h
          (paper5MovingFrameHeatOp c t u.1) x =
      paper5MovingFrameHeatOp c t
        (fun y => eta * u.1 y + spatialDifferenceQuotient h u.1 y) x := by
  rw [spatialDifferenceQuotient_paper5MovingFrameHeatOp ht c h u x]
  let q : WholeLineBUC := wholeLineBUCSpatialDifferenceQuotientCLM h u
  have hlin : wholeLineCauchyHeatBUC t ht (eta • u + q) =
      eta • wholeLineCauchyHeatBUC t ht u +
        wholeLineCauchyHeatBUC t ht q := by
    rw [← wholeLineCauchyHeatBUCCLM_apply,
      ← wholeLineCauchyHeatBUCCLM_apply,
      ← wholeLineCauchyHeatBUCCLM_apply]
    exact (wholeLineCauchyHeatBUCCLM t ht).map_add (eta • u) q |>.trans
      (congrArg (fun z => z + wholeLineCauchyHeatBUCCLM t ht q)
        ((wholeLineCauchyHeatBUCCLM t ht).map_smul eta u))
  have hpoint := congrArg
    (fun w : WholeLineBUC => w.1 (x + c * t)) hlin
  have hq : q.1 = spatialDifferenceQuotient h u.1 := by
    exact wholeLineBUCSpatialDifferenceQuotientCLM_coe h u
  change eta * wholeLineCauchyHeatOp t u.1 (x + c * t) +
      wholeLineCauchyHeatOp t (spatialDifferenceQuotient h u.1)
        (x + c * t) = _
  simpa only [paper5MovingFrameHeatOp, wholeLineCauchyHeatBUC_apply,
    Submodule.coe_add, Submodule.coe_smul,
    BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, q, hq] using hpoint.symm

/-- The conjugated raw quotient commutes with the moving heat-gradient
flow. -/
theorem rawSpatialDifferenceQuotient_paper5MovingFrameHeatGradOp_buc
    {t : ℝ} (ht : 0 < t) (c h eta : ℝ)
    (u : WholeLineBUC) (x : ℝ) :
    eta * paper5MovingFrameHeatGradOp c t u.1 x +
        spatialDifferenceQuotient h
          (paper5MovingFrameHeatGradOp c t u.1) x =
      paper5MovingFrameHeatGradOp c t
        (fun y => eta * u.1 y + spatialDifferenceQuotient h u.1 y) x := by
  rw [spatialDifferenceQuotient_paper5MovingFrameHeatGradOp ht c h u x]
  let q : WholeLineBUC := wholeLineBUCSpatialDifferenceQuotientCLM h u
  have hlin : wholeLineCauchyHeatGradientBUC t ht (eta • u + q) =
      eta • wholeLineCauchyHeatGradientBUC t ht u +
        wholeLineCauchyHeatGradientBUC t ht q := by
    rw [← wholeLineCauchyHeatGradientBUCCLM_apply,
      ← wholeLineCauchyHeatGradientBUCCLM_apply,
      ← wholeLineCauchyHeatGradientBUCCLM_apply]
    exact (wholeLineCauchyHeatGradientBUCCLM t ht).map_add (eta • u) q |>.trans
      (congrArg (fun z => z + wholeLineCauchyHeatGradientBUCCLM t ht q)
        ((wholeLineCauchyHeatGradientBUCCLM t ht).map_smul eta u))
  have hpoint := congrArg
    (fun w : WholeLineBUC => w.1 (x + c * t)) hlin
  have hq : q.1 = spatialDifferenceQuotient h u.1 := by
    exact wholeLineBUCSpatialDifferenceQuotientCLM_coe h u
  change eta * wholeLineCauchyHeatGradOp t u.1 (x + c * t) +
      wholeLineCauchyHeatGradOp t (spatialDifferenceQuotient h u.1)
        (x + c * t) = _
  simpa only [paper5MovingFrameHeatGradOp,
    wholeLineCauchyHeatGradientBUC_apply,
    Submodule.coe_add, Submodule.coe_smul,
    BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, q, hq] using hpoint.symm

#print axioms rawSpatialDifferenceQuotient_paper5MovingFrameHeatOp_buc
#print axioms rawSpatialDifferenceQuotient_paper5MovingFrameHeatGradOp_buc

end ShenWork.Paper1
