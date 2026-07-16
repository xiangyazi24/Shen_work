import ShenWork.Paper1.WholeLineWeightedRegularityHomogeneousDQ
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQ
import ShenWork.Paper1.WholeLineWeightedRegularityRawDQIdentity

open MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Homogeneous raw-DQ estimate

On a positive restart window the homogeneous heat leg gains one spatial
derivative with the standard inverse-square-root loss.  The estimate below
is uniform in the cap radius and, for `|h| ≤ 1`, uniform in the nonzero
finite-difference step.  It is the inhomogeneous Henry argument's initial
term and assumes only the cap-weighted value energy at the restart face.
-/

private theorem sqrt_exp_two_mul (a : ℝ) :
    Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
  rw [show Real.exp (2 * a) = Real.exp a ^ 2 by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos a)]

/-- Cap-weighted raw quotient of a positive-time homogeneous heat slice.
The displayed majorant has exactly a regular part plus a `t⁻¹ᐣ²` part. -/
theorem exists_capWeightedMovingHeat_rawDQL2_le_const_add_invSqrt
    {eta R c t h T F : ℝ}
    (heta : 0 ≤ eta) (ht : 0 < t) (htT : t ≤ T)
    (hh : h ≠ 0) (habs : |h| ≤ 1) (hF : 0 ≤ F)
    (f : WholeLineBUC)
    (hcap : Integrable (fun y : ℝ =>
      capWeight eta R y * |f.1 y| ^ 2))
    (henergy : (∫ y : ℝ,
      capWeight eta R y * |f.1 y| ^ 2) ≤ F ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        paper5MovingFrameHeatOp c t
          (rawSpatialDifferenceQuotient eta h f.1) x) ∧
      ‖Z‖ ≤
        ((2 * capMildGrowthBound eta c T * eta) +
          Real.exp eta *
            (2 * capMildGrowthBound eta c T * eta +
              (2 * capMildGrowthBound eta c T *
                (2 / Real.sqrt (4 * Real.pi))) *
                  t ^ (-(1 / 2 : ℝ)))) * F := by
  let B0 : ℝ := Real.exp (-t) * capHeatSchurMass eta c t * F
  let B1 : ℝ := Real.sqrt (Real.exp (2 * eta * |h|)) *
    (Real.exp (-t) * capHeatGradientSchurMass eta c t) * F
  have hB0 : 0 ≤ B0 := by
    dsimp only [B0]
    exact mul_nonneg
      (mul_nonneg (Real.exp_nonneg _)
        (capHeatSchurMass_pos eta c t).le) hF
  have hB1 : 0 ≤ B1 := by
    dsimp only [B1]
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (Real.exp_nonneg _)
          (capHeatGradientSchurMass_pos ht heta c).le)) hF
  have hvalue := capWeight_movingFrameHeatOp_l2_bounded
    heta ht R c f.1.continuous.measurable hcap
  have hvalue_bound :
      (∫ x : ℝ, capWeight eta R x *
        |paper5MovingFrameHeatOp c t f.1 x| ^ 2) ≤ B0 ^ 2 := by
    calc
      (∫ x : ℝ, capWeight eta R x *
          |paper5MovingFrameHeatOp c t f.1 x| ^ 2) ≤
          (Real.exp (-t) * capHeatSchurMass eta c t) ^ 2 *
            ∫ y : ℝ, capWeight eta R y * |f.1 y| ^ 2 := hvalue.2
      _ ≤ (Real.exp (-t) * capHeatSchurMass eta c t) ^ 2 * F ^ 2 :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
      _ = B0 ^ 2 := by dsimp only [B0]; ring
  have hquot :=
    capWeight_spatialDifferenceQuotient_movingFrameHeatOp_l2_bounded_of_input
      (eta := eta) (R := R) (c := c) (t := t) (h := h)
        heta ht hh (WholeLineBUC.isCUnifBdd f) hcap
  have hquot_bound :
      (∫ x : ℝ, capWeight eta R x *
        |spatialDifferenceQuotient h
          (paper5MovingFrameHeatOp c t f.1) x| ^ 2) ≤ B1 ^ 2 := by
    calc
      (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h
            (paper5MovingFrameHeatOp c t f.1) x| ^ 2) ≤
          Real.exp (2 * eta * |h|) *
            (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 *
              ∫ y : ℝ, capWeight eta R y * |f.1 y| ^ 2 := hquot.2
      _ ≤ Real.exp (2 * eta * |h|) *
            (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 * F ^ 2 := by
        exact mul_le_mul_of_nonneg_left henergy
          (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
      _ = B1 ^ 2 := by
        dsimp only [B1]
        calc
          Real.exp (2 * eta * |h|) *
                (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 * F ^ 2 =
              Real.sqrt (Real.exp (2 * eta * |h|)) ^ 2 *
                (Real.exp (-t) * capHeatGradientSchurMass eta c t) ^ 2 * F ^ 2 := by
            rw [Real.sq_sqrt (Real.exp_pos _).le]
          _ = (Real.sqrt (Real.exp (2 * eta * |h|)) *
                (Real.exp (-t) * capHeatGradientSchurMass eta c t) * F) ^ 2 := by
            ring
  rcases (WholeLineBUC.isCUnifBdd f).2 with ⟨M, hM⟩
  have hheatCont : Continuous (paper5MovingFrameHeatOp c t f.1) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hbase := wholeLineCauchyHeatOp_hasDerivAt
      (f := f.1) (t := t) (x := x + c * t) (M := M) ht
        f.1.continuous.aestronglyMeasurable hM
    have hinner : HasDerivAt (fun z : ℝ => z + c * t) 1 x := by
      simpa using (hasDerivAt_id x).add_const (c * t)
    simpa [paper5MovingFrameHeatOp] using
      (hbase.comp x hinner).continuousAt
  rcases exists_capWeighted_rawSpatialDifferenceQuotientL2
      (w := paper5MovingFrameHeatOp c t f.1)
      heta hB0 hB1 hheatCont
      hvalue.1 hvalue_bound hquot.1 hquot_bound with
    ⟨Z, hZrep, hZnorm⟩
  have hcomm : ∀ x,
      rawSpatialDifferenceQuotient eta h
          (paper5MovingFrameHeatOp c t f.1) x =
        paper5MovingFrameHeatOp c t
          (rawSpatialDifferenceQuotient eta h f.1) x :=
    rawSpatialDifferenceQuotient_movingFrameHeatOp ht c h eta f
  refine ⟨Z, hZrep.trans (Filter.Eventually.of_forall fun x => by
    change capWeightSqrt eta R x *
        rawSpatialDifferenceQuotient eta h
          (paper5MovingFrameHeatOp c t f.1) x =
      capWeightSqrt eta R x * paper5MovingFrameHeatOp c t
        (rawSpatialDifferenceQuotient eta h f.1) x
    rw [hcomm x]), ?_⟩
  have hheat : Real.exp (-t) * capHeatSchurMass eta c t ≤
      2 * capMildGrowthBound eta c T := by
    have hexp : Real.exp (-t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
    calc
      Real.exp (-t) * capHeatSchurMass eta c t ≤
          1 * capHeatSchurMass eta c t :=
        mul_le_mul_of_nonneg_right hexp
          (capHeatSchurMass_pos eta c t).le
      _ = capHeatSchurMass eta c t := one_mul _
      _ ≤ 2 * capMildGrowthBound eta c T :=
        capHeatSchurMass_le_capMildGrowthBound
          (c := c) heta ht.le htT
  have hgrad : Real.exp (-t) * capHeatGradientSchurMass eta c t ≤
      2 * capMildGrowthBound eta c T * eta +
        (2 * capMildGrowthBound eta c T *
          (2 / Real.sqrt (4 * Real.pi))) *
            t ^ (-(1 / 2 : ℝ)) := by
    have hexp : Real.exp (-t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
    calc
      Real.exp (-t) * capHeatGradientSchurMass eta c t ≤
          1 * capHeatGradientSchurMass eta c t :=
        mul_le_mul_of_nonneg_right hexp
          (capHeatGradientSchurMass_pos ht heta c).le
      _ = capHeatGradientSchurMass eta c t := one_mul _
      _ ≤ 2 * capMildGrowthBound eta c T * eta +
          (2 * capMildGrowthBound eta c T *
            (2 / Real.sqrt (4 * Real.pi))) *
              t ^ (-(1 / 2 : ℝ)) :=
        capHeatGradientSchurMass_le_capMildKernel
          (c := c) heta ht htT
  have hsqrt : Real.sqrt (Real.exp (2 * eta * |h|)) ≤ Real.exp eta := by
    have hsqrtEq : Real.sqrt (Real.exp (2 * eta * |h|)) =
        Real.exp (eta * |h|) := by
      convert sqrt_exp_two_mul (eta * |h|) using 1 <;> ring
    rw [hsqrtEq]
    exact Real.exp_le_exp.mpr
      (mul_le_of_le_one_right heta habs)
  let K : ℝ := 2 * capMildGrowthBound eta c T * eta +
    (2 * capMildGrowthBound eta c T *
      (2 / Real.sqrt (4 * Real.pi))) * t ^ (-(1 / 2 : ℝ))
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hG : 0 ≤ capMildGrowthBound eta c T :=
      (Real.exp_pos _).le
    have hfrac : 0 ≤ 2 / Real.sqrt (4 * Real.pi) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hG) heta)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hG) hfrac)
        (Real.rpow_nonneg ht.le _))
  have hB0le : B0 ≤ 2 * capMildGrowthBound eta c T * F := by
    exact mul_le_mul_of_nonneg_right hheat hF
  have hB1le : B1 ≤ Real.exp eta * K * F := by
    dsimp only [B1]
    have hprod : Real.sqrt (Real.exp (2 * eta * |h|)) *
          (Real.exp (-t) * capHeatGradientSchurMass eta c t) ≤
        Real.exp eta * K := by
      exact mul_le_mul hsqrt hgrad
        (mul_nonneg (Real.exp_nonneg _)
          (capHeatGradientSchurMass_pos ht heta c).le)
        (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_right hprod hF
  calc
    ‖Z‖ ≤ eta * B0 + B1 := hZnorm
    _ ≤ eta * (2 * capMildGrowthBound eta c T * F) +
        Real.exp eta * K * F := by
      exact add_le_add (mul_le_mul_of_nonneg_left hB0le heta) hB1le
    _ = ((2 * capMildGrowthBound eta c T * eta) +
          Real.exp eta *
            (2 * capMildGrowthBound eta c T * eta +
              (2 * capMildGrowthBound eta c T *
                (2 / Real.sqrt (4 * Real.pi))) *
                  t ^ (-(1 / 2 : ℝ)))) * F := by ring

section AxiomAudit

#print axioms exists_capWeightedMovingHeat_rawDQL2_le_const_add_invSqrt

end AxiomAudit

end ShenWork.Paper1
