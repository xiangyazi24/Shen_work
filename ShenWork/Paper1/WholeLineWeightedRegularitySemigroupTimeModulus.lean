import ShenWork.Paper1.WholeLineWeightedRegularityL2Semigroup
import Mathlib.Analysis.Calculus.MeanValue

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-lag time moduli for the weighted heat semigroup

The semigroup is not operator-norm continuous at zero.  After one positive
heat lag, however, the analytic-generator bound gives the precise estimate
needed when a Duhamel history is split into a near and a far part.
-/

/-- On a positive lag interval, the weighted heat orbit is Lipschitz in time
with the expected inverse distance from the zero-lag face. -/
theorem weightedMovingHeatL2Semigroup_sub_norm_le_of_positive_lag
    {eta c H r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hrhH : r + h ≤ H)
    (Z : WholeLineRealL2) :
    ‖weightedMovingHeatL2Semigroup eta c (r + h) Z -
        weightedMovingHeatL2Semigroup eta c r Z‖ ≤
      (weightedMovingHeatGeneratorHorizonConst eta c H * r⁻¹ * ‖Z‖) * h := by
  have hH : 0 ≤ H := hr.le.trans (le_add_of_nonneg_right hh) |>.trans hrhH
  have hsegPos : ∀ q ∈ Set.Icc r (r + h), 0 < q := by
    intro q hq
    exact hr.trans_le hq.1
  have hderiv : ∀ q ∈ Set.Icc r (r + h),
      HasDerivWithinAt
        (fun s : ℝ => weightedMovingHeatL2Semigroup eta c s Z)
        (weightedMovingHeatL2Generator eta c q Z)
        (Set.Icc r (r + h)) q := by
    intro q hq
    exact (weightedMovingHeatL2Semigroup_orbit_hasDerivAt
      (eta := eta) (c := c) (hsegPos q hq) Z).hasDerivWithinAt
  have hbound : ∀ q ∈ Set.Icc r (r + h),
      ‖weightedMovingHeatL2Generator eta c q Z‖ ≤
        weightedMovingHeatGeneratorHorizonConst eta c H * r⁻¹ * ‖Z‖ := by
    intro q hq
    have hqH : q ≤ H := hq.2.trans hrhH
    have hop := weightedMovingHeatL2Generator_norm_le_horizon eta c H q
      ⟨hsegPos q hq, hqH⟩
    have hmap : ‖weightedMovingHeatL2Generator eta c q Z‖ ≤
        ‖weightedMovingHeatL2Generator eta c q‖ * ‖Z‖ :=
      ContinuousLinearMap.le_opNorm _ Z
    have hinv : q ^ (-(1 : ℝ)) ≤ r⁻¹ := by
      rw [Real.rpow_neg_one]
      simpa only [one_div] using one_div_le_one_div_of_le hr hq.1
    calc
      ‖weightedMovingHeatL2Generator eta c q Z‖ ≤
          ‖weightedMovingHeatL2Generator eta c q‖ * ‖Z‖ := hmap
      _ ≤ (weightedMovingHeatGeneratorHorizonConst eta c H *
            q ^ (-(1 : ℝ))) * ‖Z‖ := by
        exact mul_le_mul_of_nonneg_right hop (norm_nonneg Z)
      _ ≤ (weightedMovingHeatGeneratorHorizonConst eta c H * r⁻¹) *
            ‖Z‖ := by
        gcongr
        exact weightedMovingHeatGeneratorHorizonConst_nonneg hH
      _ = weightedMovingHeatGeneratorHorizonConst eta c H * r⁻¹ * ‖Z‖ :=
        rfl
  have hmvt := (convex_Icc r (r + h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr (le_add_of_nonneg_right hh))
      (right_mem_Icc.mpr (le_add_of_nonneg_right hh))
  simpa only [add_sub_cancel_left, Real.norm_eq_abs, abs_of_nonneg hh] using hmvt

section AxiomAudit

#print axioms weightedMovingHeatL2Semigroup_sub_norm_le_of_positive_lag

end AxiomAudit

end ShenWork.Paper1
