import ShenWork.Paper1.WholeLineWeightedRegularityHeatGradientL2
import ShenWork.Paper1.WholeLineWeightedRegularitySemigroupTimeModulus

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-lag time modulus for the weighted heat gradient

The half-time factorization
`G(r + h) - G(r) = G(r / 2) (S(r / 2 + h) - S(r / 2))`
combines the sharp `r⁻¹⁄²` heat-gradient estimate with the positive-lag
`r⁻¹` semigroup modulus.  It therefore needs only an `L²` datum.
-/

/-- Apply-level positive-lag time modulus for the first spatial heat
derivative. -/
theorem weightedMovingHeatL2Gradient_sub_apply_norm_le_of_positive_lag
    {eta c H r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hrhH : r + h ≤ H)
    (Z : WholeLineRealL2) :
    ‖weightedMovingHeatL2Gradient eta c (r + h) Z -
        weightedMovingHeatL2Gradient eta c r Z‖ ≤
      (weightedMovingHeatGrowth eta c (r / 2) /
          Real.sqrt (Real.pi * (r / 2)) *
        weightedMovingHeatGeneratorHorizonConst eta c H *
          (r / 2)⁻¹ * h) * ‖Z‖ := by
  have hrs : 0 < r / 2 := by linarith
  have hq0 : 0 ≤ r / 2 := hrs.le
  have hqh0 : 0 ≤ r / 2 + h := add_nonneg hq0 hh
  have hsum0 : r / 2 + r / 2 = r := by ring
  have hsumh : r / 2 + (r / 2 + h) = r + h := by ring
  have hcomp0 := congrArg
    (fun A : WholeLineRealL2 →L[ℝ] WholeLineRealL2 => A Z)
    (weightedMovingHeatL2Gradient_comp_semigroup_add
      (eta := eta) (c := c) hrs hq0)
  have hcomph := congrArg
    (fun A : WholeLineRealL2 →L[ℝ] WholeLineRealL2 => A Z)
    (weightedMovingHeatL2Gradient_comp_semigroup_add
      (eta := eta) (c := c) hrs hqh0)
  have hrep0 :
      weightedMovingHeatL2Gradient eta c (r / 2)
          (weightedMovingHeatL2Semigroup eta c (r / 2) Z) =
        weightedMovingHeatL2Gradient eta c r Z := by
    simpa only [ContinuousLinearMap.comp_apply, hsum0] using hcomp0
  have hreph :
      weightedMovingHeatL2Gradient eta c (r / 2)
          (weightedMovingHeatL2Semigroup eta c (r / 2 + h) Z) =
        weightedMovingHeatL2Gradient eta c (r + h) Z := by
    simpa only [ContinuousLinearMap.comp_apply, hsumh] using hcomph
  rw [← hreph, ← hrep0, ← map_sub]
  have hsemi := weightedMovingHeatL2Semigroup_sub_norm_le_of_positive_lag
    (eta := eta) (c := c) (H := H) hrs hh
      (by linarith : r / 2 + h ≤ H) Z
  rw [weightedMovingHeatL2Gradient_of_pos hrs]
  calc
    ‖weightedMovingHeatGradientL2CLM eta c (r / 2) hrs
        (weightedMovingHeatL2Semigroup eta c (r / 2 + h) Z -
          weightedMovingHeatL2Semigroup eta c (r / 2) Z)‖ ≤
        (weightedMovingHeatGrowth eta c (r / 2) /
            Real.sqrt (Real.pi * (r / 2))) *
          ‖weightedMovingHeatL2Semigroup eta c (r / 2 + h) Z -
            weightedMovingHeatL2Semigroup eta c (r / 2) Z‖ :=
      weightedMovingHeatGradientL2CLM_apply_norm_le hrs _
    _ ≤ (weightedMovingHeatGrowth eta c (r / 2) /
            Real.sqrt (Real.pi * (r / 2))) *
          ((weightedMovingHeatGeneratorHorizonConst eta c H *
            (r / 2)⁻¹ * ‖Z‖) * h) :=
      mul_le_mul_of_nonneg_left hsemi
        (weightedMovingHeatGradientMass_nonneg hrs)
    _ = _ := by ring

/-- Operator-norm version of the positive-lag heat-gradient modulus. -/
theorem weightedMovingHeatL2Gradient_sub_norm_le_of_positive_lag
    {eta c H r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hrhH : r + h ≤ H) :
    ‖weightedMovingHeatL2Gradient eta c (r + h) -
        weightedMovingHeatL2Gradient eta c r‖ ≤
      weightedMovingHeatGrowth eta c (r / 2) /
          Real.sqrt (Real.pi * (r / 2)) *
        weightedMovingHeatGeneratorHorizonConst eta c H *
          (r / 2)⁻¹ * h := by
  have hrs : 0 < r / 2 := by linarith
  have hH : 0 ≤ H :=
    hr.le.trans (le_add_of_nonneg_right hh) |>.trans hrhH
  have hC : 0 ≤
      weightedMovingHeatGrowth eta c (r / 2) /
          Real.sqrt (Real.pi * (r / 2)) *
        weightedMovingHeatGeneratorHorizonConst eta c H *
          (r / 2)⁻¹ * h := by
    have hm : 0 ≤ weightedMovingHeatGradientMass eta c (r / 2) :=
      weightedMovingHeatGradientMass_nonneg hrs
    have hg : 0 ≤ weightedMovingHeatGeneratorHorizonConst eta c H :=
      weightedMovingHeatGeneratorHorizonConst_nonneg hH
    have hi : 0 ≤ (r / 2)⁻¹ := inv_nonneg.mpr hrs.le
    simpa [weightedMovingHeatGradientMass] using
      mul_nonneg (mul_nonneg (mul_nonneg hm hg) hi) hh
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro Z
  rw [ContinuousLinearMap.sub_apply]
  exact weightedMovingHeatL2Gradient_sub_apply_norm_le_of_positive_lag
    hr hh hrhH Z

section AxiomAudit

#print axioms weightedMovingHeatL2Gradient_sub_apply_norm_le_of_positive_lag
#print axioms weightedMovingHeatL2Gradient_sub_norm_le_of_positive_lag

end AxiomAudit

end ShenWork.Paper1
