import ShenWork.Paper1.WholeLineWeightedRegularityRawDQ

open MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Crude fixed-step raw-quotient bounds

The Henry estimate ultimately removes the inverse-step loss from the spatial
difference quotient.  Before applying Henry, however, one only needs a finite
bound for each fixed nonzero step.  The cap translation estimate supplies
that preliminary bound directly from the value energy, uniformly in the cap
radius.
-/

/-- A cap-weighted value bound produces an honest `L²` representative of the
conjugated raw spatial quotient at every fixed nonzero step.  The displayed
constant may depend on the step, but is independent of the cap radius. -/
theorem exists_capWeighted_rawSpatialDifferenceQuotientL2_of_value
    {eta R h B0 : ℝ}
    (heta : 0 ≤ eta) (hh : h ≠ 0) (hB0 : 0 ≤ B0)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hvalue : Integrable (fun x : ℝ =>
      capWeight eta R x * |w x| ^ 2))
    (hvalue_bound : (∫ x : ℝ,
      capWeight eta R x * |w x| ^ 2) ≤ B0 ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        (eta * w x + spatialDifferenceQuotient h w x)) ∧
      ‖Z‖ ≤ eta * B0 +
        Real.sqrt
          (2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)) * B0 := by
  let C : ℝ :=
    2 * |h⁻¹| ^ 2 * (Real.exp (2 * eta * |h|) + 1)
  let B1 : ℝ := Real.sqrt C * B0
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hB1 : 0 ≤ B1 :=
    mul_nonneg (Real.sqrt_nonneg C) hB0
  have hquot := capWeight_spatialDifferenceQuotient_integrable_of_value
    heta hh hw hvalue
  have hquot_bound :
      (∫ x : ℝ, capWeight eta R x *
        |spatialDifferenceQuotient h w x| ^ 2) ≤ B1 ^ 2 := by
    calc
      (∫ x : ℝ, capWeight eta R x *
          |spatialDifferenceQuotient h w x| ^ 2) ≤
          C * ∫ x : ℝ, capWeight eta R x * |w x| ^ 2 := by
            simpa only [C] using hquot.2
      _ ≤ C * B0 ^ 2 :=
        mul_le_mul_of_nonneg_left hvalue_bound hC
      _ = B1 ^ 2 := by
        dsimp only [B1]
        rw [mul_pow, Real.sq_sqrt hC]
  simpa only [B1, C] using
    exists_capWeighted_rawSpatialDifferenceQuotientL2
      heta hB0 hB1 hw hvalue hvalue_bound hquot.1 hquot_bound

#print axioms exists_capWeighted_rawSpatialDifferenceQuotientL2_of_value

end ShenWork.Paper1
