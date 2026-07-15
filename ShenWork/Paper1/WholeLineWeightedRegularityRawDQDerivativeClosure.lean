import ShenWork.Paper1.WholeLineWeightedRegularityRawDQFatou
import ShenWork.Paper1.WholeLineWeightedRegularityGradientClosure

open Filter Topology MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# From raw finite differences to the weighted spatial derivative

This file specializes the fixed-cap Fatou theorem to the canonical sequence
of nonzero steps `(n + 1)⁻¹`.  It then performs the cap exhaustion already
isolated in `WholeLineWeightedRegularityGradientClosure`.  The hypotheses are
only uniform `L²` representatives of raw finite differences and classical
`C¹` spatial regularity; no weighted derivative is assumed.
-/

/-- Uniform fixed-cap raw-difference-quotient estimates pass to the actual
raw derivative bracket. -/
theorem exists_capWeighted_rawPopulationXL2_of_uniform_rawDQ
    {eta R B c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hU1 : ContDiff ℝ 1 U)
    (hrep : ∀ n : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          rawSpatialDifferenceQuotient eta
            ((1 : ℝ) / (n + 1))
            (fun y => coMovingPath c u t y - U y) x) ∧
      ‖Z‖ ≤ B) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          paper5RawPopulationX eta (coMovingPath c u) U t x) ∧
      ‖Z‖ ≤ B := by
  have hw : Continuous (fun y => coMovingPath c u t y - U y) :=
    hu1.continuous.sub hU1.continuous
  have hdu : Continuous (deriv (coMovingPath c u t)) :=
    hu1.continuous_deriv (by norm_num)
  have hdU : Continuous (deriv U) :=
    hU1.continuous_deriv (by norm_num)
  have hraw : Continuous
      (paper5RawPopulationX eta (coMovingPath c u) U t) := by
    unfold paper5RawPopulationX
    exact (continuous_const.mul (hu1.continuous.sub hU1.continuous)).add
      (hdu.sub hdU)
  have hstep : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop
      (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0))
    · filter_upwards with n
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact one_div_ne_zero (ne_of_gt hn)
  refine exists_capWeighted_rawDQLimitL2_of_uniform_representatives
    (eta := eta) (R := R) (B := B)
    (w := fun y => coMovingPath c u t y - U y)
    (q := paper5RawPopulationX eta (coMovingPath c u) U t)
    (step := fun n : ℕ => (1 : ℝ) / (n + 1))
    hB hw hraw ?_ hrep
  intro x
  have hderiv :=
    ((hu1.differentiable (by norm_num) x).hasDerivAt.sub
      (hU1.differentiable (by norm_num) x).hasDerivAt)
  have hlim := rawSpatialDifferenceQuotient_tendsto
    (eta := eta) hderiv
  simpa only [paper5RawPopulationX] using hlim.comp hstep

/-- A single bound uniform in both the cap radius and the canonical nonzero
finite-difference steps yields the exact weighted `hWx2` integrability input.
-/
theorem paper5WeightedPopulationX_sq_integrable_of_uniform_rawDQ
    {eta B c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (heta : 0 < eta) (hB : 0 ≤ B)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hU1 : ContDiff ℝ 1 U)
    (hrep : ∀ N n : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta (N : ℝ) x *
          rawSpatialDifferenceQuotient eta
            ((1 : ℝ) / (n + 1))
            (fun y => coMovingPath c u t y - U y) x) ∧
      ‖Z‖ ≤ B) :
    Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)
      volume := by
  have hdu : Continuous (deriv (coMovingPath c u t)) :=
    hu1.continuous_deriv (by norm_num)
  have hdU : Continuous (deriv U) :=
    hU1.continuous_deriv (by norm_num)
  refine paper5WeightedPopulationX_sq_integrable_of_uniform_cap_representatives
    heta hB ?_ ?_
  · unfold paper5RawPopulationX
    exact (continuous_const.mul (hu1.continuous.sub hU1.continuous)).add
      (hdu.sub hdU)
  · intro N
    exact exists_capWeighted_rawPopulationXL2_of_uniform_rawDQ
      hB hu1 hU1 (hrep N)

#print axioms exists_capWeighted_rawPopulationXL2_of_uniform_rawDQ
#print axioms paper5WeightedPopulationX_sq_integrable_of_uniform_rawDQ

end ShenWork.Paper1
