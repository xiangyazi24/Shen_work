import ShenWork.Paper1.WholeLineWeightedRegularityRawDQDerivativeClosure
import ShenWork.Paper1.WholeLineWeightedRegularityActualL2History

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Numerical exact-weight gradient budgets from raw differences

The existing natural raw-DQ closure records only integrability.  Generator
forcing on a compact time window also needs the numerical square budget.  The
same cap representatives already contain that information; retaining it
through monotone cap exhaustion gives the sharpened pair below.
-/

/-- A bound uniform in cap radius and canonical nonzero quotient step gives
both exact-weight gradient integrability and the same squared numerical
budget. -/
theorem paper5WeightedPopulationX_data_of_uniform_rawDQ
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
      volume ∧
      (∫ x : ℝ,
        paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2) ≤
        B ^ 2 := by
  let raw : ℝ → ℝ :=
    paper5RawPopulationX eta (coMovingPath c u) U t
  have hdu : Continuous (deriv (coMovingPath c u t)) :=
    hu1.continuous_deriv (by norm_num)
  have hdU : Continuous (deriv U) :=
    hU1.continuous_deriv (by norm_num)
  have hraw : Continuous raw := by
    dsimp only [raw]
    unfold paper5RawPopulationX
    exact (continuous_const.mul (hu1.continuous.sub hU1.continuous)).add
      (hdu.sub hdU)
  have hcap : ∀ N : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta (N : ℝ) x * raw x) ∧ ‖Z‖ ≤ B := by
    intro N
    simpa only [raw] using
      (exists_capWeighted_rawPopulationXL2_of_uniform_rawDQ
        hB hu1 hU1 (hrep N))
  have hcap_int : ∀ N : ℕ, Integrable (fun x : ℝ =>
      capWeight eta (N : ℝ) x * |raw x| ^ 2) := by
    intro N
    obtain ⟨Z, hZrep, hZnorm⟩ := hcap N
    exact (capEnergy_of_wholeLineRealL2_rep hB Z hZrep hZnorm).1
  have hcap_le : ∀ N : ℕ,
      (∫ x : ℝ, capWeight eta (N : ℝ) x * |raw x| ^ 2) ≤ B ^ 2 := by
    intro N
    obtain ⟨Z, hZrep, hZnorm⟩ := hcap N
    exact (capEnergy_of_wholeLineRealL2_rep hB Z hZrep hZnorm).2
  have hfull : Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) * |raw x| ^ 2) :=
    fullWeightedL2_integrable_of_uniform_cap
      (C := B ^ 2) heta hraw hcap_int hcap_le
  have hfull_le :
      (∫ x : ℝ, Real.exp (2 * eta * x) * |raw x| ^ 2) ≤ B ^ 2 :=
    le_of_tendsto (tentEnergy_mono_limit heta hraw hfull)
      (Eventually.of_forall hcap_le)
  constructor
  · refine hfull.congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [paper5WeightedPopulationX_eq_exp_mul_rawPopulationX]
    dsimp only [raw]
    rw [mul_pow, sq_abs]
    have hexp : Real.exp (2 * eta * x) = Real.exp (eta * x) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp]
  · calc
      (∫ x : ℝ,
          paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2) =
          ∫ x : ℝ, Real.exp (2 * eta * x) * |raw x| ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        rw [paper5WeightedPopulationX_eq_exp_mul_rawPopulationX]
        dsimp only [raw]
        rw [mul_pow, sq_abs]
        have hexp : Real.exp (2 * eta * x) =
            Real.exp (eta * x) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
        rw [hexp]
      _ ≤ B ^ 2 := hfull_le

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedPopulationX_data_of_uniform_rawDQ
