import ShenWork.Paper1.WholeLineWeightedRegularitySecondDerivGenerator

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted diffusion data from an explicit generator representative

The analytic endpoint argument first produces an `L²` representative of the
full conjugated spatial generator.  Once that representative is available,
all weighted second-derivative pairings follow without repeating the time
derivative identification.
-/

/-- An `L²` representative of the conjugated spatial generator supplies the
`W * Wxx` integrability input used by the weighted energy identity. -/
theorem paper5WeightedPopulation_mul_second_integrable_of_generator_representation
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {A : WholeLineRealL2}
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hArep : (((A : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
          (c - 2 * eta) *
            paper5WeightedPopulationX eta (coMovingPath c u) U t x +
          (eta ^ 2 - c * eta) *
            paper5WeightedPopulation eta (coMovingPath c u) U t x)) :
    Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x *
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x) := by
  have hA2 : Integrable (fun x : ℝ => ((A : WholeLineRealL2) x) ^ 2)
      volume :=
    (memLp_two_iff_integrable_sq (Lp.memLp A).1).1 (Lp.memLp A)
  have hgenerator2 : Integrable (fun x =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2) := by
    apply hA2.congr
    filter_upwards [hArep] with x hx
    rw [hx]
  exact (paper5WeightedPopulation_diffusion_data_of_spatialGenerator_sq
    hu2 hU2 hclose hWx2 hgenerator2).2.2.1

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedPopulation_mul_second_integrable_of_generator_representation
