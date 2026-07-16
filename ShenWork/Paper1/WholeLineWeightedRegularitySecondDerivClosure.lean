import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorClosure

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted second-derivative closure

This file packages the last algebraic step from an `L2` bound for the full
conjugated spatial generator to the diffusion data used by the weighted
Henry energy.  The generator input is kept concrete: it is exactly

`Wxx + (c - 2 * eta) * Wx + (eta ^ 2 - c * eta) * W`.

There is no use of a weighted derivative of the chemotaxis flux here.  In
particular, none of the declarations below consumes the desired weighted
first- or second-derivative conclusion through a hidden package field.
-/

/-- A square-integrable concrete conjugated generator, together with the
already-established value and first-derivative estimates, gives both the
weighted second derivative and the diffusion density `W * Wxx` in `L2` and
`L1`, respectively. -/
theorem paper5WeightedPopulationXX_and_diffusion_integrable_of_spatialGenerator_sq
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hgenerator2 : Integrable (fun x =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2)) :
    Integrable (fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x ^ 2) ∧
      Integrable (fun x =>
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) := by
  have hWxxMeas : AEStronglyMeasurable
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t) volume :=
    (paper5WeightedPopulationXX_continuous hu2 hU2).aestronglyMeasurable
  have hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x ^ 2) :=
    paper5WeightedPopulation_sq_integrable_of_weighted_difference hclose
  have hWxx2 : Integrable (fun x =>
      paper5WeightedPopulationXX eta (coMovingPath c u) U t x ^ 2) := by
    exact paper5WeightedPopulationXX_sq_integrable_of_generator
      (G := fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
          (c - 2 * eta) *
            paper5WeightedPopulationX eta (coMovingPath c u) U t x +
          (eta ^ 2 - c * eta) *
            paper5WeightedPopulation eta (coMovingPath c u) U t x)
      hWxxMeas (fun _ => rfl) hgenerator2 hW2 hWx2
  exact ⟨hWxx2,
    paper5WeightedPopulation_mul_XX_integrable_of_XX_sq
      hu2 hU2 hclose hWxx2⟩

/-- The companion product `Wx * Wxx` is integrable once both factors are
square integrable.  It is useful for later differentiated estimates, though
the diffusion term in the current Henry energy consumes `W * Wxx`. -/
theorem paper5WeightedPopulationX_mul_XX_integrable_of_XX_sq
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hWxx2 : Integrable (fun x =>
      paper5WeightedPopulationXX eta (coMovingPath c u) U t x ^ 2)) :
    Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x *
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x) := by
  have hWxCont : Continuous
      (paper5WeightedPopulationX eta (coMovingPath c u) U t) :=
    continuous_iff_continuousAt.mpr fun x =>
      (paper5WeightedPopulationX_space_hasDerivAt
        (η := eta) (t := t) (x := x)
        (u := coMovingPath c u) (U := U) hu2 hU2).continuousAt
  have hWxxCont : Continuous
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t) :=
    paper5WeightedPopulationXX_continuous hu2 hU2
  exact integrable_mul_of_sq_integrable_of_continuous
    hWxCont hWxxCont hWx2 hWxx2

/-- The natural `H2` reducer: square integrability of `W`, `Wx`, and `Wxx`
is enough to construct both mixed products and the exact diffusion pairing.
This statement contains no generator, semigroup, or source hypothesis. -/
theorem paper5WeightedPopulation_diffusion_data_of_square_integrability
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hWxx2 : Integrable (fun x =>
      paper5WeightedPopulationXX eta (coMovingPath c u) U t x ^ 2)) :
    Integrable (fun x =>
        paper5WeightedPopulationX eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) ∧
      Integrable (fun x =>
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) ∧
      (∫ x, paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) =
        -∫ x, paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2 := by
  have hWxWxx := paper5WeightedPopulationX_mul_XX_integrable_of_XX_sq
    hu2 hU2 hWx2 hWxx2
  have hWCont : Continuous
      (paper5WeightedPopulation eta (coMovingPath c u) U t) := by
    unfold paper5WeightedPopulation
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        (hu2.continuous.sub hU2.continuous)
  have hWxxCont : Continuous
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t) :=
    paper5WeightedPopulationXX_continuous hu2 hU2
  have hWWxx : Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x *
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x) :=
    integrable_mul_of_sq_integrable_of_continuous
      hWCont hWxxCont hW2 hWxx2
  obtain ⟨_hWxW, hdecayBot, hdecayTop, _hW2Bot, _hW2Top⟩ :=
    paper5WeightedPopulation_spatial_product_data
      hu2 hU2 hW2 hWx2 hWWxx
  have hgrad : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x *
        paper5WeightedPopulationX eta (coMovingPath c u) U t x) := by
    simpa only [pow_two] using hWx2
  have hibp := paper5WeightedPopulation_diffusion_ibp
    hu2 hU2 hWWxx hgrad hdecayBot hdecayTop
  exact ⟨hWxWxx, hWWxx, hibp⟩

/-- Complete diffusion data from a concrete conjugated-generator `L2`
estimate.  Besides the two product integrability statements, this records
the exact whole-line integration-by-parts identity consumed in the energy
calculation. -/
theorem paper5WeightedPopulation_diffusion_data_of_spatialGenerator_sq
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hgenerator2 : Integrable (fun x =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2)) :
    Integrable (fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x ^ 2) ∧
      Integrable (fun x =>
        paper5WeightedPopulationX eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) ∧
      Integrable (fun x =>
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) ∧
      (∫ x, paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) =
        -∫ x, paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2 := by
  obtain ⟨hWxx2, hWWxx⟩ :=
    paper5WeightedPopulationXX_and_diffusion_integrable_of_spatialGenerator_sq
      hu2 hU2 hclose hWx2 hgenerator2
  have hWxWxx := paper5WeightedPopulationX_mul_XX_integrable_of_XX_sq
    hu2 hU2 hWx2 hWxx2
  have hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x ^ 2) :=
    paper5WeightedPopulation_sq_integrable_of_weighted_difference hclose
  obtain ⟨_hWxW, hdecayBot, hdecayTop, _hW2Bot, _hW2Top⟩ :=
    paper5WeightedPopulation_spatial_product_data
      hu2 hU2 hW2 hWx2 hWWxx
  have hgrad : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x *
        paper5WeightedPopulationX eta (coMovingPath c u) U t x) := by
    simpa only [pow_two] using hWx2
  have hibp := paper5WeightedPopulation_diffusion_ibp
    hu2 hU2 hWWxx hgrad hdecayBot hdecayTop
  exact ⟨hWxx2, hWxWxx, hWWxx, hibp⟩

/-- Minimal regularization frontier for the second-derivative closure.
A family of scalar generator representatives with a uniform square-integral
bound and pointwise convergence supplies the concrete generator `L2` input
by Fatou; the preceding theorem then yields all diffusion data. -/
theorem paper5WeightedPopulation_diffusion_data_of_spatialGenerator_regularizations
    {eta c t C : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {G : ℕ → ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hGmeas : ∀ n, AEStronglyMeasurable (G n) volume)
    (hG2 : ∀ n, Integrable (fun x => G n x ^ 2) volume)
    (hGbound : ∀ n, (∫ x, G n x ^ 2) ≤ C)
    (hGconv : ∀ x, Tendsto (fun n => G n x) atTop
      (𝓝 (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x))) :
    Integrable (fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x ^ 2) ∧
      Integrable (fun x =>
        paper5WeightedPopulationX eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) ∧
      Integrable (fun x =>
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) ∧
      (∫ x, paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationXX eta (coMovingPath c u) U t x) =
        -∫ x, paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2 := by
  have hgenerator2 : Integrable (fun x =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2) :=
    (integrable_sq_of_pointwise_tendsto_of_uniform_integral_le
      hGmeas hG2 hGbound hGconv).1
  exact paper5WeightedPopulation_diffusion_data_of_spatialGenerator_sq
    hu2 hU2 hclose hWx2 hgenerator2

section AxiomAudit

#print axioms
  paper5WeightedPopulationXX_and_diffusion_integrable_of_spatialGenerator_sq
#print axioms paper5WeightedPopulationX_mul_XX_integrable_of_XX_sq
#print axioms
  paper5WeightedPopulation_diffusion_data_of_square_integrability
#print axioms paper5WeightedPopulation_diffusion_data_of_spatialGenerator_sq
#print axioms
  paper5WeightedPopulation_diffusion_data_of_spatialGenerator_regularizations

end AxiomAudit

end ShenWork.Paper1
