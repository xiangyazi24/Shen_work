import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorIdentification

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Weighted second derivatives from the exact mild generator

The mild right derivative identifies the semigroup generator as an `L²`
representative of the classical conjugated spatial generator.  This directly
supplies the weighted `H²` data used by the whole-line energy calculation.
-/

/-- A genuine right derivative of the full exact-weight mild trajectory
produces all weighted diffusion data, in particular the `W * Wxx`
integrability input. -/
theorem paper5WeightedPopulation_diffusion_data_of_fullGenerator_rightDerivative
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {A F : WholeLineRealL2}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u t x - U x| ^ 2))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2))
    (hW_meas : ∀ n : ℕ, AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U
        (t + ((n + 1 : ℕ) : ℝ)⁻¹)) volume)
    (hW_sq : ∀ n : ℕ, Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U
        (t + ((n + 1 : ℕ) : ℝ)⁻¹) x ^ 2) volume)
    (hW0_meas : AEStronglyMeasurable
      (paper5WeightedPopulation eta (coMovingPath c u) U t) volume)
    (hW0_sq : Integrable (fun x : ℝ =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x ^ 2) volume)
    (hright : HasDerivWithinAt
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
      (A + F) (Set.Ici t) t)
    (hpoint : ∀ x, HasDerivAt
      (fun s => paper5WeightedPopulation eta (coMovingPath c u) U s x)
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t x) t)
    (hFrep : (((F : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t)) :
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
  have hArep :=
    paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative
      p hsol ht0 htT hTW hu (hu2.of_le (by norm_num)) hv2
        (hU2.of_le (by norm_num)) hV2 hW_meas hW_sq hW0_meas hW0_sq
        hright hpoint hFrep
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
  exact paper5WeightedPopulation_diffusion_data_of_spatialGenerator_sq
    hu2 hU2 hclose hWx2 hgenerator2

section AxiomAudit

#print axioms
  paper5WeightedPopulation_diffusion_data_of_fullGenerator_rightDerivative

end AxiomAudit

end ShenWork.Paper1
