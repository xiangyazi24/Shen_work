import ShenWork.Paper1.WholeLineWeightedRegularityL2Semigroup
import ShenWork.Paper1.WholeLineWeightedRegularityH2
import ShenWork.Paper1.WholeLineWeightedRegularityMaximal
import ShenWork.Paper1.WholeLineWeightedRegularitySecondDeriv

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-! A concrete specialization of the endpoint-safe generator cancellation to
the weighted whole-line heat operators.  The source hypotheses are explicit:
the theorem is a wiring lemma, not an assumption package hidden in a field. -/

theorem weightedMovingHeatL2_generatorDuhamel_truncated_tendsto
    {eta c h t theta C H : ℝ}
    (htheta : 0 < theta) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    {eps : ℕ → ℝ}
    (heps_pos : ∀ n, 0 < eps n)
    (hepsh : ∀ n, eps n ≤ h)
    (heps : Tendsto eps atTop (𝓝 0))
    {F : ℝ → WholeLineRealL2}
    (hA : ∀ r ∈ Ioc (0 : ℝ) h,
      ‖weightedMovingHeatL2Generator eta c r‖ ≤ C * r ^ (-(1 : ℝ)))
    (hF : ∀ r ∈ Icc (0 : ℝ) h,
      ‖F (t - r) - F t‖ ≤ H * r ^ theta)
    (hmeas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r
        (F (t - r) - F t))
      (volume.restrict (uIoc (0 : ℝ) h)))
    (hfull : ∀ n, IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r (F (t - r)))
      volume (eps n) h)
    (hconst : ∀ n, IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r (F t))
      volume (eps n) h)
    (horbit : ∀ n, ∀ r ∈ Icc (eps n) h,
      HasDerivAt
        (fun q => weightedMovingHeatL2Semigroup eta c q (F t))
        (weightedMovingHeatL2Generator eta c r (F t)) r)
    (hSzero : Tendsto
      (fun n => weightedMovingHeatL2Semigroup eta c (eps n) (F t))
      atTop (𝓝 (F t))) :
    Tendsto
      (fun n => ∫ r in eps n..h,
        weightedMovingHeatL2Generator eta c r (F (t - r)))
      atTop
      (𝓝 ((∫ r in (0 : ℝ)..h,
        weightedMovingHeatL2Generator eta c r
          (F (t - r) - F t)) +
        (weightedMovingHeatL2Semigroup eta c h - 1) (F t))) := by
  have hrem : IntervalIntegrable
      (fun r => weightedMovingHeatL2Generator eta c r
        (F (t - r) - F t)) volume 0 h := by
    exact intervalIntegrable_generator_holder_remainder
      htheta hh hC hH hA hF hmeas
  exact tendsto_truncated_generator_duhamel_integral
    hh heps_pos hepsh heps hrem hfull hconst horbit hSzero

theorem weightedMovingHeatL2_generatorDuhamel_limit_norm_le
    {eta c h t theta C H : ℝ}
    (htheta : 0 < theta) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    {F : ℝ → WholeLineRealL2}
    (hA : ∀ r ∈ Ioc (0 : ℝ) h,
      ‖weightedMovingHeatL2Generator eta c r‖ ≤ C * r ^ (-(1 : ℝ)))
    (hF : ∀ r ∈ Icc (0 : ℝ) h,
      ‖F (t - r) - F t‖ ≤ H * r ^ theta)
    (hmeas : AEStronglyMeasurable
      (fun r => weightedMovingHeatL2Generator eta c r
        (F (t - r) - F t))
      (volume.restrict (uIoc (0 : ℝ) h))) :
    ‖(∫ r in (0 : ℝ)..h,
        weightedMovingHeatL2Generator eta c r
          (F (t - r) - F t)) +
        (weightedMovingHeatL2Semigroup eta c h - 1) (F t)‖ ≤
      C * H * (h ^ theta / theta) +
        ‖(weightedMovingHeatL2Semigroup eta c h - 1) (F t)‖ := by
  have hrem := intervalIntegrable_generator_holder_remainder
    htheta hh hC hH hA hF hmeas
  have hremNorm := intervalIntegral_generator_holder_remainder_norm_le
    htheta hh hC hH hA hF hrem
  exact (norm_add_le _ _).trans (add_le_add hremNorm le_rfl)

/-- The final algebraic H² step for a weighted perturbation slice.  Once the
full conjugated generator has been put in L² by the preceding Duhamel
estimate, this turns the classical generator decomposition into the genuine
weighted second-derivative integrability consumed by the Henry energy. -/
theorem paper5WeightedPopulationXX_sq_integrable_of_generator
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {G : ℝ → ℝ}
    (hWxx_meas : AEStronglyMeasurable
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t) volume)
    (hdecomp : ∀ x, G x =
      paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x)
    (hG2 : Integrable (fun x => G x ^ 2) volume)
    (hW2 : Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x ^ 2) volume)
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2) volume) :
    Integrable (fun x =>
      paper5WeightedPopulationXX eta (coMovingPath c u) U t x ^ 2) volume := by
  exact secondDerivative_sq_integrable_of_generator_decomposition
    (Wxx := paper5WeightedPopulationXX eta (coMovingPath c u) U t)
    (W := paper5WeightedPopulation eta (coMovingPath c u) U t)
    (Wx := paper5WeightedPopulationX eta (coMovingPath c u) U t)
    hWxx_meas hdecomp hG2 hW2 hWx2

theorem paper5WeightedPopulation_mul_XX_integrable_of_generator
    {eta c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {G : ℝ → ℝ}
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hU2 : ContDiff ℝ 2 U)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u t x - U x| ^ 2))
    (hWxx_meas : AEStronglyMeasurable
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t) volume)
    (hdecomp : ∀ x, G x =
      paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x)
    (hG2 : Integrable (fun x => G x ^ 2) volume)
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2) volume) :
    Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x *
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x) := by
  have hWxx2 := paper5WeightedPopulationXX_sq_integrable_of_generator
    hWxx_meas hdecomp hG2
    (paper5WeightedPopulation_sq_integrable_of_weighted_difference hclose)
    hWx2
  exact paper5WeightedPopulation_mul_XX_integrable_of_XX_sq
    hu2 hU2 hclose hWxx2

section AxiomAudit

#print axioms weightedMovingHeatL2_generatorDuhamel_truncated_tendsto
#print axioms weightedMovingHeatL2_generatorDuhamel_limit_norm_le
#print axioms paper5WeightedPopulationXX_sq_integrable_of_generator
#print axioms paper5WeightedPopulation_mul_XX_integrable_of_generator

end AxiomAudit

end ShenWork.Paper1
