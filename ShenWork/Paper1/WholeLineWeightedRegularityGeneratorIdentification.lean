import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorDomainNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorPairing
import ShenWork.Paper1.WholeLineWeightedRegularityForcingL2Trajectory

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Identifying the exact weighted generator

The right Hilbert derivative of the full mild trajectory is the sum of its
semigroup generator and the nonlinear forcing.  The independently available
classical pointwise PDE therefore identifies the semigroup-generator summand
almost everywhere with the conjugated spatial generator.
-/

/-- Subtract an `L²` forcing representative from the total material
derivative and use the pointwise PDE to identify the remaining summand. -/
theorem wholeLineRealL2_spatialGenerator_coe_ae_of_total_and_forcing
    {A F : WholeLineRealL2} {Wt G Q : ℝ → ℝ}
    (htotal : ((((A + F : WholeLineRealL2) : ℝ → ℝ)) =ᵐ[volume] Wt))
    (hforcing : (((F : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] Q))
    (hpde : ∀ x, Wt x = G x + Q x) :
    (((A : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume] G) := by
  filter_upwards [Lp.coeFn_add A F, htotal, hforcing] with x hadd htot hF
  rw [hadd] at htot
  simp only [Pi.add_apply] at htot
  rw [hF, hpde x] at htot
  linarith

/-- Classical specialization: a right derivative of the canonical exact-
weight state identifies the semigroup-generator summand with the full
conjugated spatial generator.  The positive sequence used for the a.e.
identification is chosen internally. -/
theorem paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {A F : WholeLineRealL2}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V)
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
    (((A : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x =>
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
          (c - 2 * eta) *
            paper5WeightedPopulationX eta (coMovingPath c u) U t x +
          (eta ^ 2 - c * eta) *
            paper5WeightedPopulation eta (coMovingPath c u) U t x) := by
  have htotal : ((((A + F : WholeLineRealL2) : ℝ → ℝ)) =ᵐ[volume]
      paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) :=
    wholeLineRealL2Total_hasDerivWithinAt_coe_ae_of_pointwise
      hW_meas hW_sq hW0_meas hW0_sq hright hpoint
  apply wholeLineRealL2_spatialGenerator_coe_ae_of_total_and_forcing
    htotal hFrep
  intro x
  exact paper5WeightedPopulationT_eq_spatialGenerator_add_generatorForcing
    p hsol ht0 htT hTW (hu x) hu1 hv2 hU1 hV2

section AxiomAudit

#print axioms wholeLineRealL2_spatialGenerator_coe_ae_of_total_and_forcing
#print axioms
  paper5WeightedFullGenerator_coe_ae_spatialGenerator_of_rightDerivative

end AxiomAudit

end ShenWork.Paper1
