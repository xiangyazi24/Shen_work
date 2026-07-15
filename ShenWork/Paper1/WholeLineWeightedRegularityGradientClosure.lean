import ShenWork.Paper1.WholeLineWeightedRegularityGradient
import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import ShenWork.Paper1.WholeLineWeightedRegularityCap

open Filter MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Closing the raw-cap first-derivative estimate

The tent exhaustion in `WholeLineWeightedRegularityGradient` acts on the raw
derivative bracket.  This file converts uniformly bounded `L²`
representatives of the correctly cap-conjugated raw bracket into the genuine
exponentially weighted first-derivative integrability statement.
-/

/-- Uniformly bounded `L²` representatives of the cap-conjugated raw spatial
derivative produce the genuine exponentially weighted `hWx2`.  The cap is
applied before exponential exhaustion, so the exponential weight is inserted
exactly once. -/
theorem paper5WeightedPopulationX_sq_integrable_of_uniform_cap_representatives
    {eta B c t : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    (heta : 0 < eta) (hB : 0 ≤ B)
    (hraw_cont : Continuous
      (paper5RawPopulationX eta (coMovingPath c u) U t))
    (hrep : ∀ n : ℕ, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta (n : ℝ) x *
          paper5RawPopulationX eta (coMovingPath c u) U t x) ∧
      ‖Z‖ ≤ B) :
    Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)
      volume := by
  refine paper5WeightedPopulationX_sq_integrable_of_uniform_raw_cap
    (eta := eta) (C := B ^ 2) (t := t)
    (u := coMovingPath c u) (U := U)
    heta hraw_cont ?_ ?_
  · intro n
    obtain ⟨Z, hZrep, _hZnorm⟩ := hrep n
    have hZsq : Integrable (fun x : ℝ => Z x ^ 2) volume :=
      (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
    refine hZsq.congr ?_
    filter_upwards [hZrep] with x hx
    rw [hx, capWeightSqrt_mul_sq_eq]
  · intro n
    obtain ⟨Z, hZrep, hZnorm⟩ := hrep n
    have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq
      Z Z hZrep hZrep
    rw [real_inner_self_eq_norm_sq] at hinner
    have hnorm :
        (∫ x : ℝ, capWeight eta (n : ℝ) x *
          |paper5RawPopulationX eta (coMovingPath c u) U t x| ^ 2) =
          ‖Z‖ ^ 2 := by
      calc
        (∫ x : ℝ, capWeight eta (n : ℝ) x *
            |paper5RawPopulationX eta (coMovingPath c u) U t x| ^ 2) =
            ∫ x : ℝ,
              (capWeightSqrt eta (n : ℝ) x *
                paper5RawPopulationX eta (coMovingPath c u) U t x) *
              (capWeightSqrt eta (n : ℝ) x *
                paper5RawPopulationX eta (coMovingPath c u) U t x) := by
          apply integral_congr_ae
          filter_upwards with x
          simpa only [pow_two] using
            (capWeightSqrt_mul_sq_eq eta (n : ℝ) x
              (paper5RawPopulationX eta (coMovingPath c u) U t x)).symm
        _ = ‖Z‖ ^ 2 := hinner
    rw [hnorm]
    exact (sq_le_sq₀ (norm_nonneg Z) hB).2 hZnorm

/-- The cap-conjugated raw derivative bracket is the sum of the three
cap-conjugated derivative legs exposed by the differentiated mild formula. -/
theorem capWeightedRawPopulationX_eq_three_legs_of_hasDerivAt
    {eta R c t x : ℝ} {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ}
    {qRef q₀ qG qR : ℝ}
    (hu : HasDerivAt (coMovingPath c u t)
      (q₀ + qG + qR -
        eta * (coMovingPath c u t x - U x) + qRef) x)
    (hU : HasDerivAt U qRef x) :
    capWeightSqrt eta R x *
        paper5RawPopulationX eta (coMovingPath c u) U t x =
      capWeightSqrt eta R x * q₀ +
      capWeightSqrt eta R x * qG +
      capWeightSqrt eta R x * qR := by
  unfold paper5RawPopulationX
  rw [hu.deriv, hU.deriv]
  ring

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedPopulationX_sq_integrable_of_uniform_cap_representatives
#print axioms
  ShenWork.Paper1.capWeightedRawPopulationX_eq_three_legs_of_hasDerivAt
