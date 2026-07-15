import ShenWork.Paper1.WholeLineWeightedRegularityMaximal
import ShenWork.Paper1.WholeLineWeightedRegularityMild

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-- A cap-`L²` bound uniform over the concrete BUC Picard iterates passes to
the canonical fixed point by pointwise convergence and Fatou.  No claim that
BUC convergence itself implies weighted `L²` convergence is used. -/
theorem exists_capWeighted_mildFixedPoint_differenceL2_of_picard_uniform
    (p : CMParams) {M T eta R c B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (W : WholeLineBUCTrajectory T) (z : Set.Icc (0 : ℝ) T)
    (hpicard_sq : ∀ n, Integrable (fun x : ℝ =>
      (capWeightSqrt eta R x *
        ((((wholeLineCauchyBUCMildMap p hM hT u₀)^[n]) W z).1
            (x + c * z.1) -
          (W z).1 (x + c * z.1))) ^ 2) volume)
    (hpicard_bound : ∀ n, (∫ x : ℝ,
      (capWeightSqrt eta R x *
        ((((wholeLineCauchyBUCMildMap p hM hT u₀)^[n]) W z).1
            (x + c * z.1) -
          (W z).1 (x + c * z.1))) ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1
              (x + c * z.1) -
            (W z).1 (x + c * z.1))) ∧
      ‖Z‖ ≤ B := by
  let Φ := wholeLineCauchyBUCMildMap p hM hT u₀
  let P := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let G : ℕ → ℝ → ℝ := fun n x =>
    capWeightSqrt eta R x *
      (((Φ^[n]) W z).1 (x + c * z.1) - (W z).1 (x + c * z.1))
  let f : ℝ → ℝ := fun x =>
    capWeightSqrt eta R x *
      ((P z).1 (x + c * z.1) - (W z).1 (x + c * z.1))
  have hG_meas : ∀ n, AEStronglyMeasurable (G n) volume := by
    intro n
    exact (((capWeightSqrt_continuous eta R).mul
      (((((Φ^[n]) W z).1.continuous.comp
          (continuous_id.add continuous_const)).sub
        ((W z).1.continuous.comp
          (continuous_id.add continuous_const)))))).aestronglyMeasurable
  have hconv : ∀ x, Tendsto (fun n => G n x) atTop (nhds (f x)) := by
    intro x
    have htraj : Tendsto (fun n => (Φ^[n]) W) atTop (nhds P) := by
      simpa only [Φ, P, wholeLineCauchyBUCMildFixedPoint] using
        (wholeLineCauchyBUCMildMap_contracting
          p hM hT u₀ hsmall).tendsto_iterate_fixedPoint W
    have hslice : Tendsto (fun n => ((Φ^[n]) W) z) atTop (nhds (P z)) :=
      (ContinuousEvalConst.continuous_eval_const z).continuousAt.tendsto.comp
        htraj
    have hpoint : Tendsto
        (fun n => (((Φ^[n]) W z).1 (x + c * z.1))) atTop
        (nhds ((P z).1 (x + c * z.1))) :=
      (wholeLineBUCEvalCLM
        (x + c * z.1)).continuous.continuousAt.tendsto.comp
        hslice
    exact (tendsto_const_nhds.mul
      (hpoint.sub tendsto_const_nhds))
  have hfatou := integrable_sq_of_pointwise_tendsto_of_uniform_integral_le
    hG_meas (by simpa only [G] using hpicard_sq)
      (by simpa only [G] using hpicard_bound) hconv
  have hf_meas : AEStronglyMeasurable f volume := by
    exact (((capWeightSqrt_continuous eta R).mul
      ((((P z).1.continuous.comp
          (continuous_id.add continuous_const)).sub
        ((W z).1.continuous.comp
          (continuous_id.add continuous_const)))))).aestronglyMeasurable
  let Z := wholeLineRealL2OfSqIntegrable f hf_meas hfatou.1
  refine ⟨Z, wholeLineRealL2OfSqIntegrable_coe_ae f hf_meas hfatou.1, ?_⟩
  have hnormsq : ‖Z‖ ^ 2 = ∫ x : ℝ, f x ^ 2 :=
    wholeLineRealL2OfSqIntegrable_norm_sq f hf_meas hfatou.1
  have hsq : ‖Z‖ ^ 2 ≤ B ^ 2 := hnormsq.le.trans hfatou.2
  dsimp only [f, P] at *
  nlinarith [norm_nonneg Z]

#print axioms exists_capWeighted_mildFixedPoint_differenceL2_of_picard_uniform

end ShenWork.Paper1
