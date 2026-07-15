import ShenWork.Paper1.WholeLineWeightedRegularityDQToDeriv
import ShenWork.Paper1.WholeLineWeightedRegularityH0Fatou

open Filter Topology MeasureTheory Real Set Function
open scoped RealInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-!
# Fatou passage from raw quotients to a genuine derivative

The spatial Henry estimate is uniform in the finite-difference step.  This
file packages the final fixed-cap passage to the pointwise derivative.  It
does not infer weighted convergence from BUC convergence: only pointwise
convergence and Fatou are used.
-/

/-- Uniform cap-`L²` representatives for a sequence of raw quotients pass to
the continuous pointwise limit with the same norm bound. -/
theorem exists_capWeighted_rawDQLimitL2_of_uniform_representatives
    {eta R B : ℝ} {w q : ℝ → ℝ} {step : ℕ → ℝ}
    (hB : 0 ≤ B) (hw : Continuous w) (hq : Continuous q)
    (hconv : ∀ x, Tendsto
      (fun n => rawSpatialDifferenceQuotient eta (step n) w x)
      atTop (𝓝 (q x)))
    (hrep : ∀ n, ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x => capWeightSqrt eta R x *
        rawSpatialDifferenceQuotient eta (step n) w x) ∧
      ‖Z‖ ≤ B) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x * q x) ∧
      ‖Z‖ ≤ B := by
  let G : ℕ → ℝ → ℝ := fun n x => capWeightSqrt eta R x *
    rawSpatialDifferenceQuotient eta (step n) w x
  let f : ℝ → ℝ := fun x => capWeightSqrt eta R x * q x
  have hraw_cont : ∀ n,
      Continuous (rawSpatialDifferenceQuotient eta (step n) w) := by
    intro n
    unfold rawSpatialDifferenceQuotient spatialDifferenceQuotient
    fun_prop
  have hG_meas : ∀ n, AEStronglyMeasurable (G n) volume := by
    intro n
    exact ((capWeightSqrt_continuous eta R).mul
      (hraw_cont n)).aestronglyMeasurable
  have hG_sq : ∀ n, Integrable (fun x : ℝ => G n x ^ 2) volume := by
    intro n
    obtain ⟨Z, hZrep, _hZnorm⟩ := hrep n
    have hZsq : Integrable (fun x : ℝ => Z x ^ 2) volume :=
      (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
    refine hZsq.congr ?_
    filter_upwards [hZrep] with x hx
    rw [hx]
  have hG_bound : ∀ n, (∫ x : ℝ, G n x ^ 2) ≤ B ^ 2 := by
    intro n
    obtain ⟨Z, hZrep, hZnorm⟩ := hrep n
    have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq
      Z Z hZrep hZrep
    rw [real_inner_self_eq_norm_sq] at hinner
    have hEq : (∫ x : ℝ, G n x ^ 2) = ‖Z‖ ^ 2 := by
      simpa only [G, pow_two] using hinner
    rw [hEq]
    exact (sq_le_sq₀ (norm_nonneg Z) hB).2 hZnorm
  have hGconv : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (f x)) := by
    intro x
    exact tendsto_const_nhds.mul (hconv x)
  have hfatou := integrable_sq_of_pointwise_tendsto_of_uniform_integral_le
    hG_meas hG_sq hG_bound hGconv
  have hf_meas : AEStronglyMeasurable f volume :=
    ((capWeightSqrt_continuous eta R).mul hq).aestronglyMeasurable
  let Z := wholeLineRealL2OfSqIntegrable f hf_meas hfatou.1
  refine ⟨Z, wholeLineRealL2OfSqIntegrable_coe_ae
    f hf_meas hfatou.1, ?_⟩
  have hnormsq : ‖Z‖ ^ 2 = ∫ x : ℝ, f x ^ 2 :=
    wholeLineRealL2OfSqIntegrable_norm_sq f hf_meas hfatou.1
  have hsq : ‖Z‖ ^ 2 ≤ B ^ 2 := hnormsq.le.trans hfatou.2
  dsimp only [f] at *
  exact (sq_le_sq₀ (norm_nonneg Z) hB).mp hsq

#print axioms exists_capWeighted_rawDQLimitL2_of_uniform_representatives

end ShenWork.Paper1
