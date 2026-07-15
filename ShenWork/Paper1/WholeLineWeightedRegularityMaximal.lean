import ShenWork.Paper1.WholeLineWeightedRegularityForcingHolder
import ShenWork.Paper1.WholeLineWeightedRegularityH2

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Maximal weighted regularity on the whole line

The concrete parabolic argument first bounds a positive-time Gaussian
regularization of the weighted spatial generator uniformly in `L2`.  The
solution slice is already classically `C2`, so the regularized generators
converge pointwise to its classical generator.  This file starts with the
Fatou closure that turns exactly those two facts into square integrability of
the genuine pointwise limit.
-/

/-- Pointwise convergence together with a uniform square-integral bound
puts the limit in `L2`.  This is the endpoint-safe Fatou step used after the
generator cancellation; no dominating function is assumed. -/
theorem integrable_sq_of_pointwise_tendsto_of_uniform_integral_le
    {G : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hG_meas : ∀ n, AEStronglyMeasurable (G n) volume)
    (hG_sq : ∀ n, Integrable (fun x : ℝ => (G n x) ^ 2) volume)
    (hbound : ∀ n, (∫ x : ℝ, (G n x) ^ 2) ≤ C)
    (hconv : ∀ x, Tendsto (fun n => G n x) atTop (nhds (f x))) :
    Integrable (fun x : ℝ => (f x) ^ 2) volume ∧
      (∫ x : ℝ, (f x) ^ 2) ≤ C := by
  let H : ℕ → ℝ → ℝ := fun n x => (G n x) ^ 2
  let F : ℝ → ℝ := fun x => (f x) ^ 2
  have hHF : ∀ᵐ x ∂volume, Tendsto (fun n => H n x) atTop (nhds (F x)) := by
    filter_upwards with x
    exact (continuous_pow 2).continuousAt.tendsto.comp (hconv x)
  have hHmeas : ∀ n, AEStronglyMeasurable (H n) volume := by
    intro n
    exact (hG_meas n).pow 2
  have hlintegral_le : ∀ n,
      (∫⁻ x : ℝ, ‖H n x‖ₑ ∂volume) ≤ ENNReal.ofReal C := by
    intro n
    have hnonneg : ∀ x : ℝ, 0 ≤ H n x := fun x => sq_nonneg _
    calc
      (∫⁻ x : ℝ, ‖H n x‖ₑ ∂volume) =
          ∫⁻ x : ℝ, ENNReal.ofReal (H n x) ∂volume := by
        apply lintegral_congr
        intro x
        exact Real.enorm_of_nonneg (hnonneg x)
      _ = ENNReal.ofReal (∫ x : ℝ, H n x) :=
        (ofReal_integral_eq_lintegral_ofReal (by
          simpa only [H] using hG_sq n)
          (Eventually.of_forall hnonneg)).symm
      _ ≤ ENNReal.ofReal C := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [H] using hbound n
  have hliminf_le :
      liminf (fun n => ∫⁻ x : ℝ, ‖H n x‖ₑ ∂volume) atTop ≤
        ENNReal.ofReal C :=
    liminf_le_of_frequently_le' (Frequently.of_forall hlintegral_le)
  have hliminf_ne :
      liminf (fun n => ∫⁻ x : ℝ, ‖H n x‖ₑ ∂volume) atTop ≠ ⊤ :=
    (lt_of_le_of_lt hliminf_le ENNReal.ofReal_lt_top).ne
  have hFint : Integrable F volume :=
    MeasureTheory.integrable_of_tendsto hHF hHmeas hliminf_ne
  refine ⟨by simpa only [F] using hFint, ?_⟩
  have hfatou :
      (∫⁻ x : ℝ, ‖F x‖ₑ ∂volume) ≤
        liminf (fun n => ∫⁻ x : ℝ, ‖H n x‖ₑ ∂volume) atTop :=
    lintegral_enorm_le_liminf_of_tendsto hHF
      (fun n => (hHmeas n).aemeasurable.enorm)
  have hlintegralF_le :
      (∫⁻ x : ℝ, ‖F x‖ₑ ∂volume) ≤ ENNReal.ofReal C :=
    hfatou.trans hliminf_le
  have hF_nonneg : ∀ x : ℝ, 0 ≤ F x := fun x => sq_nonneg _
  have hlintegralF_eq :
      (∫⁻ x : ℝ, ‖F x‖ₑ ∂volume) =
        ENNReal.ofReal (∫ x : ℝ, F x) := by
    calc
      (∫⁻ x : ℝ, ‖F x‖ₑ ∂volume) =
          ∫⁻ x : ℝ, ENNReal.ofReal (F x) ∂volume := by
        apply lintegral_congr
        intro x
        exact Real.enorm_of_nonneg (hF_nonneg x)
      _ = ENNReal.ofReal (∫ x : ℝ, F x) :=
        (ofReal_integral_eq_lintegral_ofReal hFint
          (Eventually.of_forall hF_nonneg)).symm
  have hC : 0 ≤ C := by
    have hzero : 0 ≤ ∫ x : ℝ, (G 0 x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    exact hzero.trans (hbound 0)
  rw [hlintegralF_eq, ENNReal.ofReal_le_ofReal_iff hC] at hlintegralF_le
  simpa only [F] using hlintegralF_le

/-- Three-term square estimate used to recover the classical Hessian from
the full constant-coefficient generator. -/
theorem sub_sub_sq_le_three_sum_sq (a b c : ℝ) :
    (a - b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - (-b)), sq_nonneg (a - (-c)),
    sq_nonneg ((-b) - (-c))]

/-- If the full moving/conjugated generator is in `L2`, and the value and
first derivative are in `L2`, then the genuine classical second derivative
is in `L2`.  The decomposition is explicit so this result is independent of
how the generator bound was obtained. -/
theorem secondDerivative_sq_integrable_of_generator_decomposition
    {d lambda : ℝ} {G W Wx Wxx : ℝ → ℝ}
    (hWxx_meas : AEStronglyMeasurable Wxx volume)
    (hdecomp : ∀ x, G x = Wxx x + d * Wx x + lambda * W x)
    (hG2 : Integrable (fun x : ℝ => G x ^ 2) volume)
    (hW2 : Integrable (fun x : ℝ => W x ^ 2) volume)
    (hWx2 : Integrable (fun x : ℝ => Wx x ^ 2) volume) :
    Integrable (fun x : ℝ => Wxx x ^ 2) volume := by
  let major : ℝ → ℝ := fun x =>
    3 * (G x ^ 2 + (d * Wx x) ^ 2 + (lambda * W x) ^ 2)
  have hdWx : Integrable (fun x : ℝ => (d * Wx x) ^ 2) volume := by
    simpa only [mul_pow] using hWx2.const_mul (d ^ 2)
  have hlW : Integrable (fun x : ℝ => (lambda * W x) ^ 2) volume := by
    simpa only [mul_pow] using hW2.const_mul (lambda ^ 2)
  have hmajor : Integrable major volume := by
    exact ((hG2.add hdWx).add hlW).const_mul 3
  refine hmajor.mono' (hWxx_meas.pow 2) ?_
  filter_upwards with x
  have hpoint := sub_sub_sq_le_three_sum_sq
    (G x) (d * Wx x) (lambda * W x)
  have hWxx : Wxx x = G x - d * Wx x - lambda * W x := by
    rw [hdecomp x]
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hWxx]
  simpa only [major] using hpoint

section AxiomAudit

#print axioms integrable_sq_of_pointwise_tendsto_of_uniform_integral_le
#print axioms sub_sub_sq_le_three_sum_sq
#print axioms secondDerivative_sq_integrable_of_generator_decomposition

end AxiomAudit

end ShenWork.Paper1
