import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Within-set differentiation under an integral

This file supplies the one-sided/within-set analogue needed at a closed time endpoint.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace ShenWork.HasDerivWithinAtIntegral

private lemma integrable_of_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set ℝ} (hs : Convex ℝ s)
    {F : α → ℝ → ℝ} {F' : α → ℝ} {a₀ a : ℝ} (ha₀ : a₀ ∈ s) (ha : a ∈ s)
    {bound : α → ℝ}
    (hF_meas : ∀ a ∈ s, AEStronglyMeasurable (fun x => F x a) μ)
    (hF_int : Integrable (fun x => F x a₀) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ a ∈ s, |F' x| ≤ bound x)
    (bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ a ∈ s,
      HasDerivWithinAt (fun a => F x a) (F' x) s a) :
    Integrable (fun x => F x a) μ := by
  have hdiff_bound :
      ∀ᵐ x ∂μ, ‖F x a₀ - F x a‖ ≤ ‖a - a₀‖ * |bound x| := by
    filter_upwards [h_diff, h_bound] with x hx_diff hx_bound
    have hmvt :
        ‖F x a - F x a₀‖ ≤ |bound x| * ‖a - a₀‖ := by
      refine hs.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun b => F x b) (f' := fun _ => F' x) (C := |bound x|)
        hx_diff (fun b hb => ?_) ha₀ ha
      have hle : |F' x| ≤ |bound x| := (hx_bound b hb).trans (le_abs_self _)
      simpa [Real.norm_eq_abs] using hle
    simpa [norm_sub_rev, mul_comm] using hmvt
  exact integrable_of_norm_sub_le (hF_meas a ha) hF_int
    (bound_int.norm.const_mul ‖a - a₀‖) hdiff_bound

/-- Differentiation under an integral along a convex parameter set.

This is a within-set analogue of Mathlib's
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le` for real-valued
integrands, with the same dominated-derivative hypothesis but with
`HasDerivWithinAt` on a convex set replacing two-sided differentiability on a
neighborhood. -/
theorem hasDerivWithinAt_integral_of_dominated_loc
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set ℝ} (hs : Convex ℝ s)
    {F : α → ℝ → ℝ} {F' : α → ℝ} {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    {bound : α → ℝ}
    (hF_meas : ∀ a ∈ s, AEStronglyMeasurable (fun x => F x a) μ)
    (hF_int : Integrable (fun x => F x a₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ a ∈ s, |F' x| ≤ bound x)
    (bound_int : Integrable bound μ)
    (h_diff : ∀ᵐ x ∂μ, ∀ a ∈ s,
      HasDerivWithinAt (fun a => F x a) (F' x) s a) :
    HasDerivWithinAt (fun a => ∫ x, F x a ∂μ) (∫ x, F' x ∂μ) s a₀ := by
  have hF'_int : Integrable F' μ := by
    refine bound_int.mono' hF'_meas ?_
    exact h_bound.mono fun x hx => by
      simpa [Real.norm_eq_abs] using hx a₀ ha₀
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have h_integral_slope :
      (fun a => slope (fun b => ∫ x, F x b ∂μ) a₀ a)
        =ᶠ[𝓝[s \ {a₀}] a₀]
      fun a => ∫ x, slope (fun b => F x b) a₀ a ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha_s : a ∈ s := ha.1
    have ha_ne : a ≠ a₀ := by simpa using ha.2
    have hFa : Integrable (fun x => F x a) μ :=
      integrable_of_mem hs ha₀ ha_s hF_meas hF_int h_bound bound_int h_diff
    rw [slope_def_module]
    calc
      (a - a₀)⁻¹ • (∫ x, F x a ∂μ - ∫ x, F x a₀ ∂μ)
          = (a - a₀)⁻¹ • ∫ x, F x a - F x a₀ ∂μ := by
            rw [integral_sub hFa hF_int]
      _ = ∫ x, (a - a₀)⁻¹ • (F x a - F x a₀) ∂μ := by
            rw [integral_smul]
      _ = ∫ x, slope (fun b => F x b) a₀ a ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with x
            rw [slope_def_module]
  refine Tendsto.congr' h_integral_slope.symm ?_
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun x => |bound x|)
  · filter_upwards [self_mem_nhdsWithin] with a ha
    simpa [slope_def_module] using
      (((hF_meas a ha.1).sub (hF_meas a₀ ha₀)).const_smul ((a - a₀)⁻¹ : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    have ha_s : a ∈ s := ha.1
    have ha_ne : a ≠ a₀ := by simpa using ha.2
    filter_upwards [h_diff, h_bound] with x hx_diff hx_bound
    have hmvt :
        ‖F x a - F x a₀‖ ≤ |bound x| * ‖a - a₀‖ := by
      refine hs.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun b => F x b) (f' := fun _ => F' x) (C := |bound x|)
        hx_diff (fun b hb => ?_) ha₀ ha_s
      have hle : |F' x| ≤ |bound x| := (hx_bound b hb).trans (le_abs_self _)
      simpa [Real.norm_eq_abs] using hle
    have hpos : 0 < ‖a - a₀‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr ha_ne
    have hapos : 0 < |a - a₀| := by
      exact abs_pos.mpr (sub_ne_zero.mpr ha_ne)
    rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
      inv_mul_le_iff₀ hapos]
    simpa [Real.norm_eq_abs, mul_comm] using hmvt
  · exact bound_int.norm
  · exact h_diff.mono fun x hx => hasDerivWithinAt_iff_tendsto_slope.mp (hx a₀ ha₀)

end ShenWork.HasDerivWithinAtIntegral
