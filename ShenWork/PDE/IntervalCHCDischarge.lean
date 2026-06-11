import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.PDE.IntervalCoupledClassicalBallEstimates

open MeasureTheory
open ShenWork.Paper2
open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.IntervalResolverLaplacianBridge
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalCoupledClassicalBallEstimates

noncomputable section

namespace ShenWork.IntervalCHCDischarge

/-!  Lane CHC discharge module.

This file records the non-circular pieces currently available for the
`χ₀ < 0` coupled-flux local-existence frontier.
-/

/-- Unit-interval helper-semigroup `L∞ → L∞` heat-gradient estimate with the
standard `t^{-1/2}` parabolic smoothing rate. -/
theorem intervalCoupledDuhamel_heatGradient_Linfty_unit
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure 1))
    (hf : ∀ y : ℝ, |f y| ≤ 1) (x : ℝ) :
    |deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x| ≤
      heatGradientLinftyLinftyConstant / Real.sqrt t := by
  exact intervalSemigroupOperator_deriv_Linfty_pointwise_sqrt_t_unit
    ht hf_int hf x

/-- Same heat-gradient estimate with any larger declared constant. -/
theorem intervalCoupledDuhamel_heatGradient_Linfty_unit_of_constant
    {Cgrad t : ℝ} (hCgrad : heatGradientLinftyLinftyConstant ≤ Cgrad)
    (ht : 0 < t)
    {f : ℝ → ℝ} (hf_int : Integrable f (intervalMeasure 1))
    (hf : ∀ y : ℝ, |f y| ≤ 1) (x : ℝ) :
    |deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x| ≤
      Cgrad / Real.sqrt t := by
  have hbase :=
    intervalCoupledDuhamel_heatGradient_Linfty_unit ht hf_int hf x
  have hsqrt_nonneg : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  exact hbase.trans (div_le_div_of_nonneg_right hCgrad hsqrt_nonneg)

/-- Existence form of the heat-gradient constant consumed by the C¹-ball
Duhamel source estimate. -/
theorem intervalCoupledDuhamel_grad_estimate_gap_discharged :
    ∃ Cgrad : ℝ, 0 ≤ Cgrad ∧
      ∀ {t : ℝ}, 0 < t →
        ∀ {f : ℝ → ℝ}, Integrable f (intervalMeasure 1) →
          (∀ y : ℝ, |f y| ≤ 1) →
            ∀ x : ℝ,
              |deriv (fun z : ℝ => intervalSemigroupOperator 1 t f z) x| ≤
                Cgrad / Real.sqrt t := by
  refine ⟨heatGradientLinftyLinftyConstant,
    heatGradientLinftyLinftyConstant_nonneg, ?_⟩
  intro t ht f hf_int hf x
  exact intervalCoupledDuhamel_heatGradient_Linfty_unit ht hf_int hf x

/-- C¹-interior resolver specialization of the chemotaxis-divergence Lipschitz
estimate.

This is the strongest currently formalized pointwise result relevant to
`hresolverFluxC1Lipschitz`: on a classical C¹ snapshot ball, and away from the
endpoints, the concrete Neumann resolver satisfies the product-rule
chemotaxis-divergence bound once the value, gradient, and Laplacian resolver
Lipschitz controls are supplied. -/
theorem intervalNeumannResolverR_chemotaxisDiv_C1_interior_lipschitz
    {p : CM2Params} {T M G_u G H L_V L_R L_H : ℝ}
    (hMnn : 0 ≤ M) (hGunn : 0 ≤ G_u)
    (hGnn : 0 ≤ G) (hHnn : 0 ≤ H)
    (hLVnn : 0 ≤ L_V) (hLRnn : 0 ≤ L_R) (hLHnn : 0 ≤ L_H)
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsnap₁ : IntervalDomainClassicalC1Snapshot p T M G_u u₁ v₁)
    (hsnap₂ : IntervalDomainClassicalC1Snapshot p T M G_u u₂ v₂)
    (hvR₁ : ∀ τ : ℝ, v₁ τ = intervalNeumannResolverR p (u₁ τ))
    (hvR₂ : ∀ τ : ℝ, v₂ τ = intervalNeumannResolverR p (u₂ τ))
    {D D_g : ℝ} (hDnn : 0 ≤ D) (hDgnn : 0 ≤ D_g)
    (hG₁ : ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |resolverGradReal p (u₁ τ) x| ≤ G)
    (hG₂ : ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |resolverGradReal p (u₂ τ) x| ≤ G)
    (hH₁ : ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
        |intervalNeumannResolverRLap p (u₁ τ) y| ≤ H)
    (hH₂ : ∀ τ : ℝ, τ ∈ Set.Ioo (0 : ℝ) T →
      ∀ y : intervalDomainPoint, y.1 ∈ Set.Icc (0 : ℝ) 1 →
        |intervalNeumannResolverRLap p (u₂ τ) y| ≤ H)
    (hu_diff : ∀ τ x, τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift (u₁ τ) x - intervalDomainLift (u₂ τ) x| ≤ D)
    (hdu_diff : ∀ τ x, τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
      |deriv (intervalDomainLift (u₁ τ)) x -
        deriv (intervalDomainLift (u₂ τ)) x| ≤ D_g)
    (hv_diff : ∀ τ x, τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
      |intervalDomainLift (v₁ τ) x - intervalDomainLift (v₂ τ) x| ≤ L_V * D)
    (hg_diff : ∀ τ x, τ ∈ Set.Ioo (0 : ℝ) T → x ∈ Set.Icc (0 : ℝ) 1 →
      |resolverGradReal p (u₁ τ) x -
        resolverGradReal p (u₂ τ) x| ≤ L_R * D)
    (hH_diff : ∀ τ (y : intervalDomainPoint), τ ∈ Set.Ioo (0 : ℝ) T →
      y.1 ∈ Set.Icc (0 : ℝ) 1 →
        |intervalNeumannResolverRLap p (u₁ τ) y -
          intervalNeumannResolverRLap p (u₂ τ) y| ≤ L_H * D) :
    ∀ τ (y : intervalDomainPoint), τ ∈ Set.Ioo (0 : ℝ) T →
      y.1 ∈ Set.Ioo (0 : ℝ) 1 →
      |intervalDomainChemotaxisDiv p (u₁ τ) (intervalNeumannResolverR p (u₁ τ)) y -
        intervalDomainChemotaxisDiv p (u₂ τ) (intervalNeumannResolverR p (u₂ τ)) y|
        ≤ ((H + p.β * G ^ 2)
              + (G_u + 2 * p.β * M * G) * L_R
              + M * L_H
              + (G_u * G + M * H) * p.β * L_V
              + p.β * (M * G ^ 2) * (p.β + 1) * L_V) * D
          + G * D_g := by
  intro τ y hτ hy
  have hbase :=
    intervalDomainChemotaxisDiv_classical_K_D_form_interior_uniformG
      hsnap₁ hsnap₂ hMnn hGunn hτ hGnn hHnn
      (fun x hx => hG₁ τ hτ x hx)
      (fun x hx => hG₂ τ hτ x hx)
      (fun z hz => hH₁ τ hτ z hz)
      (fun z hz => hH₂ τ hτ z hz)
      hDnn hDgnn hLVnn hLRnn hLHnn
      (fun x hx => hu_diff τ x hτ hx)
      (fun x hx => hdu_diff τ x hτ hx)
      (fun x hx => hv_diff τ x hτ hx)
      (fun x hx => hg_diff τ x hτ hx)
      (fun z hz => hH_diff τ z hτ hz)
      y hy
  simpa [hvR₁ τ, hvR₂ τ] using hbase

#print axioms intervalCoupledDuhamel_heatGradient_Linfty_unit
#print axioms intervalCoupledDuhamel_heatGradient_Linfty_unit_of_constant
#print axioms intervalCoupledDuhamel_grad_estimate_gap_discharged
#print axioms intervalNeumannResolverR_chemotaxisDiv_C1_interior_lipschitz

end ShenWork.IntervalCHCDischarge
