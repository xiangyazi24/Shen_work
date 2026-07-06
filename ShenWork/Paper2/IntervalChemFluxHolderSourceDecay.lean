/-
  ShenWork/Paper2/IntervalChemFluxHolderSourceDecay.lean

  Source-decay component assembly for the chemotaxis-flux Holder frontier.
-/
import ShenWork.Paper2.IntervalChemFluxHolderFrontier
import ShenWork.Paper2.IntervalResolverHolder

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverR)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

namespace ShenWork.Paper2

noncomputable section

/-- Source-decay resolver components plus `u`-component bounds give a Holder
modulus for the nonlinear chemotaxis flux on `[0,1]`.

The remaining assumptions are genuinely about the `u` slice itself and
resolver positivity.  The resolver-gradient bound, resolver-gradient Holder
modulus, and resolver-value Holder modulus are produced internally from
`SourceCoeffQuadraticDecay`. -/
theorem chemFluxLifted_holder_Icc_of_sourceDecay_components
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p w)
    {θ U Hu : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hU_nonneg : 0 ≤ U) (hHu_nonneg : 0 ≤ Hu)
    (hu_bound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |intervalDomainLift w x| ≤ U)
    (hu_holder : ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift w a - intervalDomainLift w b| ≤
          Hu * |a - b| ^ θ)
    (hR_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (intervalNeumannResolverR p w) x) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |chemFluxLifted p w a - chemFluxLifted p w b| ≤
          HQ * |a - b| ^ θ := by
  rcases resolverGradReal_bounded_of_sourceDecay (p := p) (w := w) hdecay with
    ⟨G, hG_nonneg, hg_bound⟩
  rcases resolverGradReal_holder_Icc_of_sourceDecay
      (p := p) (w := w) hdecay hθ0 hθ1 with
    ⟨Hg, hHg_nonneg, hg_holder⟩
  rcases intervalNeumannResolverR_lift_holder_Icc_of_sourceDecay
      (p := p) (w := w) hdecay hθ0 hθ1 with
    ⟨Hv, hHv_nonneg, hR_holder⟩
  let HQ : ℝ := Hu * G + U * Hg + U * G * p.β * Hv
  have hHQ_nonneg : 0 ≤ HQ := by
    dsimp [HQ]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hHu_nonneg hG_nonneg)
        (mul_nonneg hU_nonneg hHg_nonneg))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hU_nonneg hG_nonneg)
          p.hβ)
        hHv_nonneg)
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  intro a b ha hb
  dsimp [HQ]
  exact chemFluxLifted_holder_of_component_holder
    (p := p) (w := w) (θ := θ) (U := U) (G := G)
    (Hu := Hu) (Hg := Hg) (Hv := Hv)
    hU_nonneg hG_nonneg hHu_nonneg hHg_nonneg
    hu_bound hg_bound hR_nonneg hu_holder hg_holder hR_holder
    a b ha hb

end

end ShenWork.Paper2
