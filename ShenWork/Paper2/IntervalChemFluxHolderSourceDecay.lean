/-
  ShenWork/Paper2/IntervalChemFluxHolderSourceDecay.lean

  Source-decay component assembly for the chemotaxis-flux Holder frontier.
-/
import ShenWork.Paper2.IntervalChemFluxHolderFrontier
import ShenWork.Paper2.IntervalResolverHolder

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
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

/-- Uniform component bounds and Holder moduli assemble the full
`ChemFluxCthetaSourceOn` source package.

This is deliberately a record assembler: measurability, integrability,
boundedness, and continuity of the flux are supplied separately, while the
Holder field is discharged from uniform bounds on `u`, `V_x`, and `V`. -/
theorem ChemFluxCthetaSourceOn_of_uniform_components
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {T θ CQ HQ U G Hu Hg Hv : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hCQ_nonneg : 0 ≤ CQ) (hHQ_nonneg : 0 ≤ HQ)
    (hU_nonneg : 0 ≤ U) (hG_nonneg : 0 ≤ G)
    (hHu_nonneg : 0 ≤ Hu) (hHg_nonneg : 0 ≤ Hg)
    (hcomp_le : Hu * G + U * Hg + U * G * p.β * Hv ≤ HQ)
    (flux_meas : Measurable (Function.uncurry (fun s => chemFluxLifted p (u s))))
    (flux_int : ∀ s : ℝ, Integrable (chemFluxLifted p (u s)) (intervalMeasure 1))
    (flux_bound : ∀ s : ℝ, 0 < s → s ≤ T → ∀ y : ℝ,
      |chemFluxLifted p (u s) y| ≤ CQ)
    (flux_cont : ∀ s : ℝ, 0 < s → s ≤ T → Continuous (chemFluxLifted p (u s)))
    (hu_bound : ∀ s, 0 < s → s ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (u s) x| ≤ U)
    (hg_bound : ∀ s, 0 < s → s ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |resolverGradReal p (u s) x| ≤ G)
    (hR_nonneg : ∀ s, 0 < s → s ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (intervalNeumannResolverR p (u s)) x)
    (hu_holder : ∀ s, 0 < s → s ≤ T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift (u s) a - intervalDomainLift (u s) b| ≤
          Hu * |a - b| ^ θ)
    (hg_holder : ∀ s, 0 < s → s ≤ T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |resolverGradReal p (u s) a - resolverGradReal p (u s) b| ≤
          Hg * |a - b| ^ θ)
    (hR_holder : ∀ s, 0 < s → s ≤ T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift (intervalNeumannResolverR p (u s)) a -
            intervalDomainLift (intervalNeumannResolverR p (u s)) b| ≤
          Hv * |a - b| ^ θ) :
    ChemFluxCthetaSourceOn p u T θ CQ HQ where
  theta_pos := hθ0
  theta_lt_one := hθ1
  CQ_nonneg := hCQ_nonneg
  HQ_nonneg := hHQ_nonneg
  flux_meas := flux_meas
  flux_int := flux_int
  flux_bound := flux_bound
  flux_cont := flux_cont
  flux_holder := by
    intro s hs0 hsT a b ha hb
    have hbase :
        |chemFluxLifted p (u s) a - chemFluxLifted p (u s) b| ≤
          (Hu * G + U * Hg + U * G * p.β * Hv) * |a - b| ^ θ :=
      chemFluxLifted_holder_of_component_holder
        (p := p) (w := u s) (θ := θ) (U := U) (G := G)
        (Hu := Hu) (Hg := Hg) (Hv := Hv)
        hU_nonneg hG_nonneg hHu_nonneg hHg_nonneg
        (hu_bound s hs0 hsT)
        (hg_bound s hs0 hsT)
        (hR_nonneg s hs0 hsT)
        (hu_holder s hs0 hsT)
        (hg_holder s hs0 hsT)
        (hR_holder s hs0 hsT)
        a b ha hb
    exact hbase.trans
      (mul_le_mul_of_nonneg_right hcomp_le
        (Real.rpow_nonneg (abs_nonneg _) _))

end

end ShenWork.Paper2
