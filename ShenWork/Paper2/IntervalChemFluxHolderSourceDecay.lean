/-
  ShenWork/Paper2/IntervalChemFluxHolderSourceDecay.lean

  Source-decay component assembly for the chemotaxis-flux Holder frontier.
-/
import ShenWork.Paper2.IntervalChemFluxHolderFrontier
import ShenWork.Paper2.IntervalResolverHolder
import ShenWork.Paper2.ChemMildHolderBootstrap
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalMildToClassical

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.PDE (intervalNeumannResolverR)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

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
    (flux_int : ∀ s : ℝ, 0 < s → s ≤ T →
      Integrable (chemFluxLifted p (u s)) (intervalMeasure 1))
    (flux_bound : ∀ s : ℝ, 0 < s → s ≤ T → ∀ y : ℝ,
      |chemFluxLifted p (u s) y| ≤ CQ)
    (flux_cont : ∀ s : ℝ, 0 < s → s ≤ T →
      ContinuousOn (chemFluxLifted p (u s)) (Set.Icc (0 : ℝ) 1))
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

/-- Mild-solution specialization of `ChemFluxCthetaSourceOn_of_uniform_components`.

The `GradientMildSolutionData` fields discharge the source measurability,
positive-window integrability, positive-window sup bound, positive-window
continuity, the `u`-bound (`U = D.M`), and resolver nonnegativity. -/
theorem ChemFluxCthetaSourceOn_of_gradientMild_uniform_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ HQ G Hu Hg Hv : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hHQ_nonneg : 0 ≤ HQ)
    (hG_nonneg : 0 ≤ G)
    (hHu_nonneg : 0 ≤ Hu) (hHg_nonneg : 0 ≤ Hg)
    (hcomp_le : Hu * G + D.M * Hg + D.M * G * p.β * Hv ≤ HQ)
    (hu_holder : ∀ s, 0 < s → s ≤ D.T → ∀ x y : intervalDomainPoint,
      |D.u s x - D.u s y| ≤ Hu * |x.1 - y.1| ^ θ)
    (hg_bound : ∀ s, 0 < s → s ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |resolverGradReal p (D.u s) x| ≤ G)
    (hg_holder : ∀ s, 0 < s → s ≤ D.T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |resolverGradReal p (D.u s) a - resolverGradReal p (D.u s) b| ≤
          Hg * |a - b| ^ θ)
    (hR_holder : ∀ s, 0 < s → s ≤ D.T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift (intervalNeumannResolverR p (D.u s)) a -
            intervalDomainLift (intervalNeumannResolverR p (D.u s)) b| ≤
          Hv * |a - b| ^ θ) :
    ChemFluxCthetaSourceOn p D.u D.T θ
      (D.M * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  set CQ : ℝ := D.M * (Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nonneg : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg D.hM.le (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  have hu_bound : ∀ s, 0 < s → s ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (D.u s) x| ≤ D.M := by
    intro s hs0 hsT x hx
    simpa [intervalDomainLift, hx] using D.hbound s hs0 hsT ⟨x, hx⟩
  have hR_nonneg : ∀ s, 0 < s → s ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (intervalNeumannResolverR p (D.u s)) x := by
    intro s hs0 hsT x hx
    have hsub :=
      ShenWork.IntervalMildToClassical.mildChemical_nonneg
        (p := p) (u := D.u) (T := D.T) D.hnonneg D.hcont hs0 hsT ⟨x, hx⟩
    simpa [ShenWork.IntervalMildToClassical.mildChemicalConcentration,
      intervalDomainLift, hx] using hsub
  have hu_holder_lift : ∀ s, 0 < s → s ≤ D.T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift (D.u s) a - intervalDomainLift (D.u s) b| ≤
          Hu * |a - b| ^ θ := by
    intro s hs0 hsT a b ha hb
    simpa [intervalDomainLift, ha, hb] using
      hu_holder s hs0 hsT ⟨a, ha⟩ ⟨b, hb⟩
  refine ChemFluxCthetaSourceOn_of_uniform_components
    (p := p) (u := D.u) (T := D.T) (θ := θ) (CQ := CQ) (HQ := HQ)
    (U := D.M) (G := G) (Hu := Hu) (Hg := Hg) (Hv := Hv)
    hθ0 hθ1 hCQ_nonneg hHQ_nonneg D.hM.le hG_nonneg
    hHu_nonneg hHg_nonneg hcomp_le
    (chemFluxLifted_uncurry_measurable (p := p) (u := D.u) D.hmeas)
    ?_ ?_ ?_ hu_bound hg_bound hR_nonneg hu_holder_lift hg_holder hR_holder
  · intro s hs0 hsT
    exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
      p (fun x => D.hbound s hs0 hsT x) D.hM.le
      (D.hcont s hs0 hsT) (fun x => D.hnonneg s hs0 hsT x)
  · intro s hs0 hsT y
    simpa [hCQ] using
      BFormInitialTrace.chemFluxLifted_bound_of_ball
        p D.hM.le (fun x => D.hbound s hs0 hsT x)
        (fun x => D.hnonneg s hs0 hsT x)
        (D.hcont s hs0 hsT) y
  · intro s hs0 hsT
    exact Continuous.continuousOn
      (ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_continuous_of_continuous
        p (D.hcont s hs0 hsT) (fun x => D.hnonneg s hs0 hsT x))

end

end ShenWork.Paper2
