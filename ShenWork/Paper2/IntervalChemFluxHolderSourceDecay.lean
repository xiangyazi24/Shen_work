/-
  ShenWork/Paper2/IntervalChemFluxHolderSourceDecay.lean

  Source-decay component assembly for the chemotaxis-flux Holder frontier.
-/
import ShenWork.Paper2.IntervalChemFluxHolderFrontier
import ShenWork.Paper2.IntervalResolverHolder
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.IntervalInitialHolder
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
continuity, the `u`-bound (`U = D.M`), the resolver-gradient sup bound, the
resolver-value Holder bound, and resolver nonnegativity. -/
theorem ChemFluxCthetaSourceOn_of_gradientMild_uniform_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ HQ Hu Hg : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hHQ_nonneg : 0 ≤ HQ)
    (hHu_nonneg : 0 ≤ Hu) (hHg_nonneg : 0 ≤ Hg)
    (hcomp_le :
      Hu * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * D.M ^ p.γ))) +
        D.M * Hg +
        D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ))) * p.β *
          (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * D.M ^ p.γ))) ≤ HQ)
    (hu_holder : ∀ s, 0 < s → s ≤ D.T → ∀ x y : intervalDomainPoint,
      |D.u s x - D.u s y| ≤ Hu * |x.1 - y.1| ^ θ)
    (hg_holder : ∀ s, 0 < s → s ≤ D.T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |resolverGradReal p (D.u s) a - resolverGradReal p (D.u s) b| ≤
          Hg * |a - b| ^ θ) :
    ChemFluxCthetaSourceOn p D.u D.T θ
      (D.M * (Real.sqrt (∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  set CQ : ℝ := D.M * (Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ))) with hCQ
  set G : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ)) with hG
  have hG_nonneg : 0 ≤ G := by
    rw [hG]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hCQ_nonneg : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg D.hM.le hG_nonneg
  have hu_bound : ∀ s, 0 < s → s ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |intervalDomainLift (D.u s) x| ≤ D.M := by
    intro s hs0 hsT x hx
    simpa [intervalDomainLift, hx] using D.hbound s hs0 hsT ⟨x, hx⟩
  have hcont_on : ∀ s, 0 < s → s ≤ D.T →
      ContinuousOn (intervalDomainLift (D.u s)) (Set.Icc (0 : ℝ) 1) := by
    intro s hs0 hsT
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift (D.u s)) =
        D.u s := by
      ext ⟨y, hy⟩
      simp [Set.restrict, intervalDomainLift, hy]
      rfl
    rw [this]
    exact D.hcont s hs0 hsT
  have hlb : ∀ s, 0 < s → s ≤ D.T → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ intervalDomainLift (D.u s) y := by
    intro s hs0 hsT y hy
    simpa [intervalDomainLift, hy] using D.hnonneg s hs0 hsT ⟨y, hy⟩
  have hub : ∀ s, 0 < s → s ≤ D.T → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (D.u s) y ≤ D.M := by
    intro s hs0 hsT y hy
    have hb := D.hbound s hs0 hsT ⟨y, hy⟩
    simpa [intervalDomainLift, hy] using (abs_le.mp hb).2
  have hg_bound : ∀ s, 0 < s → s ≤ D.T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |resolverGradReal p (D.u s) x| ≤ G := by
    intro s hs0 hsT x hx
    rw [hG]
    exact ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
      p (hcont_on s hs0 hsT) (hlb s hs0 hsT) (hub s hs0 hsT) hx
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
  have hR_holder : ∀ s, 0 < s → s ≤ D.T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |intervalDomainLift (intervalNeumannResolverR p (D.u s)) a -
            intervalDomainLift (intervalNeumannResolverR p (D.u s)) b| ≤
          G * |a - b| ^ θ := by
    intro s hs0 hsT a b ha hb
    rw [hG]
    exact ShenWork.IntervalResolverWeakBounds.intervalNeumannResolverR_lift_holder_Icc_of_bounded
      p hθ0 hθ1.le (hcont_on s hs0 hsT) (hlb s hs0 hsT) (hub s hs0 hsT) ha hb
  refine ChemFluxCthetaSourceOn_of_uniform_components
    (p := p) (u := D.u) (T := D.T) (θ := θ) (CQ := CQ) (HQ := HQ)
    (U := D.M) (G := G) (Hu := Hu) (Hg := Hg) (Hv := G)
    hθ0 hθ1 hCQ_nonneg hHQ_nonneg D.hM.le hG_nonneg
    hHu_nonneg hHg_nonneg ?_
    (chemFluxLifted_uncurry_measurable (p := p) (u := D.u) D.hmeas)
    ?_ ?_ ?_ hu_bound hg_bound hR_nonneg hu_holder_lift hg_holder hR_holder
  · simpa [hG] using hcomp_le
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

/-- Mild-solution source package from initial-data Holder regularity plus the
contractive-coupling frontier for the homogeneous Neumann heat leg.

This wrapper uses the existing small-time mild Holder theorem to produce the
uniform `u`-Holder modulus internally, and chooses the resulting source Holder
constant `HQ` explicitly.  The resolver-gradient Holder modulus remains a real
frontier input. -/
theorem ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ H₀ Hg : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hH₀_nonneg : 0 ≤ H₀) (hHg_nonneg : 0 ≤ Hg)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor t x y (intervalDomainLift u₀))
    (hg_holder : ∀ s, 0 < s → s ≤ D.T → ∀ a b : ℝ,
      a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
        |resolverGradReal p (D.u s) a - resolverGradReal p (D.u s) b| ≤
          Hg * |a - b| ^ θ) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemFluxCthetaSourceOn p D.u D.T θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  rcases mild_orderBox_smallTime_holder_of_initialDatumHolder_contracting_couplings
      D hθ0 hθ1 hH₀_nonneg hholder hplan with
    ⟨Hu, hHu_nonneg, hu_holder⟩
  set G : ℝ := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ)) with hG
  set HQ : ℝ := Hu * G + D.M * Hg + D.M * G * p.β * G with hHQ
  have hG_nonneg : 0 ≤ G := by
    rw [hG]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _)))
  have hHQ_nonneg : 0 ≤ HQ := by
    rw [hHQ]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hHu_nonneg hG_nonneg)
        (mul_nonneg D.hM.le hHg_nonneg))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg D.hM.le hG_nonneg)
          p.hβ)
        hG_nonneg)
  refine ⟨HQ, hHQ_nonneg, ?_⟩
  refine ChemFluxCthetaSourceOn_of_gradientMild_uniform_components
    (D := D) (θ := θ) (HQ := HQ) (Hu := Hu) (Hg := Hg)
    hθ0 hθ1 hHQ_nonneg hHu_nonneg hHg_nonneg ?_ hu_holder hg_holder
  rw [hHQ, hG]

/-- Uniform resolver-gradient spatial Holder bound from per-slice source decay
and one uniform bound on the resolver second derivative.

This is a consumer for the remaining analytic frontier: it does not produce the
uniform `resolverGrad2Real` bound, but it packages exactly the MVT step needed
to turn that bound into the `hg_holder` field used by the chemFlux assembler. -/
theorem resolverGradReal_uniform_holder_Icc_of_sourceDecay_grad2Bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T θ Hg : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hHg_nonneg : 0 ≤ Hg)
    (hdecay : ∀ s, 0 < s → s ≤ T → SourceCoeffQuadraticDecay p (u s))
    (hgrad2_bound : ∀ s, 0 < s → s ≤ T → ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |resolverGrad2Real p (u s) z| ≤ Hg) :
    ∀ s, 0 < s → s ≤ T → ∀ x y : ℝ,
      x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 →
        |resolverGradReal p (u s) x - resolverGradReal p (u s) y| ≤
          Hg * |x - y| ^ θ := by
  intro s hs0 hsT x y hx hy
  have hsdecay : SourceCoeffQuadraticDecay p (u s) := hdecay s hs0 hsT
  have hderiv : ∀ z : ℝ, HasDerivAt (fun y : ℝ => resolverGradReal p (u s) y)
      (resolverGrad2Real p (u s) z) z :=
    fun z => resolverGradReal_hasDerivAt_of_sourceDecay hsdecay z
  have hdiffAt : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun y : ℝ => resolverGradReal p (u s) y) z :=
    fun z _ => (hderiv z).differentiableAt
  have hderiv_eq : ∀ z : ℝ,
      deriv (fun y : ℝ => resolverGradReal p (u s) y) z =
        resolverGrad2Real p (u s) z :=
    fun z => (hderiv z).deriv
  have hbound : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv (fun y : ℝ => resolverGradReal p (u s) y) z‖ ≤ Hg := by
    intro z hz
    rw [Real.norm_eq_abs, hderiv_eq z]
    exact hgrad2_bound s hs0 hsT z hz
  have hlip :
      |resolverGradReal p (u s) x - resolverGradReal p (u s) y| ≤
        Hg * |x - y| := by
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun y => resolverGradReal p (u s) y)
      hdiffAt hbound (convex_Icc 0 1) hx hy
    simp only [Real.norm_eq_abs] at hmv
    rw [abs_sub_comm (resolverGradReal p (u s) x), abs_sub_comm x y]
    exact hmv
  have hdist_le_one : |x - y| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hdist_le_pow : |x - y| ≤ |x - y| ^ θ := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (x := |x - y|) (y := 1) (z := θ)
        (abs_nonneg _) hdist_le_one hθ0.le hθ1)
  exact hlip.trans (mul_le_mul_of_nonneg_left hdist_le_pow hHg_nonneg)

/-- Initial-data Holder chemFlux source package with the resolver-gradient
Holder field discharged from a uniform resolver-second-derivative bound. -/
theorem ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_grad2_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ H₀ Hg : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hH₀_nonneg : 0 ≤ H₀) (hHg_nonneg : 0 ≤ Hg)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor t x y (intervalDomainLift u₀))
    (hdecay : ∀ s, 0 < s → s ≤ D.T → SourceCoeffQuadraticDecay p (D.u s))
    (hgrad2_bound : ∀ s, 0 < s → s ≤ D.T → ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |resolverGrad2Real p (D.u s) z| ≤ Hg) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemFluxCthetaSourceOn p D.u D.T θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  have hg_holder :=
    resolverGradReal_uniform_holder_Icc_of_sourceDecay_grad2Bound
      (p := p) (u := D.u) (T := D.T) hθ0 hθ1.le hHg_nonneg hdecay hgrad2_bound
  exact ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_components
    D hθ0 hθ1 hH₀_nonneg hHg_nonneg hholder hplan hg_holder

/-- Uniform quadratic decay of the elliptic source coefficients on the positive
time window.  This is the quantitative upstream frontier that can produce the
uniform resolver-gradient C¹ control used by Task175. -/
structure UniformSourceCoeffQuadraticDecayOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T Csrc : ℝ) : Prop where
  Csrc_nonneg : 0 ≤ Csrc
  decay : ∀ s, 0 < s → s ≤ T → ∀ k : ℕ, 1 ≤ k →
    |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| ≤
      Csrc / ((k : ℝ) * Real.pi) ^ 2

/-- Uniform cosine-coefficient decay for the power source `ν*u^γ` is exactly the
same positive-mode decay as `UniformSourceCoeffQuadraticDecayOn`.  This bridge
connects window-uniform power-source producers to the Task176 interface. -/
theorem UniformSourceCoeffQuadraticDecayOn_of_powerSource_cosineCoeff_decay
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T Csrc : ℝ}
    (hCsrc : 0 ≤ Csrc)
    (hdecay : ∀ s, 0 < s → s ≤ T → ∀ k : ℕ, 1 ≤ k →
      |ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (fun x => p.ν * intervalDomainLift (u s) x ^ p.γ) k| ≤
        Csrc / ((k : ℝ) * Real.pi) ^ 2) :
    UniformSourceCoeffQuadraticDecayOn p u T Csrc := by
  refine ⟨hCsrc, ?_⟩
  intro s hs0 hsT k hk
  have hkne : k ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hre_eq :
      (ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re =
        ShenWork.IntervalNeumannFullKernel.cosineCoeffs
          (fun x => p.ν * intervalDomainLift (u s) x ^ p.γ) k := by
    unfold ShenWork.PDE.intervalNeumannResolverSourceCoeff
    unfold ShenWork.IntervalNeumannFullKernel.cosineCoeffs
    simp only [Complex.ofReal_re,
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
      if_neg hkne]
  rw [hre_eq]
  exact hdecay s hs0 hsT k hk

/-- A uniform source-coefficient decay record gives per-time
`SourceCoeffQuadraticDecay`. -/
def UniformSourceCoeffQuadraticDecayOn.sourceDecay
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T Csrc : ℝ}
    (H : UniformSourceCoeffQuadraticDecayOn p u T Csrc) :
    ∀ s, 0 < s → s ≤ T → SourceCoeffQuadraticDecay p (u s) := by
  intro s hs0 hsT
  exact ⟨Csrc, H.Csrc_nonneg, H.decay s hs0 hsT⟩

/-- Fixed summable majorant for the resolver second derivative under a uniform
source-coefficient quadratic decay constant. -/
noncomputable def resolverGrad2UniformMajorant (Csrc : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else Csrc / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2)

theorem resolverGrad2UniformMajorant_nonneg {Csrc : ℝ}
    (hCsrc : 0 ≤ Csrc) (k : ℕ) :
    0 ≤ resolverGrad2UniformMajorant Csrc k := by
  by_cases hk : k = 0
  · simp [resolverGrad2UniformMajorant, hk]
  · have hpi2 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    have hk2 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
    simpa [resolverGrad2UniformMajorant, hk] using
      mul_nonneg (div_nonneg hCsrc hpi2) (inv_nonneg.mpr hk2)

theorem resolverGrad2UniformMajorant_summable (Csrc : ℝ) :
    Summable fun k : ℕ => resolverGrad2UniformMajorant Csrc k := by
  classical
  rw [← summable_nat_add_iff 1]
  have hp2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
  convert hp2.mul_left (Csrc / Real.pi ^ 2) using 1
  ext k
  simp [resolverGrad2UniformMajorant, Nat.cast_add, Nat.cast_one]

/-- Concrete uniform bound obtained by summing the fixed second-derivative
majorant. -/
noncomputable def resolverGrad2UniformBound (Csrc : ℝ) : ℝ :=
  ∑' k : ℕ, resolverGrad2UniformMajorant Csrc k

theorem resolverGrad2UniformBound_nonneg {Csrc : ℝ} (hCsrc : 0 ≤ Csrc) :
    0 ≤ resolverGrad2UniformBound Csrc := by
  exact tsum_nonneg fun k => resolverGrad2UniformMajorant_nonneg hCsrc k

/-- Uniform source-coefficient quadratic decay gives a single uniform bound on
the resolver second derivative series. -/
theorem resolverGrad2Real_uniform_bound_of_uniformSourceCoeffQuadraticDecayOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T Csrc : ℝ}
    (H : UniformSourceCoeffQuadraticDecayOn p u T Csrc) :
    ∀ s, 0 < s → s ≤ T → ∀ z : ℝ,
      |resolverGrad2Real p (u s) z| ≤ resolverGrad2UniformBound Csrc := by
  classical
  set majorant : ℕ → ℝ := resolverGrad2UniformMajorant Csrc with hmajorant
  have hmajorant_sum : Summable majorant := by
    simpa [majorant] using resolverGrad2UniformMajorant_summable Csrc
  intro s hs0 hsT z
  set term : ℕ → ℝ := fun k =>
    (ShenWork.PDE.intervalNeumannResolverCoeff p (u s) k).re *
      (-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * z)) with hterm
  have hterm_le : ∀ k : ℕ, ‖term k‖ ≤ majorant k := by
    intro k
    by_cases hk0 : k = 0
    · subst k
      simp [term, majorant, resolverGrad2UniformMajorant]
    · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
      have hkpos_nat : 0 < k := Nat.pos_of_ne_zero hk0
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos_nat
      have hkpipos : (0 : ℝ) < (k : ℝ) * Real.pi := mul_pos hkpos Real.pi_pos
      have hkpisqpos : (0 : ℝ) < ((k : ℝ) * Real.pi) ^ 2 := by positivity
      have hden_pos : 0 < p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k :=
        ShenWork.PDE.intervalNeumannResolver_denom_pos p k
      have hlam :
          ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k =
            (k : ℝ) ^ 2 * Real.pi ^ 2 := rfl
      have hdenlow :
          ((k : ℝ) * Real.pi) ^ 2 ≤
            p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k := by
        rw [hlam]
        nlinarith [p.hμ.le, sq_nonneg ((k : ℝ) * Real.pi)]
      have hsrc := H.decay s hs0 hsT k hk1
      have hmode :
          |(-(((k : ℝ) * Real.pi) ^ 2) * Real.cos ((k : ℝ) * Real.pi * z))| ≤
            ((k : ℝ) * Real.pi) ^ 2 := by
        rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg _)]
        calc ((k : ℝ) * Real.pi) ^ 2 * |Real.cos ((k : ℝ) * Real.pi * z)|
            ≤ ((k : ℝ) * Real.pi) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg _)
          _ = ((k : ℝ) * Real.pi) ^ 2 := mul_one _
      have hcoeff :
          |(ShenWork.PDE.intervalNeumannResolverCoeff p (u s) k).re| =
            |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| /
              (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) := by
        rw [ShenWork.IntervalResolverGradientBridge.resolverCoeff_re_eq,
          abs_div, abs_of_pos hden_pos]
      have hterm_base :
          ‖term k‖ ≤
            |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| /
              (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
                ((k : ℝ) * Real.pi) ^ 2 := by
        rw [hterm, Real.norm_eq_abs, abs_mul, hcoeff]
        exact mul_le_mul_of_nonneg_left hmode
          (div_nonneg (abs_nonneg _) hden_pos.le)
      have hratio :
          |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| /
              (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
                ((k : ℝ) * Real.pi) ^ 2 ≤
            |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| := by
        have hdivle : ((k : ℝ) * Real.pi) ^ 2 /
            (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) ≤ 1 := by
          exact (div_le_one hden_pos).2 hdenlow
        calc
          |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| /
              (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
                ((k : ℝ) * Real.pi) ^ 2
              = |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| *
                  (((k : ℝ) * Real.pi) ^ 2 /
                    (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k)) := by
                ring
          _ ≤ |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| * 1 :=
              mul_le_mul_of_nonneg_left hdivle (abs_nonneg _)
          _ = |(ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u s) k).re| := mul_one _
      have htarget :
          Csrc / ((k : ℝ) * Real.pi) ^ 2 = majorant k := by
        rw [hmajorant, resolverGrad2UniformMajorant, if_neg hk0]
        have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
        field_simp [hkne, Real.pi_ne_zero]
      exact hterm_base.trans (hratio.trans (hsrc.trans (by rw [htarget])))
  have hterm_sum : Summable term := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hterm_le hmajorant_sum
  have hnorm_sum : Summable fun k : ℕ => ‖term k‖ := hterm_sum.norm
  have hsum_norm_le :
      (∑' k : ℕ, ‖term k‖) ≤ resolverGrad2UniformBound Csrc := by
    simpa [resolverGrad2UniformBound, majorant] using
      hnorm_sum.tsum_le_tsum hterm_le hmajorant_sum
  calc
    |resolverGrad2Real p (u s) z|
        = ‖∑' k : ℕ, term k‖ := by
          rw [Real.norm_eq_abs]
          congr 1
    _ ≤ ∑' k : ℕ, ‖term k‖ := norm_tsum_le_tsum_norm hterm_sum.norm
    _ ≤ resolverGrad2UniformBound Csrc := hsum_norm_le

/-- Initial-data Holder chemFlux source package from a uniform source-coefficient
quadratic decay frontier. -/
theorem ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_uniformSourceCoeff_components
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {θ H₀ Csrc : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀)
    (hplan : ∀ t, 0 < t → t ≤ D.T → ∀ x y : intervalDomainPoint,
      NeumannHeatContractiveCouplingFor t x y (intervalDomainLift u₀))
    (Hsrc : UniformSourceCoeffQuadraticDecayOn p D.u D.T Csrc) :
    ∃ HQ : ℝ, 0 ≤ HQ ∧
      ChemFluxCthetaSourceOn p D.u D.T θ
        (D.M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * D.M ^ p.γ)))) HQ := by
  exact ChemFluxCthetaSourceOn_of_gradientMild_initialHolder_grad2_components
    D hθ0 hθ1 hH₀_nonneg
    (resolverGrad2UniformBound_nonneg Hsrc.Csrc_nonneg)
    hholder hplan Hsrc.sourceDecay
    (by
      intro s hs0 hsT z _hz
      exact resolverGrad2Real_uniform_bound_of_uniformSourceCoeffQuadraticDecayOn
        Hsrc s hs0 hsT z)

end

end ShenWork.Paper2
