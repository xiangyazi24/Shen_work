import ShenWork.Paper3.IntervalDomainIntegratedMoserAssembly
import ShenWork.PDE.P3MoserGradientIntegrability

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper3

noncomputable section

/-!
Global-classical chain for the integrated Moser assembly.

The closed-time Moser-gradient continuity remains an explicit input.  The
power-energy endpoint continuity is produced from the global classical branch,
the initial trace, and the re-anchored zero slice.
-/

/-- Full integrated-Moser classical regularity for a re-anchored global
classical solution, assuming the closed-time Moser-gradient continuity frontier. -/
theorem intervalDomain_classicalRegularityData_global_withInitialSlice
    {p : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hp0 : 1 ≤ p0)
    (hgrad : ∀ q, p0 ≤ q →
        ContinuousOn (intervalDomainMoserGradientEnergy
          (intervalDomainWithInitialSlice u₀ u) q) (Set.Icc 0 T)) :
    IntervalDomainIntegratedMoserClassicalRegularityData
      (intervalDomainWithInitialSlice u₀ u) T p0 := by
  have hend :
      IntervalDomainPowerEnergyEndpointContinuity
        (intervalDomainWithInitialSlice u₀ u) T p0 :=
    intervalDomain_powerEnergyEndpointContinuity_withInitialSlice_of_global_classical
      (p := p) (T := T) (p0 := p0) (u₀ := u₀) (u := u) (v := v)
      hglobal hT htrace hdatum hp0
  exact
    intervalDomain_classicalRegularityData_of_global_atZero_gradientContinuous
      (params := p) (T := T) (p0 := p0)
      (u := intervalDomainWithInitialSlice u₀ u) (v := v)
      (intervalDomain_globalClassical_withInitialSlice
        (params := p) (u₀ := u₀) (u := u) (v := v) hglobal)
      hT hend.atZero hgrad

/-- A finite branch seen by the reusable assembly is covered by the global
chain when it is presented as a re-anchored global branch with closed-time
Moser-gradient continuity. -/
def IntervalDomainGlobalClassicalRegularityInputs (p : CM2Params) : Prop :=
  ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u
      (p.N : ℝ) T rho p0 →
      ∃ (u₀ : intervalDomain.Point → ℝ)
        (uRaw : ℝ → intervalDomain.Point → ℝ),
        u = intervalDomainWithInitialSlice u₀ uRaw ∧
        IsPaper2GlobalClassicalSolution intervalDomain p uRaw v ∧
        InitialTrace intervalDomain u₀ uRaw ∧
        PaperPositiveInitialDatum intervalDomain u₀ ∧
        1 ≤ p0 ∧
        (∀ q, p0 ≤ q →
          ContinuousOn (intervalDomainMoserGradientEnergy u q)
            (Set.Icc 0 T))

/-- Turn the global re-anchoring input surface into the exact regularity
supplier expected by the integrated-step assembly. -/
theorem intervalDomain_classicalRegularitySupplier_global_withInitialSlice
    {p : CM2Params}
    (hinputs : IntervalDomainGlobalClassicalRegularityInputs p) :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      IntervalDomainIntegratedMoserClassicalRegularityData u T p0 := by
  intro T rho p0 u v hsol hcross hboot
  rcases hinputs hsol hcross hboot with
    ⟨u₀, uRaw, rfl, hglobal, htrace, hdatum, hp0, hgrad⟩
  exact
    intervalDomain_classicalRegularityData_global_withInitialSlice
      (p := p) (T := T) (p0 := p0) (u₀ := u₀) (u := uRaw) (v := v)
      hglobal (IsPaper2ClassicalSolution.T_pos hsol) htrace hdatum hp0 hgrad

/-- Full route residual package for the integrated-drop assembly, with the
classical-regularity supplier filled by the global re-anchoring chain above. -/
theorem intervalDomain_massLpSmoothingRouteResiduals_global_withInitialSlice
    {p : CM2Params}
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀)
    (hinputs : IntervalDomainGlobalClassicalRegularityInputs p)
    (boundednessHyp : IntervalDomainBoundednessHyp p)
    (closedEnergyTrace :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          Nonempty
            (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u))
    (integratedMoserDissipation :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntegratedMoserDissipationDropBefore intervalDomain u T rho p0)
    (relativeMassGradient :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          ∃ cGrad : ℝ → ℝ,
            (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
            (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
              LpMassGradientInterpolationEstimate intervalDomain
                (pExp + rho) eta Ceta T u) ∧
            (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
              intervalDomain.integral (fun x =>
                (u t x) ^ (pExp + rho - 2) *
                  (intervalDomain.gradNorm (u t) x) ^ 2) ≤
              cGrad pExp * intervalDomain.integral (fun x =>
                (intervalDomain.gradNorm
                  (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
            MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0)
    (quantitativeEndpoint :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (p.N : ℝ)
            (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound) :
    IntervalDomainMassLpSmoothingRouteResiduals p := by
  let hres : IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p :=
    { boundednessHyp := boundednessHyp
      closedEnergyTrace := closedEnergyTrace
      integratedMoserDissipation := integratedMoserDissipation
      relativeMassGradient := relativeMassGradient
      quantitativeEndpoint := quantitativeEndpoint }
  exact
    hres.to_routeResiduals
      (intervalDomain_classicalRegularitySupplier_global_withInitialSlice
        hinputs)
      ha hχ0

#print axioms intervalDomain_classicalRegularityData_global_withInitialSlice
#print axioms intervalDomain_classicalRegularitySupplier_global_withInitialSlice
#print axioms intervalDomain_massLpSmoothingRouteResiduals_global_withInitialSlice

end

end ShenWork.Paper3
