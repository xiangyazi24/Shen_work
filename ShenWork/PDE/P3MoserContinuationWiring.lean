import ShenWork.PDE.P3MoserFirstCrossingContinuation

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.IntervalDomainExistence.P3MoserContinuationWiring

noncomputable section

/-!
Continuation-based wiring for the integrated-drop Moser residual package.

The only purpose of this layer is to replace the assembly filler's circular
`hBoundedBefore` input by the non-circular first-crossing continuation
residuals from `P3MoserFirstCrossingContinuation`.
-/

theorem intervalDomain_integratedDropResiduals_via_continuation
    {p : CM2Params}
    (hbdns : IntervalDomainBoundednessHyp p)
    (hClosedTrace :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          Nonempty
            (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u))
    (hFTC :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hClassicalRegularity :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hGap :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hDyadicEndpoint :
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
              IntegratedMoserDissipationDropBefore
                intervalDomain u T (2 * p.γ) pExp →
              _root_.ShenWork.IntervalDomainExistence.P3MoserQuantitativeEndpointDischarge.DyadicMoserEndpointRecurrence
                u T pSeq rootBound)
    (hShort : ShortTimeBoundedBeforeResidual intervalDomain p)
    (hAssembly : SubintervalAssemblyResidual intervalDomain p)
    (hExtend : ExtensionByContinuityResidual intervalDomain p)
    (hClosure : FirstCrossingSupremumClosureResidual intervalDomain p) :
    _root_.ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p := by
  let hBoundedBefore :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IsPaper2BoundedBefore intervalDomain T u := by
    intro T rho p0 u v hsol _hcross _hboot
    exact
      boundedBefore_of_classical_and_assembly
        hShort hAssembly hExtend hClosure hsol
  exact
    P3MoserAssemblyFiller.intervalDomain_integratedDropResiduals_of_classical
      hbdns hClosedTrace hFTC hClassicalRegularity hBoundedBefore hGap
      hDyadicEndpoint

#print axioms intervalDomain_integratedDropResiduals_via_continuation

end

end ShenWork.IntervalDomainExistence.P3MoserContinuationWiring
