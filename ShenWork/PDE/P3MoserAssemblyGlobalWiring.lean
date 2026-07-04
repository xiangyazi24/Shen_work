import ShenWork.PDE.P3MoserAssemblyFiller
import ShenWork.Paper3.IntervalDomainGlobalChain

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.IntervalDomainExistence.P3MoserAssemblyGlobalWiring

noncomputable section

/-- Wire the assembly filler into the global classical-regularity chain.

The filler produces the integrated-drop residual package from the decomposed
PDE frontier hypotheses.  The global chain supplies the missing classical
regularity data from `IntervalDomainGlobalClassicalRegularityInputs`, and the
integrated-drop package then converts to the route residuals surface. -/
theorem intervalDomain_massLpSmoothingRouteResiduals_global_assembly_wiring
    {p : CM2Params}
    (hinputs : _root_.ShenWork.Paper3.IntervalDomainGlobalClassicalRegularityInputs p)
    (hbdns : IntervalDomainBoundednessHyp p)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀)
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
    (hBoundedBefore :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IsPaper2BoundedBefore intervalDomain T u)
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
                u T pSeq rootBound) :
    _root_.ShenWork.IntervalDomainExistence.IntervalDomainMassLpSmoothingRouteResiduals p := by
  let hClassicalRegularity :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntervalDomainIntegratedMoserClassicalRegularityData u T p0 :=
    _root_.ShenWork.Paper3.intervalDomain_classicalRegularitySupplier_global_withInitialSlice
      (hinputs := hinputs)
  let hres : _root_.ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p :=
    P3MoserAssemblyFiller.intervalDomain_integratedDropResiduals_of_classical
      hbdns hClosedTrace hFTC hClassicalRegularity hBoundedBefore hGap
      hDyadicEndpoint
  exact hres.to_routeResiduals hClassicalRegularity ha hχ0

#print axioms intervalDomain_massLpSmoothingRouteResiduals_global_assembly_wiring

end

end ShenWork.IntervalDomainExistence.P3MoserAssemblyGlobalWiring
