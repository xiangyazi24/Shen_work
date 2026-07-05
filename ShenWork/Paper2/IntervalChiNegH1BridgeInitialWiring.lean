import ShenWork.Paper2.IntervalChiNegH1InitialWiring
import ShenWork.Paper2.IntervalChiNegH1Bridge

/-!
# H¹ bridge routes with split initial endpoint data

This file combines the route-specific H¹ bridge packages with the split
initial-endpoint data from `IntervalChiNegH1InitialWiring`.  It is only wiring:
all physical estimates, RHS/component regularity, and endpoint
trace/compatibility remain explicit hypotheses.  The old wrappers also retain
an explicit local H¹ seed; the `_before` variants use the scalar-DI seed
producer from `IntervalChiNegH1InitialWiring`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1InitialContinuity
open ShenWork.Paper2.IntervalChiNegH1InitialWiring
open ShenWork.Paper2.IntervalChiNegH1Bridge

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1BridgeInitialWiring

/-- Parametric route to bounded-before, using split initial endpoint data and
raw RHS interval-integrability in the route package. -/
theorem boundedBefore_of_parametricSplit_initialTraceEnergy
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1ParametricSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit hsplit)
    hlocal

/-- Parametric route to bounded-before from a classical solution, using split
initial endpoint data and raw RHS interval-integrability in the route package.
-/
theorem boundedBefore_of_parametricSplit_classical_initialTraceEnergy
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1ParametricSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit hsplit)
    hlocal

/-- Spectral route to bounded-before, using split initial endpoint data and raw
RHS interval-integrability in the route package. -/
theorem boundedBefore_of_spectralSplit_initialTraceEnergy
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1SpectralSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit hsplit)
    hlocal

/-- Spectral route to bounded-before from a classical solution, using split
initial endpoint data and raw RHS interval-integrability in the route package.
-/
theorem boundedBefore_of_spectralSplit_classical_initialTraceEnergy
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1SpectralSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit hsplit)
    hlocal

/-- Parametric route to bounded-before, using split initial endpoint data and
component continuity instead of raw RHS interval-integrability. -/
theorem boundedBefore_of_parametricSplit_components_initialTraceEnergy
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1ParametricSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit_componentsContinuous
      hsplit)
    hlocal

/-- Parametric route to bounded-before from a classical solution, using split
initial endpoint data and component continuity instead of raw RHS
interval-integrability. -/
theorem boundedBefore_of_parametricSplit_components_classical_initialTraceEnergy
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1ParametricSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit_componentsContinuous
      hsplit)
    hlocal

/-- Spectral route to bounded-before, using split initial endpoint data and
component continuity instead of raw RHS interval-integrability. -/
theorem boundedBefore_of_spectralSplit_components_initialTraceEnergy
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1SpectralSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit_componentsContinuous
      hsplit)
    hlocal

/-- Spectral route to bounded-before from a classical solution, using split
initial endpoint data and component continuity instead of raw RHS
interval-integrability. -/
theorem boundedBefore_of_spectralSplit_components_classical_initialTraceEnergy
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1SpectralSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit_componentsContinuous
      hsplit)
    hlocal

/-- Parametric route to bounded-before, using bundled H¹ endpoint data. -/
theorem boundedBefore_of_parametricSplit_initialEndpointData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1ParametricSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_parametricSplit_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hsplit hlocal

/-- Parametric route to bounded-before from a classical solution, using bundled
H¹ endpoint data. -/
theorem boundedBefore_of_parametricSplit_classical_initialEndpointData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1ParametricSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_parametricSplit_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hsplit hlocal

/-- Spectral route to bounded-before, using bundled H¹ endpoint data. -/
theorem boundedBefore_of_spectralSplit_initialEndpointData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1SpectralSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_spectralSplit_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hsplit hlocal

/-- Spectral route to bounded-before from a classical solution, using bundled
H¹ endpoint data. -/
theorem boundedBefore_of_spectralSplit_classical_initialEndpointData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1SpectralSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_spectralSplit_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hsplit hlocal

/-- Parametric component-continuity route to bounded-before, using bundled H¹
endpoint data. -/
theorem boundedBefore_of_parametricSplit_components_initialEndpointData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1ParametricSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_parametricSplit_components_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hsplit hlocal

/-- Parametric component-continuity route to bounded-before from a classical
solution, using bundled H¹ endpoint data. -/
theorem boundedBefore_of_parametricSplit_components_classical_initialEndpointData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1ParametricSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_parametricSplit_components_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hsplit hlocal

/-- Spectral component-continuity route to bounded-before, using bundled H¹
endpoint data. -/
theorem boundedBefore_of_spectralSplit_components_initialEndpointData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1SpectralSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_spectralSplit_components_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hsplit hlocal

/-- Spectral component-continuity route to bounded-before from a classical
solution, using bundled H¹ endpoint data. -/
theorem boundedBefore_of_spectralSplit_components_classical_initialEndpointData
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hsplit : H1SpectralSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_spectralSplit_components_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hsplit hlocal

/-- Parametric route to bounded-before, using split initial endpoint data and
producing the local H¹ seed from the scalar differential inequality. -/
theorem boundedBefore_of_parametricSplit_initialTraceEnergy_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1ParametricSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit hsplit)

/-- Classical parametric route with split initial endpoint data and no manual
local H¹ seed. -/
theorem boundedBefore_of_parametricSplit_classical_initialTraceEnergy_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1ParametricSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit hsplit)

/-- Spectral route with split initial endpoint data and no manual local H¹
seed. -/
theorem boundedBefore_of_spectralSplit_initialTraceEnergy_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1SpectralSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit hsplit)

/-- Classical spectral route with split initial endpoint data and no manual
local H¹ seed. -/
theorem boundedBefore_of_spectralSplit_classical_initialTraceEnergy_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1SpectralSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit hsplit)

/-- Parametric component-continuity route with split initial endpoint data and
no manual local H¹ seed. -/
theorem boundedBefore_of_parametricSplit_components_initialTraceEnergy_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1ParametricSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit_componentsContinuous
      hsplit)

/-- Classical parametric component-continuity route with split initial endpoint
data and no manual local H¹ seed. -/
theorem boundedBefore_of_parametricSplit_components_classical_initialTraceEnergy_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1ParametricSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit_componentsContinuous
      hsplit)

/-- Spectral component-continuity route with split initial endpoint data and no
manual local H¹ seed. -/
theorem boundedBefore_of_spectralSplit_components_initialTraceEnergy_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1SpectralSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit_componentsContinuous
      hsplit)

/-- Classical spectral component-continuity route with split initial endpoint
data and no manual local H¹ seed. -/
theorem boundedBefore_of_spectralSplit_components_classical_initialTraceEnergy_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1SpectralSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    htend hcompat
    (H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit_componentsContinuous
      hsplit)

/-- Parametric route to bounded-before, using bundled H¹ endpoint data and no
manual local H¹ seed. -/
theorem boundedBefore_of_parametricSplit_initialEndpointData_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1ParametricSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_parametricSplit_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hsplit

/-- Classical parametric route with bundled H¹ endpoint data and no manual
local H¹ seed. -/
theorem boundedBefore_of_parametricSplit_classical_initialEndpointData_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1ParametricSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_parametricSplit_classical_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hsplit

/-- Spectral route with bundled H¹ endpoint data and no manual local H¹ seed.
-/
theorem boundedBefore_of_spectralSplit_initialEndpointData_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1SpectralSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_spectralSplit_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hsplit

/-- Classical spectral route with bundled H¹ endpoint data and no manual local
H¹ seed. -/
theorem boundedBefore_of_spectralSplit_classical_initialEndpointData_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1SpectralSplitSqrtRHSIntegrableBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_spectralSplit_classical_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hsplit

/-- Parametric component-continuity route with bundled H¹ endpoint data and no
manual local H¹ seed. -/
theorem boundedBefore_of_parametricSplit_components_initialEndpointData_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1ParametricSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_parametricSplit_components_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hsplit

/-- Classical parametric component-continuity route with bundled H¹ endpoint
data and no manual local H¹ seed. -/
theorem boundedBefore_of_parametricSplit_components_classical_initialEndpointData_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1ParametricSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uxt) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_parametricSplit_components_classical_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hsplit

/-- Spectral component-continuity route with bundled H¹ endpoint data and no
manual local H¹ seed. -/
theorem boundedBefore_of_spectralSplit_components_initialEndpointData_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1SpectralSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_spectralSplit_components_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hsplit

/-- Classical spectral component-continuity route with bundled H¹ endpoint data
and no manual local H¹ seed. -/
theorem boundedBefore_of_spectralSplit_components_classical_initialEndpointData_before
    {params : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L : ℝ}
    (hsplit : H1SpectralSplitSqrtComponentContinuousBefore params u T
      V₁ V₂ M L taxisX uvxx reactX uhatT) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_spectralSplit_components_classical_initialTraceEnergy_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hsplit

#print axioms boundedBefore_of_parametricSplit_initialTraceEnergy
#print axioms boundedBefore_of_parametricSplit_classical_initialTraceEnergy
#print axioms boundedBefore_of_spectralSplit_initialTraceEnergy
#print axioms boundedBefore_of_spectralSplit_classical_initialTraceEnergy
#print axioms boundedBefore_of_parametricSplit_components_initialTraceEnergy
#print axioms boundedBefore_of_parametricSplit_components_classical_initialTraceEnergy
#print axioms boundedBefore_of_spectralSplit_components_initialTraceEnergy
#print axioms boundedBefore_of_spectralSplit_components_classical_initialTraceEnergy
#print axioms boundedBefore_of_parametricSplit_initialEndpointData
#print axioms boundedBefore_of_parametricSplit_classical_initialEndpointData
#print axioms boundedBefore_of_spectralSplit_initialEndpointData
#print axioms boundedBefore_of_spectralSplit_classical_initialEndpointData
#print axioms boundedBefore_of_parametricSplit_components_initialEndpointData
#print axioms boundedBefore_of_parametricSplit_components_classical_initialEndpointData
#print axioms boundedBefore_of_spectralSplit_components_initialEndpointData
#print axioms boundedBefore_of_spectralSplit_components_classical_initialEndpointData
#print axioms boundedBefore_of_parametricSplit_initialTraceEnergy_before
#print axioms boundedBefore_of_parametricSplit_classical_initialTraceEnergy_before
#print axioms boundedBefore_of_spectralSplit_initialTraceEnergy_before
#print axioms boundedBefore_of_spectralSplit_classical_initialTraceEnergy_before
#print axioms boundedBefore_of_parametricSplit_components_initialTraceEnergy_before
#print axioms boundedBefore_of_parametricSplit_components_classical_initialTraceEnergy_before
#print axioms boundedBefore_of_spectralSplit_components_initialTraceEnergy_before
#print axioms boundedBefore_of_spectralSplit_components_classical_initialTraceEnergy_before
#print axioms boundedBefore_of_parametricSplit_initialEndpointData_before
#print axioms boundedBefore_of_parametricSplit_classical_initialEndpointData_before
#print axioms boundedBefore_of_spectralSplit_initialEndpointData_before
#print axioms boundedBefore_of_spectralSplit_classical_initialEndpointData_before
#print axioms boundedBefore_of_parametricSplit_components_initialEndpointData_before
#print axioms boundedBefore_of_parametricSplit_components_classical_initialEndpointData_before
#print axioms boundedBefore_of_spectralSplit_components_initialEndpointData_before
#print axioms boundedBefore_of_spectralSplit_components_classical_initialEndpointData_before

end ShenWork.Paper2.IntervalChiNegH1BridgeInitialWiring
