import ShenWork.Paper2.IntervalChiNegH1InitialContinuity
import ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

/-!
# H¹ initial endpoint wiring

This file threads the split H¹ endpoint data from
`IntervalChiNegH1InitialContinuity` through the downstream scalar-DI and
bounded-before wrappers, replacing the raw `hcont0` carry by deleted-right
initial energy convergence plus zero-slice compatibility.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1AverageWiring
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1InitialContinuity
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1InitialWiring

/-- H¹ scalar regularity from `u_xx` L¹-continuity, explicit RHS integrability,
and the split initial endpoint data. -/
theorem H1ScalarRegularityBefore_of_initialTraceEnergy
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_hcont_and_identityRHSIntegrable
    (H1energy_continuousOn_before_of_uxxL1Cont_initialTraceEnergy
      hsol hUxxL1 htend hcompat)
    hRHS

/-- H¹ scalar regularity from a classical solution, explicit RHS
integrability, and the split initial endpoint data. -/
theorem H1ScalarRegularityBefore_of_classical_initialTraceEnergy
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_initialTraceEnergy
    hsol
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    htend hcompat hRHS

/-- Direct scalar-DI producer using the split initial endpoint data instead of a
raw right-continuity-at-zero hypothesis. -/
theorem H1ScalarDIOnBefore_of_initialTraceEnergy
    {p : CM2Params} {T A B : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX)
    (hBound : H1IdentityRHSBoundBefore p u T A B) :
    H1ScalarDIOnBefore u T A B :=
  H1ScalarDIOnBefore_of_identityRHSBound
    (H1ScalarRegularityBefore_of_initialTraceEnergy
      hsol hUxxL1 htend hcompat hRHS)
    hBound

/-- Direct scalar-DI producer from a classical solution and split initial
endpoint data. -/
theorem H1ScalarDIOnBefore_of_classical_initialTraceEnergy
    {p : CM2Params} {T A B : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX)
    (hBound : H1IdentityRHSBoundBefore p u T A B) :
    H1ScalarDIOnBefore u T A B :=
  H1ScalarDIOnBefore_of_initialTraceEnergy
    hsol
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    htend hcompat hRHS hBound

/-- Paper-positive bounded-before route with the endpoint carry expressed as
deleted-right initial-energy convergence plus zero-slice compatibility. -/
theorem boundedBefore_of_H1identityRHS_initialTraceEnergy
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {A B Ylocal : ℝ}
    (hBound : H1IdentityRHSBoundBefore params u T A B)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hDI : H1ScalarDIOnBefore u T A B :=
    H1ScalarDIOnBefore_of_initialTraceEnergy
      hsol hUxxL1 htend hcompat hRHS hBound
  exact intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local_before
    hbounded ha hu₀ hT hsol htrace hfrontier hDI hlocal

/-- Paper-positive bounded-before route from a classical solution, with the
endpoint carry expressed as deleted-right initial-energy convergence plus
zero-slice compatibility. -/
theorem boundedBefore_of_H1identityRHS_classical_initialTraceEnergy
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {A B Ylocal : ℝ}
    (hBound : H1IdentityRHSBoundBefore params u T A B)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1identityRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    htend hcompat hRHS hBound hlocal

/-- Sup-bound DI variant of the split-endpoint bounded-before route. -/
theorem boundedBefore_of_H1supBoundDI_initialTraceEnergy
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  let A : ℝ := 2 * (-params.χ₀) ^ 2 * V₁ ^ 2 + 2 * L
  let B : ℝ := (-params.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2
  have hBound : H1IdentityRHSBoundBefore params u T A B := by
    simpa [A, B] using H1IdentityRHSBoundBefore_of_supBoundDIData hdata
  exact boundedBefore_of_H1identityRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1 htend hcompat hRHS
    hBound hlocal

/-- Sup-bound DI variant from a classical solution and split endpoint data. -/
theorem boundedBefore_of_H1supBoundDI_classical_initialTraceEnergy
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundDI_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    htend hcompat hRHS hdata hlocal

/-- Square-root sup-bound DI variant of the split-endpoint bounded-before route. -/
theorem boundedBefore_of_H1supBoundSqrtDI_initialTraceEnergy
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundDI_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat hRHS
    (H1SupBoundDIDataBefore_of_sqrtData hdata)
    hlocal

/-- Square-root sup-bound DI variant from a classical solution and split
endpoint data. -/
theorem boundedBefore_of_H1supBoundSqrtDI_classical_initialTraceEnergy
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtDI_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    htend hcompat hRHS hdata hlocal

/-- Combined square-root/RHS package variant of the split-endpoint
bounded-before route. -/
theorem boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtRHSIntegrableBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtDI_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 htend hcompat
    (H1IdentityRHSIntegrableBefore_of_supBoundSqrtRHSData hdata)
    hdata.sqrtData hlocal

/-- Combined square-root/RHS package variant from a classical solution and
split endpoint data. -/
theorem boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (htend : H1InitialTraceEnergyTendsto u₀ u T)
    (hcompat : H1InitialEnergyCompatibleAtZero u₀ u)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtRHSIntegrableBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    (H1UxxL1ContBefore_of_classical_liftChemotaxisDivPhysicalRep hsol)
    htend hcompat hdata hlocal

/-- Bundled-endpoint version of
`H1ScalarRegularityBefore_of_initialTraceEnergy`. -/
theorem H1ScalarRegularityBefore_of_initialEndpointData
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_initialTraceEnergy
    hsol hUxxL1 hinit.tendsto hinit.compatible hRHS

/-- Bundled-endpoint classical version of
`H1ScalarRegularityBefore_of_classical_initialTraceEnergy`. -/
theorem H1ScalarRegularityBefore_of_classical_initialEndpointData
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_classical_initialTraceEnergy
    hsol hinit.tendsto hinit.compatible hRHS

/-- Bundled-endpoint version of
`H1ScalarDIOnBefore_of_initialTraceEnergy`. -/
theorem H1ScalarDIOnBefore_of_initialEndpointData
    {p : CM2Params} {T A B : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX)
    (hBound : H1IdentityRHSBoundBefore p u T A B) :
    H1ScalarDIOnBefore u T A B :=
  H1ScalarDIOnBefore_of_initialTraceEnergy
    hsol hUxxL1 hinit.tendsto hinit.compatible hRHS hBound

/-- Bundled-endpoint classical version of
`H1ScalarDIOnBefore_of_classical_initialTraceEnergy`. -/
theorem H1ScalarDIOnBefore_of_classical_initialEndpointData
    {p : CM2Params} {T A B : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX)
    (hBound : H1IdentityRHSBoundBefore p u T A B) :
    H1ScalarDIOnBefore u T A B :=
  H1ScalarDIOnBefore_of_classical_initialTraceEnergy
    hsol hinit.tendsto hinit.compatible hRHS hBound

/-- Endpoint-data-facing wrapper for the scalar local seed.

The endpoint bundle is not analytically needed once `H1ScalarDIOnBefore` is
available; it is kept here only so route APIs that already carry
`H1InitialEndpointData` can call the seed theorem without changing imports. -/
theorem exists_H1_localSeed_of_scalarDI_initialEndpointData
    {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T A B : ℝ}
    (hT : 0 < T)
    (hDI : H1ScalarDIOnBefore u T A B)
    (_hinit : H1InitialEndpointData u₀ u T) :
    ∃ Ylocal : ℝ,
      ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
        H1energy u τ ≤ Ylocal :=
  exists_H1_localSeed_of_scalarDI_before hT hDI

/-- Bundled-endpoint version of
`boundedBefore_of_H1identityRHS_initialTraceEnergy`. -/
theorem boundedBefore_of_H1identityRHS_initialEndpointData
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {A B Ylocal : ℝ}
    (hBound : H1IdentityRHSBoundBefore params u T A B)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1identityRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hRHS hBound hlocal

/-- Bundled-endpoint classical version of
`boundedBefore_of_H1identityRHS_classical_initialTraceEnergy`. -/
theorem boundedBefore_of_H1identityRHS_classical_initialEndpointData
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {A B Ylocal : ℝ}
    (hBound : H1IdentityRHSBoundBefore params u T A B)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1identityRHS_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hRHS hBound hlocal

/-- Bundled-endpoint version of
`boundedBefore_of_H1supBoundDI_initialTraceEnergy`. -/
theorem boundedBefore_of_H1supBoundDI_initialEndpointData
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundDI_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hRHS hdata hlocal

/-- Bundled-endpoint classical version of
`boundedBefore_of_H1supBoundDI_classical_initialTraceEnergy`. -/
theorem boundedBefore_of_H1supBoundDI_classical_initialEndpointData
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundDI_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hRHS hdata hlocal

/-- Bundled-endpoint version of
`boundedBefore_of_H1supBoundSqrtDI_initialTraceEnergy`. -/
theorem boundedBefore_of_H1supBoundSqrtDI_initialEndpointData
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtDI_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hRHS hdata hlocal

/-- Bundled-endpoint classical version of
`boundedBefore_of_H1supBoundSqrtDI_classical_initialTraceEnergy`. -/
theorem boundedBefore_of_H1supBoundSqrtDI_classical_initialEndpointData
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    (hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtDIDataBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtDI_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hRHS hdata hlocal

/-- Bundled-endpoint version of
`boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy`. -/
theorem boundedBefore_of_H1supBoundSqrtRHS_initialEndpointData
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtRHSIntegrableBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier hUxxL1
    hinit.tendsto hinit.compatible hdata hlocal

/-- Bundled-endpoint classical version of
`boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy`. -/
theorem boundedBefore_of_H1supBoundSqrtRHS_classical_initialEndpointData
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
    {taxisX uvxx reactX : ℝ → ℝ}
    (hinit : H1InitialEndpointData u₀ u T)
    {V₁ V₂ M L Ylocal : ℝ}
    (hdata : H1SupBoundSqrtRHSIntegrableBefore params u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy
    hbounded ha hu₀ hT hsol htrace hfrontier
    hinit.tendsto hinit.compatible hdata hlocal

#print axioms H1ScalarRegularityBefore_of_initialTraceEnergy
#print axioms H1ScalarRegularityBefore_of_classical_initialTraceEnergy
#print axioms H1ScalarDIOnBefore_of_initialTraceEnergy
#print axioms H1ScalarDIOnBefore_of_classical_initialTraceEnergy
#print axioms boundedBefore_of_H1identityRHS_initialTraceEnergy
#print axioms boundedBefore_of_H1identityRHS_classical_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundDI_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundDI_classical_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundSqrtDI_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundSqrtDI_classical_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundSqrtRHS_classical_initialTraceEnergy
#print axioms H1ScalarRegularityBefore_of_initialEndpointData
#print axioms H1ScalarRegularityBefore_of_classical_initialEndpointData
#print axioms H1ScalarDIOnBefore_of_initialEndpointData
#print axioms H1ScalarDIOnBefore_of_classical_initialEndpointData
#print axioms exists_H1_localSeed_of_scalarDI_initialEndpointData
#print axioms boundedBefore_of_H1identityRHS_initialEndpointData
#print axioms boundedBefore_of_H1identityRHS_classical_initialEndpointData
#print axioms boundedBefore_of_H1supBoundDI_initialEndpointData
#print axioms boundedBefore_of_H1supBoundDI_classical_initialEndpointData
#print axioms boundedBefore_of_H1supBoundSqrtDI_initialEndpointData
#print axioms boundedBefore_of_H1supBoundSqrtDI_classical_initialEndpointData
#print axioms boundedBefore_of_H1supBoundSqrtRHS_initialEndpointData
#print axioms boundedBefore_of_H1supBoundSqrtRHS_classical_initialEndpointData

end ShenWork.Paper2.IntervalChiNegH1InitialWiring
