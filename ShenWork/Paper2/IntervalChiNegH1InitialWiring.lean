import ShenWork.Paper2.IntervalChiNegH1InitialContinuity
import ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer

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

#print axioms H1ScalarRegularityBefore_of_initialTraceEnergy
#print axioms H1ScalarDIOnBefore_of_initialTraceEnergy
#print axioms boundedBefore_of_H1identityRHS_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundDI_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundSqrtDI_initialTraceEnergy
#print axioms boundedBefore_of_H1supBoundSqrtRHS_initialTraceEnergy

end ShenWork.Paper2.IntervalChiNegH1InitialWiring
