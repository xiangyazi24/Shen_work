import ShenWork.Paper2.IntervalChiNegH1InitialWiring
import ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
import ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC

/-!
# Physical H¹ exit wrappers

This file contains only route-level wrappers from the physical strict/initial
H¹ package to bounded-before endpoints.  It does not prove the physical
identity, square-root estimates, or zero-start primitive regularity.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1InitialContinuity
open ShenWork.Paper2.IntervalChiNegH1InitialWiring
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalExit

/-- Endpoint-data bounded-before wrapper from an already assembled physical
strict/initial route.  This is the route-facing exit point: upstream files may
produce the strict route by any non-circular source, while this theorem only
feeds it into the scalar H¹ bounded-before machinery. -/
theorem boundedBefore_of_physicalStrictInitialRoute_initialEndpointData_before
    {params : CM2Params} {T V₁ V₂ M L : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    (hinit : H1InitialEndpointData u₀ u T)
    (hStrict : H1PhysicalRHSStrictInitialRouteBefore params u v T V₁ V₂ M L) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hdata :
      H1SupBoundSqrtRHSIntegrableBefore params u T V₁ V₂ M L
        (H1PhysicalTaxisX params u v)
        (H1PhysicalUvxxX params u v)
        (H1PhysicalReactX params u) :=
    H1SupBoundSqrtRHSIntegrableBefore_of_physicalStrictInitialRoute hStrict
  exact
    boundedBefore_of_H1supBoundSqrtRHS_classical_initialEndpointData_before
      (params := params) (T := T) (u₀ := u₀) (u := u) (v := v)
      (taxisX := H1PhysicalTaxisX params u v)
      (uvxx := H1PhysicalUvxxX params u v)
      (reactX := H1PhysicalReactX params u)
      hbounded ha hu₀ hT hsol htrace hfrontier hinit hdata

#print axioms boundedBefore_of_physicalStrictInitialRoute_initialEndpointData_before

/-- Endpoint-data bounded-before wrapper for the physical H¹ route.

This composes the Task104 strict/initial route with the existing initial
endpoint-data bounded-before theorem.  The analytic frontiers remain explicit:
the physical identity, square-root bounds, zero-start primitive data, initial
endpoint data, and a positive zero window. -/
theorem boundedBefore_of_physical_classical_zeroStartPrimitiveData_initialEndpointData_before
    {params : CM2Params} {T δ V₁ V₂ M L : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    (hinit : H1InitialEndpointData u₀ u T)
    (H : H1ZeroStartPhysicalPrimitiveDataBefore params u v T)
    (hId : H1PhysicalRHSIdentityBefore params u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore params u v T V₁ V₂ M L)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hStrict :
      H1PhysicalRHSStrictInitialRouteBefore params u v T V₁ V₂ M L :=
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_zeroStartPrimitiveData
      (p := params) (T := T) (δ := δ)
      (V₁ := V₁) (V₂ := V₂) (M := M) (L := L)
      (u := u) (v := v)
      hsol H hId hBounds hδ_pos hδ_before
  exact
    boundedBefore_of_physicalStrictInitialRoute_initialEndpointData_before
      hbounded ha hu₀ hT hsol htrace hfrontier hinit hStrict

#print axioms
  boundedBefore_of_physical_classical_zeroStartPrimitiveData_initialEndpointData_before

/-- Endpoint-data bounded-before wrapper after the physical identity has been
closed from the classical solution.  The remaining explicit analytic frontiers
are the zero-start primitive data and square-root bounds. -/
theorem
    boundedBefore_of_physical_classical_zeroStart_identityClosed_before
    {params : CM2Params} {T δ V₁ V₂ M L : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hbounded : IntervalDomainBoundednessHyp params)
    (ha : 0 < params.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    (hinit : H1InitialEndpointData u₀ u T)
    (H : H1ZeroStartPhysicalPrimitiveDataBefore params u v T)
    (hBounds : H1PhysicalRHSSqrtBoundsBefore params u v T V₁ V₂ M L)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    IsPaper2BoundedBefore intervalDomain T u :=
  boundedBefore_of_physical_classical_zeroStartPrimitiveData_initialEndpointData_before
    (params := params) (T := T) (δ := δ)
    (V₁ := V₁) (V₂ := V₂) (M := M) (L := L)
    (u₀ := u₀) (u := u) (v := v)
    hbounded ha hu₀ hT hsol htrace hfrontier hinit H
    (H1PhysicalRHSIdentityBefore_of_classicalSolution hsol)
    hBounds hδ_pos hδ_before

#print axioms
  boundedBefore_of_physical_classical_zeroStart_identityClosed_before

end ShenWork.Paper2.IntervalChiNegH1PhysicalExit
