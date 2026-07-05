import ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS
import ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars

/-!
# Physical H¹ RHS strict/initial route

This file connects the physical H¹ RHS scalar triple to the route-C
strict-positive-time/zero-start split.  The new route asks for strict component
continuity away from `0` plus a near-zero L¹ majorant for the assembled physical
RHS; it does not require zero-start component continuity.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge
open ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeProducer
open ShenWork.Paper2.IntervalChiNegH1InitialDerivativeRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS

/-- Strict-positive-time component continuity plus a zero-start RHS majorant
gives the existing full explicit-RHS integrability package. -/
theorem H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialWindow
    hId hStrict
    (H1IdentityRHSInitialWindowIntegrableBefore_of_majorant hMaj)

/-- Pointwise identity, square-root bounds, strict-positive-time component
continuity, and a zero-start RHS majorant give the combined sqrt/RHS package. -/
theorem
    H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsStrict_initialMajorant
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hb : H1SqrtTermBoundsBefore p u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hMaj : H1IdentityRHSInitialWindowMajorantBefore p u T
      taxisX uvxx reactX) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_RHSInt
    hId hb
    (H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
      hId hStrict hMaj).rhs_intervalIntegrable

/-- Strict-positive-time component continuity for the concrete physical scalar
triple. -/
structure H1PhysicalRHSComponentsContinuousStrictBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop where
  components : H1IdentityRHSComponentsContinuousStrictBefore p u T
    (H1PhysicalTaxisX p u v)
    (H1PhysicalUvxxX p u v)
    (H1PhysicalReactX p u)

/-- Near-zero L¹ majorant for the assembled concrete physical H¹ RHS. -/
structure H1PhysicalRHSInitialWindowMajorantBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop where
  majorant : H1IdentityRHSInitialWindowMajorantBefore p u T
    (H1PhysicalTaxisX p u v)
    (H1PhysicalUvxxX p u v)
    (H1PhysicalReactX p u)

/-- Route package for the concrete physical scalar triple with strict
positive-time component continuity and a zero-start assembled-RHS majorant. -/
structure H1PhysicalRHSStrictInitialRouteBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  identity : H1PhysicalRHSIdentityBefore p u v T
  bounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L
  componentsStrict : H1PhysicalRHSComponentsContinuousStrictBefore p u v T
  initialMajorant : H1PhysicalRHSInitialWindowMajorantBefore p u v T

/-- The physical initial majorant gives the generic assembled-RHS initial
majorant for the same concrete scalar triple. -/
theorem H1IdentityRHSInitialWindowMajorantBefore_of_physicalInitialMajorant
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSInitialWindowMajorantBefore p u v T) :
    H1IdentityRHSInitialWindowMajorantBefore p u T
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  h.majorant

/-- The physical initial majorant gives initial-window integrability of the
assembled physical H¹ RHS. -/
theorem H1IdentityRHSInitialWindowIntegrableBefore_of_physicalInitialMajorant
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSInitialWindowMajorantBefore p u v T) :
    H1IdentityRHSInitialWindowIntegrableBefore p u T
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1IdentityRHSInitialWindowIntegrableBefore_of_majorant h.majorant

/-- A physical identity plus a physical initial RHS majorant gives the scalar
zero-start H¹ derivative-integrability input. -/
theorem H1EnergyDerivativeInitialWindowIntegrableBefore_of_physicalInitialMajorant
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hId : H1PhysicalRHSIdentityBefore p u v T)
    (hMaj : H1PhysicalRHSInitialWindowMajorantBefore p u v T) :
    H1EnergyDerivativeInitialWindowIntegrableBefore u T :=
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_identityRHSMajorant
    hId.identity hMaj.majorant

/-- The strict/initial physical route supplies full explicit-RHS integrability
for the concrete scalar triple. -/
theorem H1IdentityRHSIntegrableBefore_of_physicalStrictInitialRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L) :
    H1IdentityRHSIntegrableBefore p u T
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
    h.identity.identity
    h.componentsStrict.components
    h.initialMajorant.majorant

/-- The strict/initial physical route supplies the square-root DI package. -/
theorem H1SupBoundSqrtDIDataBefore_of_physicalStrictInitialRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L) :
    H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1SupBoundSqrtDIDataBefore_of_identity_and_sqrtBounds
    h.identity.identity
    h.bounds.bounds

/-- The strict/initial physical route supplies the combined sqrt/RHS package
without requiring zero-start component continuity. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_physicalStrictInitialRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSStrictInitialRouteBefore p u v T V₁ V₂ M L) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsStrict_initialMajorant
    h.identity.identity
    h.bounds.bounds
    h.componentsStrict.components
    h.initialMajorant.majorant

/-- Bounded-before wrapper from the concrete physical strict/initial route and
the remaining scalar regularity inputs. -/
theorem intervalDomain_boundedBefore_of_physicalStrictInitialRoute_before
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
    (hUxxL1 : H1UxxL1ContBefore u T)
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    {V₁ V₂ M L : ℝ}
    (h : H1PhysicalRHSStrictInitialRouteBefore params u v T V₁ V₂ M L) :
    IsPaper2BoundedBefore intervalDomain T u :=
  intervalDomain_boundedBefore_of_H1supBoundSqrtRHS_before
    hbounded ha hu₀ hT hsol htrace hfrontier
    hUxxL1 hcont0
    (H1SupBoundSqrtRHSIntegrableBefore_of_physicalStrictInitialRoute h)

#print axioms
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
#print axioms
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsStrict_initialMajorant
#print axioms
  H1IdentityRHSInitialWindowMajorantBefore_of_physicalInitialMajorant
#print axioms
  H1IdentityRHSInitialWindowIntegrableBefore_of_physicalInitialMajorant
#print axioms
  H1EnergyDerivativeInitialWindowIntegrableBefore_of_physicalInitialMajorant
#print axioms H1IdentityRHSIntegrableBefore_of_physicalStrictInitialRoute
#print axioms H1SupBoundSqrtDIDataBefore_of_physicalStrictInitialRoute
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_physicalStrictInitialRoute
#print axioms intervalDomain_boundedBefore_of_physicalStrictInitialRoute_before

end ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
