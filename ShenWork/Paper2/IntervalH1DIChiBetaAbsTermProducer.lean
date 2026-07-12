import ShenWork.Paper2.IntervalH1DIChiBetaAbsorption
import ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
import ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
import ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
import ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
import ShenWork.Paper2.IntervalChiNegH1InitialWiring
import ShenWork.Paper2.IntervalChiNegH1DerivativeWindowProducer

/-!
# Positive-sensitivity physical H¹ absolute-term producer

This file connects the sign-agnostic physical resolver estimates to the
`|χ₀|` H¹ absorption theorem.  The strict-positive-time route uses only the
regularity contained in a classical solution.  The closed-zero route records
the genuinely additional initial endpoint and zero-window integrability data
needed by `H1ScalarRegularityBefore`.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1AverageWiring
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1DerivativeWindowProducer
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1InitialContinuity
open ShenWork.Paper2.IntervalChiNegH1InitialWiring
open ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
open ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
open ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer

noncomputable section

namespace ShenWork.Paper2.IntervalH1DIChiBetaAbsTermProducer

/-- A classical solution supplies the strict physical identity and component
continuity.  Together with the explicit zero-window majorant, these give the
full RHS-integrability package, with no sign condition on `p.χ₀`. -/
theorem H1PhysicalRHSIntegrableBefore_of_classical_initialMajorant
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hMaj : H1PhysicalRHSInitialWindowMajorantBefore p u v T) :
    H1IdentityRHSIntegrableBefore p u T
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialMajorant
    (H1PhysicalRHSIdentityBefore_of_classicalSolution hsol).identity
    (H1PhysicalRHSComponentsContinuousStrictBefore_of_classicalSolution
      hsol).components
    hMaj.majorant

/-- Closed-zero H¹ scalar regularity from the classical positive-time
regularity and the exact two endpoint carries that are not contained in
`IsPaper2ClassicalSolution`: initial H¹ convergence and zero-window RHS
integrability. -/
theorem H1ScalarRegularityBefore_of_classical_physical_initialData
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hinit : H1InitialEndpointData u₀ u T)
    (hMaj : H1PhysicalRHSInitialWindowMajorantBefore p u v T) :
    H1ScalarRegularityBefore u T :=
  H1ScalarRegularityBefore_of_classical_initialEndpointData
    hsol hinit
    (H1PhysicalRHSIntegrableBefore_of_classical_initialMajorant hsol hMaj)

/-- The three physical absolute-term bounds plus classical positive-time
regularity produce the strict scalar H¹ differential inequality.  This is the
native route when no zero-time derivative integrability is available. -/
theorem H1ScalarDIOnStrictBefore_of_classical_absTermBounds
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hAbs : H1PhysicalRHSAbsTermBoundsBefore p u v T V₁ V₂ M L) :
    H1ScalarDIOnStrictBefore u T
      (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L)
      ((-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2) := by
  have hId := H1PhysicalRHSIdentityBefore_of_classicalSolution hsol
  have hStrict :=
    H1PhysicalRHSComponentsContinuousStrictBefore_of_classicalSolution hsol
  have hBound :
      H1IdentityRHSBoundBefore p u T
        (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L)
        ((-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2) :=
    H1IdentityRHSBoundBefore_of_supBoundDIDataAbs
      (H1SupBoundDIDataAbsBefore_of_absTermBounds
        hAbs.hV1 hAbs.hV2 hAbs.hM hAbs.hL
        (fun τ hτ0 hτT => hId.identity τ ⟨hτ0, hτT⟩)
        (fun τ hτ0 hτT => hAbs.taxis_abs τ ⟨hτ0, hτT⟩)
        (fun τ hτ0 hτT => hAbs.uvxx_abs τ ⟨hτ0, hτT⟩)
        (fun τ hτ0 hτT => hAbs.react_bound τ ⟨hτ0, hτT⟩))
  refine
    { hA := hBound.hA
      hB := hBound.hB
      hcont := ?_
      hderivInt := ?_
      hhasDerivRight := ?_
      hDI := ?_ }
  · intro a b ha _hab hbT τ hτ
    have hτIoo : τ ∈ Set.Ioo (0 : ℝ) T :=
      ⟨lt_of_lt_of_le ha hτ.1, lt_of_le_of_lt hτ.2 hbT⟩
    exact (hId.identity τ hτIoo).continuousAt.continuousWithinAt
  · intro a b ha hab hbT
    exact
      H1EnergyDerivativePositiveStartWindowIntegrableBefore_of_componentsStrictBefore
        hId.identity hStrict.components ha hab hbT
  · intro a b r ha _hab hbT hr
    have hr0 : 0 < r := lt_trans ha hr.1
    have hrT : r < T := lt_trans hr.2 hbT
    rcases hBound.bound r hr0 hrT with
      ⟨taxisX, uvxx, reactX, hEnergy, _hrhs⟩
    unfold H1EnergyIdentity at hEnergy
    have hderiv_eq :
        deriv (H1energy u) r =
          (-(lapL2sq u r) + (-p.χ₀) * taxisX +
            (-p.χ₀) * uvxx + reactX) :=
      hEnergy.deriv
    simpa [hderiv_eq] using hEnergy.hasDerivWithinAt (s := Set.Ioi r)
  · intro r hr0 hrT
    rcases hBound.bound r hr0 hrT with
      ⟨taxisX, uvxx, reactX, hEnergy, hrhs⟩
    unfold H1EnergyIdentity at hEnergy
    have hderiv_eq :
        deriv (H1energy u) r =
          (-(lapL2sq u r) + (-p.χ₀) * taxisX +
            (-p.χ₀) * uvxx + reactX) :=
      hEnergy.deriv
    calc
      deriv (H1energy u) r =
          (-(lapL2sq u r) + (-p.χ₀) * taxisX +
            (-p.χ₀) * uvxx + reactX) := hderiv_eq
      _ ≤ (2 * (-p.χ₀) ^ 2 * V₁ ^ 2 + 2 * L) * H1energy u r +
          ((-p.χ₀) ^ 2 * M ^ 2 * V₂ ^ 2) := hrhs

/-- Closed-zero capstone wrapper.  Resolver/core sup data produce all three
absolute physical terms; the physical identity and scalar regularity are
assembled internally before calling
`intervalDomain_boundedBefore_of_absTermBounds_and_frontiers`. -/
theorem intervalDomain_boundedBefore_of_classical_resolverSup_absTermBounds
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    {V₁ V₂ M L Ylocal : ℝ}
    (hbounded : IntervalDomainBoundednessHyp p)
    (ha : 0 < p.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    (hinit : H1InitialEndpointData u₀ u T)
    (hMaj : H1PhysicalRHSInitialWindowMajorantBefore p u v T)
    (hL : p.a ≤ L)
    (hres : H1PhysicalChemResolverSupBefore p u v T V₁ V₂ M)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAbs :=
    H1PhysicalRHSAbsTermBoundsBefore_of_classical_resolverSup
      (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M) (L := L)
      (u := u) (v := v) hsol hL hres
  have hId := H1PhysicalRHSIdentityBefore_of_classicalSolution hsol
  have hreg :=
    H1ScalarRegularityBefore_of_classical_physical_initialData
      hsol hinit hMaj
  exact
    intervalDomain_boundedBefore_of_absTermBounds_and_frontiers
      hbounded ha hu₀ hT hsol htrace hfrontier hreg
      hAbs.hV1 hAbs.hV2 hAbs.hM hAbs.hL
      (fun τ hτ0 hτT => hId.identity τ ⟨hτ0, hτT⟩)
      (fun τ hτ0 hτT => hAbs.taxis_abs τ ⟨hτ0, hτT⟩)
      (fun τ hτ0 hτT => hAbs.uvxx_abs τ ⟨hτ0, hτT⟩)
      (fun τ hτ0 hτT => hAbs.react_bound τ ⟨hτ0, hτT⟩)
      hlocal

/-- Strict-positive-time capstone for the same resolver data.  It avoids any
artificial zero-time regularity assertion and consumes the existing local H¹
seed only where the solution is defined. -/
theorem intervalDomain_boundedBefore_of_classical_resolverSup_absTermBounds_strict
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    {V₁ V₂ M L Ylocal : ℝ}
    (hbounded : IntervalDomainBoundednessHyp p)
    (ha : 0 < p.a)
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀)
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hfrontier : IntervalDomainL2SeedRegularityFrontier T u)
    (hL : p.a ≤ L)
    (hres : H1PhysicalChemResolverSupBefore p u v T V₁ V₂ M)
    (hlocal : ∀ τ, τ ∈ Set.Ioc (0 : ℝ) 1 → τ < T →
      H1energy u τ ≤ Ylocal) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hAbs :=
    H1PhysicalRHSAbsTermBoundsBefore_of_classical_resolverSup
      (p := p) (T := T) (V₁ := V₁) (V₂ := V₂) (M := M) (L := L)
      (u := u) (v := v) hsol hL hres
  exact
    intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_strict_local_before
      hbounded ha hu₀ hT hsol htrace hfrontier
      (H1ScalarDIOnStrictBefore_of_classical_absTermBounds hsol hAbs)
      hlocal

#print axioms H1PhysicalRHSIntegrableBefore_of_classical_initialMajorant
#print axioms H1ScalarRegularityBefore_of_classical_physical_initialData
#print axioms H1ScalarDIOnStrictBefore_of_classical_absTermBounds
#print axioms intervalDomain_boundedBefore_of_classical_resolverSup_absTermBounds
#print axioms
  intervalDomain_boundedBefore_of_classical_resolverSup_absTermBounds_strict

end ShenWork.Paper2.IntervalH1DIChiBetaAbsTermProducer
