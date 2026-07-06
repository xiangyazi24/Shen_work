import ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
import ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
import ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
import ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

/-!
# Physical H¹ strict/initial route from independent bounded-before data

This file only assembles already-proved producers.  The `IsPaper2BoundedBefore`
input must come from an upstream source independent of the physical H¹ route.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
open ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
open ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
open ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
open ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalBoundedBeforeRoute

/-- Classical solution plus an independent finite-horizon bounded-before source
supplies the concrete physical strict/initial route with a Young zero-window
majorant.  The physical identity and square-root bounds are produced internally. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_youngScalarZero
    {p : CM2Params} {T L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u)
    (hYoung : H1PhysicalRHSYoungScalarZeroMajorantsBefore p u v T) :
    ∃ M, H1PhysicalRHSStrictInitialRouteBefore p u v T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M L := by
  rcases
    H1PhysicalRHSSqrtBoundsBefore_of_classical_boundedBefore_valueGrad
      (p := p) (T := T) (L := L) (u := u) (v := v)
      hsol hchi hL hbounded with
    ⟨M, hBounds⟩
  refine ⟨M, ?_⟩
  exact
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_youngScalarZero
      (p := p) (T := T)
      (V₁ := H1PhysicalChemResolverGradCap p M)
      (V₂ := H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      (M := M) (L := L) (u := u) (v := v)
      hsol
      (H1PhysicalRHSIdentityBefore_of_classicalSolution hsol)
      hBounds
      hYoung

/-- Component-square zero-window version of the bounded-before physical
strict/initial route. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_componentSquareZero
    {p : CM2Params} {T L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u)
    (hSq : H1PhysicalRHSComponentSquareZeroDataBefore p u v T) :
    ∃ M, H1PhysicalRHSStrictInitialRouteBefore p u v T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M L :=
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_youngScalarZero
    (p := p) (T := T) (L := L) (u := u) (v := v)
    hsol hchi hL hbounded
    (H1PhysicalRHSYoungScalarZeroMajorantsBefore_of_componentSquareZeroData hSq)

/-- Zero-start primitive-data version of the bounded-before physical
strict/initial route.  This keeps the zero-start primitive package as the
source-side initial-window input, while producing identity and sqrt bounds
internally from classicality and the independent bounded-before source. -/
theorem
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_zeroStartPrimitiveData
    {p : CM2Params} {T δ L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (hbounded : IsPaper2BoundedBefore intervalDomain T u)
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    ∃ M, H1PhysicalRHSStrictInitialRouteBefore p u v T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M L := by
  rcases
    H1PhysicalRHSSqrtBoundsBefore_of_classical_boundedBefore_valueGrad
      (p := p) (T := T) (L := L) (u := u) (v := v)
      hsol hchi hL hbounded with
    ⟨M, hBounds⟩
  refine ⟨M, ?_⟩
  exact
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_zeroStartPrimitiveData
      (p := p) (T := T) (δ := δ)
      (V₁ := H1PhysicalChemResolverGradCap p M)
      (V₂ := H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      (M := M) (L := L) (u := u) (v := v)
      hsol H
      (H1PhysicalRHSIdentityBefore_of_classicalSolution hsol)
      hBounds
      hδ_pos hδ_before

#print axioms H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_youngScalarZero
#print axioms H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_componentSquareZero
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_zeroStartPrimitiveData

end ShenWork.Paper2.IntervalChiNegH1PhysicalBoundedBeforeRoute
