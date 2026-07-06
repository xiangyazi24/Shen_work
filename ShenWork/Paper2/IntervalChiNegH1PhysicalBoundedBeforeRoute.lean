import ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
import ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
import ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
import ShenWork.Paper2.IntervalChiNegH1ZeroStartConstantPrimitiveData
import ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
import ShenWork.Paper2.IntervalDomainGlobalWellposed

/-!
# Physical H¹ strict/initial route from independent bounded-before data

This file only assembles already-proved producers.  The `IsPaper2BoundedBefore`
input must come from an upstream source independent of the physical H¹ route.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
open ShenWork.Paper2.IntervalChiNegH1PhysicalInitialRHS
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
open ShenWork.Paper2.IntervalChiNegH1PhysicalYoungSpatial
open ShenWork.Paper2.IntervalChiNegH1PhysicalClassicalContinuity
open ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
open ShenWork.Paper2.IntervalChiNegH1ZeroStartComponents
open ShenWork.Paper2.IntervalDomainGlobalWellposed

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

/-- Nonminimal negative-sensitivity specialization: the independent
bounded-before source is the corrected initial-approach sup-norm bound from
Lemma 3.1. -/
theorem
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_nonminimal_zeroStartPrimitiveData
    (p : CM2Params)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T δ : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    ∃ M, H1PhysicalRHSStrictInitialRouteBefore p u v T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M p.a := by
  have hbounded : IsPaper2BoundedBefore intervalDomain T u :=
    boundedBefore_nonminimal_of_corrected_initial_approach
      p hboundedInitial hχ ha hb hu₀ hT hsol htrace
  exact
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_zeroStartPrimitiveData
      (p := p) (T := T) (δ := δ) (L := p.a) (u := u) (v := v)
      hsol (by linarith) le_rfl hbounded H hδ_pos hδ_before

/-- Minimal negative-sensitivity specialization: the independent bounded-before
source is the corrected initial-approach sup-norm bound in the zero-reaction
branch. -/
theorem
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_minimal_zeroStartPrimitiveData
    (p : CM2Params)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T δ : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (H : H1ZeroStartPhysicalPrimitiveDataBefore p u v T)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    ∃ M, H1PhysicalRHSStrictInitialRouteBefore p u v T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M 0 := by
  have hbounded : IsPaper2BoundedBefore intervalDomain T u :=
    boundedBefore_minimal_of_corrected_initial_approach
      p hboundedInitial hχ ha hb hu₀ hT hsol htrace
  exact
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_zeroStartPrimitiveData
      (p := p) (T := T) (δ := δ) (L := 0) (u := u) (v := v)
      hsol (by linarith) (by simp [ha]) hbounded H hδ_pos hδ_before

/-- Constant nonminimal equilibrium route.  This packages the existing constant
classical solution, constant initial trace, and constant zero-start primitive
data into the negative-sensitivity physical route. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_const_equilibrium
    (p : CM2Params)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    {T δ : ℝ} (hT : 0 < T)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    ∃ M, H1PhysicalRHSStrictInitialRouteBefore p
      (fun _ (_ : intervalDomainPoint) => (p.a / p.b) ^ (1 / p.α))
      (fun _ (_ : intervalDomainPoint) =>
        ellipticV p ((p.a / p.b) ^ (1 / p.α)))
      T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M p.a := by
  exact
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_nonminimal_zeroStartPrimitiveData
      (p := p) hboundedInitial hχ ha hb
      (u₀ := constOnInterval ((p.a / p.b) ^ (1 / p.α)))
      (constOnInterval_pos (equilibrium_pos p ha hb))
      (hT := hT)
      ((equilibrium_isPaper2ClassicalSolution p ha hb) T hT)
      (constantSolution_initialTrace ((p.a / p.b) ^ (1 / p.α)))
      (H1ZeroStartPhysicalPrimitiveDataBefore_const_equilibrium
        (p := p) ha hb hT)
      hδ_pos hδ_before

/-- Constant minimal zero-reaction route.  This packages the existing constant
classical solution, constant initial trace, and constant zero-start primitive
data into the negative-sensitivity physical route. -/
theorem H1PhysicalRHSStrictInitialRouteBefore_const_zeroReaction
    (p : CM2Params)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hχ : p.χ₀ ≤ 0) (ha : p.a = 0) (hb : p.b = 0)
    {c T δ : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hδ_pos : 0 < δ) (hδ_before : δ < T) :
    ∃ M, H1PhysicalRHSStrictInitialRouteBefore p
      (fun _ (_ : intervalDomainPoint) => c)
      (fun _ (_ : intervalDomainPoint) => ellipticV p c)
      T
      (H1PhysicalChemResolverGradCap p M)
      (H1PhysicalChemUvxxCoreSupConstant p M
        (H1PhysicalChemResolverValueCap p M)
        (H1PhysicalChemResolverGradCap p M))
      M 0 := by
  exact
    H1PhysicalRHSStrictInitialRouteBefore_of_classical_minimal_zeroStartPrimitiveData
      (p := p) hboundedInitial hχ ha hb
      (u₀ := constOnInterval c)
      (constOnInterval_pos hc)
      (hT := hT)
      ((zeroReaction_isPaper2ClassicalSolution p ha hb c hc) T hT)
      (constantSolution_initialTrace c)
      (H1ZeroStartPhysicalPrimitiveDataBefore_const_zeroReaction
        (p := p) ha hb hc hT)
      hδ_pos hδ_before

#print axioms H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_youngScalarZero
#print axioms H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_componentSquareZero
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_boundedBefore_zeroStartPrimitiveData
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_nonminimal_zeroStartPrimitiveData
#print axioms
  H1PhysicalRHSStrictInitialRouteBefore_of_classical_minimal_zeroStartPrimitiveData
#print axioms H1PhysicalRHSStrictInitialRouteBefore_const_equilibrium
#print axioms H1PhysicalRHSStrictInitialRouteBefore_const_zeroReaction

end ShenWork.Paper2.IntervalChiNegH1PhysicalBoundedBeforeRoute
