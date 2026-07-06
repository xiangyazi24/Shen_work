import ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds
import ShenWork.Paper2.IntervalDomainResolverSupQuantitative

/-!
# Source producers for physical H¹ chem resolver sup data

This file lowers a smaller source-facing residual to the resolver/core package
used by the physical H¹ sqrt route.  It does not produce uniform before-`T`
constants from classical regularity alone.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
open ShenWork.Paper2.IntervalChiNegH1PhysicalChemSqrtBounds

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer

/-- Quantitative resolver-gradient cap obtained from a fixed pointwise upper
bound on `u`. -/
abbrev H1PhysicalChemResolverGradCap (p : CM2Params) (M : ℝ) : ℝ :=
  Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ))

private theorem H1PhysicalChemResolverGradCap_nonneg
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ H1PhysicalChemResolverGradCap p M := by
  unfold H1PhysicalChemResolverGradCap
  exact
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM p.γ)))

/-- Smaller source-facing residual for the physical H¹ chem route: a fixed
before-`T` pointwise upper bound on `u`, plus the remaining exact uvxx-core
bound.  The resolver-gradient bound is produced quantitatively from the `u`
upper bound. -/
structure H1PhysicalChemUpperCoreBoundsBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T M V₂ : ℝ) : Prop where
  hM : 0 ≤ M
  hV2 : 0 ≤ V₂
  u_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      intervalDomainLift (u τ) x ≤ M
  uvxx_core_le : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
      |(p.μ * intervalDomainLift (v τ) x -
          p.ν * (intervalDomainLift (u τ) x) ^ p.γ) /
          (1 + intervalDomainLift (v τ) x) ^ p.β -
        p.β * (deriv (intervalDomainLift (v τ)) x) ^ 2 /
          (1 + intervalDomainLift (v τ) x) ^ (p.β + 1)| ≤ V₂

/-- Uniform pointwise upper control of `u` plus the exact uvxx-core source bound
produces the resolver/core package used by the physical H¹ sqrt route. -/
theorem H1PhysicalChemResolverSupBefore_of_upperCore
    {p : CM2Params} {T M V₂ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (h : H1PhysicalChemUpperCoreBoundsBefore p u v T M V₂) :
    H1PhysicalChemResolverSupBefore p u v T
      (H1PhysicalChemResolverGradCap p M) V₂ M := by
  refine
    { hV1 := H1PhysicalChemResolverGradCap_nonneg p h.hM
      hV2 := h.hV2
      hM := h.hM
      u_abs_le := ?_
      resolver_grad_le := ?_
      uvxx_core_le := h.uvxx_core_le }
  · intro τ hτ x hx
    have hpos : 0 < intervalDomainLift (u τ) x :=
      solution_lift_pos
        (p := p) (T := T) (u := u) (v := v) hsol hτ x hx
    rw [abs_of_pos hpos]
    exact h.u_le τ hτ x hx
  · intro τ hτ x hx
    simpa [H1PhysicalChemResolverGradCap] using
      resolverGrad_sup_le_of_ub
        (p := p) (T := T) (u := u) (v := v)
        hsol (τ := τ) (M := M) hτ (h.u_le τ hτ) (x := x) hx

/-- Direct full physical H¹ sqrt wrapper from the smaller source-facing
upper/core package. -/
theorem H1PhysicalRHSSqrtBoundsBefore_of_classical_upperCore
    {p : CM2Params} {T M V₂ L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hchi : 0 ≤ -p.χ₀)
    (hL : p.a ≤ L)
    (h : H1PhysicalChemUpperCoreBoundsBefore p u v T M V₂) :
    H1PhysicalRHSSqrtBoundsBefore p u v T
      (H1PhysicalChemResolverGradCap p M) V₂ M L :=
  H1PhysicalRHSSqrtBoundsBefore_of_classical_resolverSup
    (p := p) (T := T)
    (V₁ := H1PhysicalChemResolverGradCap p M) (V₂ := V₂)
    (M := M) (L := L) (u := u) (v := v) hsol hchi hL
    (H1PhysicalChemResolverSupBefore_of_upperCore
      (p := p) (T := T) (M := M) (V₂ := V₂)
      (u := u) (v := v) hsol h)

#print axioms H1PhysicalChemResolverSupBefore_of_upperCore
#print axioms H1PhysicalRHSSqrtBoundsBefore_of_classical_upperCore

end ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
