import ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
import ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer

/-!
# Route-C physical H¹ identity interface

This file connects the finite-difference H¹ energy derivative producer to the
concrete physical RHS scalar triple, while keeping the actual substitution
equality as an explicit frontier.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC

/-- Exact substitution frontier for the Route-C derivative value into the
concrete physical scalar triple. -/
def H1PhysicalRHSRouteCSubstitutionBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop :=
  ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    -(∫ x in (0 : ℝ)..1,
        liftDeriv2 u τ x * liftTimeDeriv u τ x) =
      H1IdentityRHSValue p u
        (H1PhysicalTaxisX p u v)
        (H1PhysicalUvxxX p u v)
        (H1PhysicalReactX p u) τ

/-- Route-C finite-difference derivative plus the exact physical substitution
gives the concrete physical H¹ identity package. -/
theorem H1PhysicalRHSIdentityBefore_of_classical_uxxL1Cont_routeCSubstitution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hUxx : H1UxxL1ContBefore u T)
    (hsub : H1PhysicalRHSRouteCSubstitutionBefore p u v T) :
    H1PhysicalRHSIdentityBefore p u v T := by
  refine ⟨?_⟩
  intro τ hτ
  have hUxxτ : ∀ ε > 0, ∃ δ > 0,
      ∀ s, |s - τ| < δ → s ∈ Set.Ioo (0 : ℝ) T →
        ∫ x in (0 : ℝ)..1,
          ‖liftDeriv2 u s x - liftDeriv2 u τ x‖ ≤ ε := by
    simpa [H1UxxL1ContBefore, liftDeriv2] using hUxx τ hτ.1 hτ.2
  have hder :
      HasDerivAt (H1energy u)
        (-(∫ x in (0 : ℝ)..1,
            liftDeriv2 u τ x * liftTimeDeriv u τ x)) τ :=
    H1energy_hasDerivAt_of_uxxL1Cont hsol hτ hUxxτ
  have hsub' :
      -(∫ x in (0 : ℝ)..1,
          liftDeriv2 u τ x * liftTimeDeriv u τ x) =
        -(lapL2sq u τ) +
          (-p.χ₀) * H1PhysicalTaxisX p u v τ +
          (-p.χ₀) * H1PhysicalUvxxX p u v τ +
          H1PhysicalReactX p u τ := by
    simpa [H1IdentityRHSValue] using hsub τ hτ
  unfold H1EnergyIdentity
  rw [← hsub']
  exact hder

#print axioms
  H1PhysicalRHSIdentityBefore_of_classical_uxxL1Cont_routeCSubstitution

end ShenWork.Paper2.IntervalChiNegH1PhysicalIdentityRouteC
