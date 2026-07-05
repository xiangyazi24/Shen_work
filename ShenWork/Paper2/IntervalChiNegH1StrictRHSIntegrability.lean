import ShenWork.Paper2.IntervalChiNegH1Bridge

/-!
# Strict-time H¹ RHS integrability bridge

This file keeps the route-C near-zero input at the weakest assembled-RHS level:
strict-positive-time component continuity supplies positive-left-endpoint
windows, while initial-window RHS integrability supplies windows starting at
zero.  No zero-start `lapL2sq` continuity is inferred here.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability

/-- Initial-window integrability of the assembled explicit H¹ identity RHS.

This is intentionally weaker than zero-start component continuity and does not
assert any zero-time `lapL2sq` trace. -/
def H1IdentityRHSInitialWindowIntegrableBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) : Prop :=
  ∀ {b : ℝ}, 0 ≤ b → b < T →
    IntervalIntegrable
      (H1IdentityRHSValue p u taxisX uvxx reactX) volume (0 : ℝ) b

/-- Strict positive-time component continuity plus explicit zero-window RHS
integrability gives the existing `H1IdentityRHSIntegrableBefore` package. -/
theorem H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hInit : H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX := by
  refine
    { identity := hId
      rhs_intervalIntegrable := ?_ }
  intro a b ha hab hbT
  rcases lt_or_eq_of_le ha with ha_pos | hzero
  · have hRHSCont :
        ContinuousOn
          (H1IdentityRHSValue p u taxisX uvxx reactX) (Set.Icc a b) :=
      H1IdentityRHS_continuousOn_Icc_of_components
        (hStrict.lap_cont ha_pos hab hbT)
        (hStrict.taxis_cont ha_pos hab hbT)
        (hStrict.uvxx_cont ha_pos hab hbT)
        (hStrict.react_cont ha_pos hab hbT)
    exact hRHSCont.intervalIntegrable_of_Icc hab
  · subst a
    exact hInit hab hbT

/-- Route-C bounded-before wrapper: strict positive-time RHS component data plus
zero-window RHS integrability, with the local H¹ seed produced from the scalar
DI route. -/
theorem boundedBefore_of_H1supBoundDI_classicalChemRep_strictRHS_initialWindow_before
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
    (hcont0 : ContinuousWithinAt (H1energy u) (Set.Ici (0 : ℝ)) 0)
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity params u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore params u T
      taxisX uvxx reactX)
    (hInit : H1IdentityRHSInitialWindowIntegrableBefore params u T
      taxisX uvxx reactX)
    {V₁ V₂ M L : ℝ}
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hRHS : H1IdentityRHSIntegrableBefore params u T taxisX uvxx reactX :=
    H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialWindow
      hId hStrict hInit
  exact boundedBefore_of_H1supBoundDI_classicalChemRep_before
    hbounded ha hu₀ hT hsol htrace hfrontier hcont0 hRHS hdata

#print axioms
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialWindow
#print axioms
  boundedBefore_of_H1supBoundDI_classicalChemRep_strictRHS_initialWindow_before

end ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability
