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

/-- Initial-window interval-integrability of the scalar H¹-energy derivative.

This is a strictly scalar near-zero input.  It does not assert componentwise
integrability or zero-start `lapL2sq` continuity. -/
def H1EnergyDerivativeInitialWindowIntegrableBefore
    (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∀ {b : ℝ}, 0 ≤ b → b < T →
    IntervalIntegrable (fun r => deriv (H1energy u) r) volume (0 : ℝ) b

/-- Initial-window integrability of the assembled explicit H¹ identity RHS.

This is intentionally weaker than zero-start component continuity and does not
assert any zero-time `lapL2sq` trace. -/
def H1IdentityRHSInitialWindowIntegrableBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (T : ℝ)
    (taxisX uvxx reactX : ℝ → ℝ) : Prop :=
  ∀ {b : ℝ}, 0 ≤ b → b < T →
    IntervalIntegrable
      (H1IdentityRHSValue p u taxisX uvxx reactX) volume (0 : ℝ) b

/-- Transfer interval-integrability from the scalar H¹ derivative to an
explicit RHS when they agree on the unordered integration interval. -/
theorem H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_uIoc
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {a b : ℝ}
    (hDeriv :
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b)
    (heq : ∀ r, r ∈ Set.uIoc a b →
      deriv (H1energy u) r =
        H1IdentityRHSValue p u taxisX uvxx reactX r) :
    IntervalIntegrable
      (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b :=
  hDeriv.congr heq

/-- Ordered-interval version of
`H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_uIoc`. -/
theorem H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_Ioc
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hDeriv :
      IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b)
    (heq : ∀ r, r ∈ Set.Ioc a b →
      deriv (H1energy u) r =
        H1IdentityRHSValue p u taxisX uvxx reactX r) :
    IntervalIntegrable
      (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b := by
  refine H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_uIoc
    (p := p) (u := u) (taxisX := taxisX) (uvxx := uvxx)
    (reactX := reactX) hDeriv ?_
  intro r hr
  exact heq r (by simpa [Set.uIoc_of_le hab] using hr)

/-- Initial-window integrability of the scalar H¹ derivative gives
initial-window integrability of the assembled explicit RHS.

The H¹ identity is only used on `Ioc 0 b`; the endpoint value at zero is
irrelevant for interval integrability. -/
theorem H1IdentityRHSInitialWindowIntegrableBefore_of_deriv_initialWindow
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hDeriv :
      H1EnergyDerivativeInitialWindowIntegrableBefore u T) :
    H1IdentityRHSInitialWindowIntegrableBefore p u T
      taxisX uvxx reactX := by
  intro b hb0 hbT
  refine H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_Ioc
    (p := p) (u := u) (taxisX := taxisX) (uvxx := uvxx)
    (reactX := reactX) hb0 (hDeriv hb0 hbT) ?_
  intro r hr
  have hr0 : 0 < r := hr.1
  have hrT : r < T := lt_of_le_of_lt hr.2 hbT
  have hEnergy := hId r ⟨hr0, hrT⟩
  unfold H1EnergyIdentity at hEnergy
  simpa [H1IdentityRHSValue] using hEnergy.deriv

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

/-- Strict component continuity plus scalar H¹ derivative initial-window
integrability gives the landed `H1IdentityRHSIntegrableBefore` package. -/
theorem H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_derivInitial
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hStrict : H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX)
    (hDeriv :
      H1EnergyDerivativeInitialWindowIntegrableBefore u T) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialWindow
    hId hStrict
    (H1IdentityRHSInitialWindowIntegrableBefore_of_deriv_initialWindow
      hId hDeriv)

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

/-- Route-C bounded-before wrapper using scalar H¹ derivative initial-window
integrability as the near-zero input. -/
theorem boundedBefore_of_H1supBoundDI_classicalChemRep_strictRHS_derivInitial_before
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
    (hDeriv :
      H1EnergyDerivativeInitialWindowIntegrableBefore u T)
    {V₁ V₂ M L : ℝ}
    (hdata : H1SupBoundDIDataBefore params u T V₁ V₂ M L) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hInit :
      H1IdentityRHSInitialWindowIntegrableBefore params u T
        taxisX uvxx reactX :=
    H1IdentityRHSInitialWindowIntegrableBefore_of_deriv_initialWindow
      hId hDeriv
  exact boundedBefore_of_H1supBoundDI_classicalChemRep_strictRHS_initialWindow_before
    hbounded ha hu₀ hT hsol htrace hfrontier hcont0 hId hStrict hInit hdata

#print axioms H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_uIoc
#print axioms H1IdentityRHS_intervalIntegrable_of_deriv_eq_on_Ioc
#print axioms H1IdentityRHSInitialWindowIntegrableBefore_of_deriv_initialWindow
#print axioms
  H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_initialWindow
#print axioms H1IdentityRHSIntegrableBefore_of_componentsStrictBefore_derivInitial
#print axioms
  boundedBefore_of_H1supBoundDI_classicalChemRep_strictRHS_initialWindow_before
#print axioms
  boundedBefore_of_H1supBoundDI_classicalChemRep_strictRHS_derivInitial_before

end ShenWork.Paper2.IntervalChiNegH1StrictRHSIntegrability
