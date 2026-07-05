import ShenWork.Paper2.IntervalChiNegH1PhysicalComponents
import ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

/-!
# Concrete physical H1 RHS scalar functions

This file names the physical scalar pieces that should instantiate the H1
identity route.  It only packages route data for those exact functions; the
analytic continuity, bounds, and substitution hypotheses remain explicit.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyCore
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge
open ShenWork.Paper2.IntervalChiNegH1PhysicalComponents
open ShenWork.Paper2.IntervalChiNegH1ChemDivRepresentative

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars

/-- The `u_x v_x / (1+v)^beta` part of the physical chemotaxis divergence
representative. -/
def H1PhysicalChemTaxisPart (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  deriv (intervalDomainLift (u t)) x *
      deriv (intervalDomainLift (v t)) x /
    (1 + intervalDomainLift (v t) x) ^ p.β

/-- The remaining `u v_xx` and denominator-derivative part of the physical
chemotaxis divergence representative, with `v_xx` replaced by the elliptic
reaction representative. -/
def H1PhysicalChemUvxxPart (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  intervalDomainLift (u t) x *
      (p.μ * intervalDomainLift (v t) x -
        p.ν * (intervalDomainLift (u t) x) ^ p.γ) /
    (1 + intervalDomainLift (v t) x) ^ p.β -
  p.β * intervalDomainLift (u t) x *
      (deriv (intervalDomainLift (v t)) x) ^ 2 /
    (1 + intervalDomainLift (v t) x) ^ (p.β + 1)

/-- The logistic reaction part in the physical H1 RHS. -/
def H1PhysicalLogisticReactionPart (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  intervalDomainLift (u t) x *
    (p.a - p.b * (intervalDomainLift (u t) x) ^ p.α)

/-- The two physical chemotaxis scalar pieces recombine to the landed
closed-slab chemotaxis-divergence representative. -/
theorem H1PhysicalChemParts_sum_eq_liftChemotaxisDivPhysicalRep
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) :
    H1PhysicalChemTaxisPart p u v t x +
        H1PhysicalChemUvxxPart p u v t x =
      liftChemotaxisDivPhysicalRep p u v t x := by
  unfold H1PhysicalChemTaxisPart H1PhysicalChemUvxxPart
    liftChemotaxisDivPhysicalRep
  ring

/-- Integral scalar for the taxis part of the physical H1 RHS. -/
def H1PhysicalTaxisX (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  -(∫ x in (0 : ℝ)..1,
      liftDeriv2 u τ x * H1PhysicalChemTaxisPart p u v τ x)

/-- Integral scalar for the `u v_xx`/denominator-derivative part of the
physical H1 RHS. -/
def H1PhysicalUvxxX (p : CM2Params)
    (u v : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  -(∫ x in (0 : ℝ)..1,
      liftDeriv2 u τ x * H1PhysicalChemUvxxPart p u v τ x)

/-- Integral scalar for the logistic reaction part of the physical H1 RHS. -/
def H1PhysicalReactX (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (τ : ℝ) : ℝ :=
  -(∫ x in (0 : ℝ)..1,
      liftDeriv2 u τ x * H1PhysicalLogisticReactionPart p u τ x)

/-- Pointwise H1 identity for the concrete physical scalar triple. -/
structure H1PhysicalRHSIdentityBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop where
  identity : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    H1EnergyIdentity p u τ
      (H1PhysicalTaxisX p u v τ)
      (H1PhysicalUvxxX p u v τ)
      (H1PhysicalReactX p u τ)

/-- Closed-window component continuity for the concrete physical scalar
triple. -/
structure H1PhysicalRHSComponentsContinuousBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) : Prop where
  components : H1IdentityRHSComponentsContinuousBefore p u T
    (H1PhysicalTaxisX p u v)
    (H1PhysicalUvxxX p u v)
    (H1PhysicalReactX p u)

/-- Square-root estimates for the concrete physical scalar triple. -/
structure H1PhysicalRHSSqrtBoundsBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  bounds : H1SqrtTermBoundsBefore p u T V₁ V₂ M L
    (H1PhysicalTaxisX p u v)
    (H1PhysicalUvxxX p u v)
    (H1PhysicalReactX p u)

/-- Route package for the concrete physical scalar triple. -/
structure H1PhysicalRHSRouteBefore
    (p : CM2Params) (u v : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop where
  identity : H1PhysicalRHSIdentityBefore p u v T
  bounds : H1PhysicalRHSSqrtBoundsBefore p u v T V₁ V₂ M L
  components : H1PhysicalRHSComponentsContinuousBefore p u v T

/-- Parametric Leibniz plus substitution into the concrete physical scalar RHS
gives the pointwise H1 identity package. -/
theorem H1PhysicalRHSIdentityBefore_of_parametric_and_substitution
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ} {uxt : ℝ → ℝ → ℝ}
    (hpar : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      HasDerivAt (H1energy u)
        (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) τ)
    (hsub : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) =
        H1IdentityRHSValue p u
          (H1PhysicalTaxisX p u v)
          (H1PhysicalUvxxX p u v)
          (H1PhysicalReactX p u) τ) :
    H1PhysicalRHSIdentityBefore p u v T := by
  refine ⟨?_⟩
  intro τ hτ
  have hsub' :
      (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) =
        -(lapL2sq u τ) +
          (-p.χ₀) * H1PhysicalTaxisX p u v τ +
          (-p.χ₀) * H1PhysicalUvxxX p u v τ +
          H1PhysicalReactX p u τ := by
    simpa [H1IdentityRHSValue] using hsub τ hτ
  exact H1EnergyIdentity_of_parametric_and_IBP (hpar τ hτ) hsub'

/-- The concrete physical scalar route supplies the Task77 physical split
component package. -/
theorem H1PhysicalSplitComponentDataBefore_of_physicalRHSRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSRouteBefore p u v T V₁ V₂ M L) :
    H1PhysicalSplitComponentDataBefore p u T V₁ V₂ M L
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  { identity := h.identity.identity
    bounds := h.bounds.bounds
    components := h.components.components }

/-- The concrete physical scalar route supplies the square-root differential
inequality data. -/
theorem H1SupBoundSqrtDIDataBefore_of_physicalRHSRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSRouteBefore p u v T V₁ V₂ M L) :
    H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1SupBoundSqrtDIDataBefore_of_physicalSplitComponents
    (H1PhysicalSplitComponentDataBefore_of_physicalRHSRoute h)

/-- The concrete physical scalar route supplies RHS integrability for the same
scalar triple. -/
theorem H1IdentityRHSIntegrableBefore_of_physicalRHSRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSRouteBefore p u v T V₁ V₂ M L) :
    H1IdentityRHSIntegrableBefore p u T
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1IdentityRHSIntegrableBefore_of_physicalSplitComponents
    (H1PhysicalSplitComponentDataBefore_of_physicalRHSRoute h)

/-- The concrete physical scalar route supplies the combined sqrt/RHS package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_physicalRHSRoute
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalRHSRouteBefore p u v T V₁ V₂ M L) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      (H1PhysicalTaxisX p u v)
      (H1PhysicalUvxxX p u v)
      (H1PhysicalReactX p u) :=
  H1SupBoundSqrtRHSIntegrableBefore_of_physicalSplitComponents
    (H1PhysicalSplitComponentDataBefore_of_physicalRHSRoute h)

#print axioms H1PhysicalChemParts_sum_eq_liftChemotaxisDivPhysicalRep
#print axioms H1PhysicalRHSIdentityBefore_of_parametric_and_substitution
#print axioms H1PhysicalSplitComponentDataBefore_of_physicalRHSRoute
#print axioms H1SupBoundSqrtDIDataBefore_of_physicalRHSRoute
#print axioms H1IdentityRHSIntegrableBefore_of_physicalRHSRoute
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_physicalRHSRoute

end ShenWork.Paper2.IntervalChiNegH1PhysicalRHSScalars
