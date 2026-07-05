import ShenWork.Paper2.IntervalChiNegH1Bridge

/-!
# H¹ physical split component frontier

This file gives a stable name to the remaining H¹ physical-split frontier:
one fixed triple of scalar component functions must simultaneously supply the
pointwise H¹ identity, the square-root estimates, and closed-window component
continuity.  It deliberately does not define the analytic formulas for those
components; future producers must instantiate the fields with the real PDE
terms, not with a bookkeeping placeholder.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1Bridge

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1PhysicalComponents

/-- Route-facing package for one fixed H¹ RHS split.

The name says "physical" only at the interface level: this record asserts the
facts downstream needs about the supplied functions.  It is not a producer of
the PDE formulas themselves. -/
structure H1PhysicalSplitComponentDataBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) (taxisX uvxx reactX : ℝ → ℝ) : Prop where
  identity : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ)
  bounds : H1SqrtTermBoundsBefore p u T V₁ V₂ M L
    taxisX uvxx reactX
  components : H1IdentityRHSComponentsContinuousBefore p u T
    taxisX uvxx reactX

/-- The named physical-split component package supplies the canonical
square-root differential-inequality data. -/
theorem H1SupBoundSqrtDIDataBefore_of_physicalSplitComponents
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (h : H1PhysicalSplitComponentDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX) :
    H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX :=
  H1SupBoundSqrtDIDataBefore_of_identity_and_sqrtBounds
    h.identity h.bounds

/-- The named physical-split component package supplies RHS integrability for
the same fixed component functions. -/
theorem H1IdentityRHSIntegrableBefore_of_physicalSplitComponents
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (h : H1PhysicalSplitComponentDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSIntegrableBefore_of_componentsContinuousBefore
    h.identity h.components

/-- The named physical-split component package is exactly enough for the
combined sqrt/RHS package used by the bounded-before route. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_physicalSplitComponents
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (h : H1PhysicalSplitComponentDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsContinuous
    h.identity h.bounds h.components

/-- Existential wrapper for a future producer that constructs the actual
component functions rather than taking them as parameters. -/
def H1PhysicalSplitFrontierBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) : Prop :=
  ∃ taxisX uvxx reactX : ℝ → ℝ,
    H1PhysicalSplitComponentDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX

/-- Unpack an existential physical-split frontier into the route package with
its concrete global component functions exposed. -/
theorem exists_H1SupBoundSqrtRHSIntegrableBefore_of_physicalSplitFrontier
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (h : H1PhysicalSplitFrontierBefore p u T V₁ V₂ M L) :
    ∃ taxisX uvxx reactX : ℝ → ℝ,
      H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
        taxisX uvxx reactX :=
  by
    rcases h with ⟨taxisX, uvxx, reactX, hdata⟩
    exact ⟨taxisX, uvxx, reactX,
      H1SupBoundSqrtRHSIntegrableBefore_of_physicalSplitComponents hdata⟩

#print axioms H1SupBoundSqrtDIDataBefore_of_physicalSplitComponents
#print axioms H1IdentityRHSIntegrableBefore_of_physicalSplitComponents
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_physicalSplitComponents
#print axioms exists_H1SupBoundSqrtRHSIntegrableBefore_of_physicalSplitFrontier

end ShenWork.Paper2.IntervalChiNegH1PhysicalComponents
