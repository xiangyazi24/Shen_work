import ShenWork.Paper2.IntervalChiNegH1EnergyCore
import ShenWork.Paper2.IntervalChiNegH1EnergyDeriv
import ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer
import ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer

/-!
# H¹ route-specific bridge to the sqrt/RHS frontier

This file connects the two existing H¹ identity assembly routes to the
`H1SupBoundSqrtRHSIntegrableBefore` frontier package.  All analytic content is
kept as explicit hypotheses: the file only assembles records.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1EnergyCore
open ShenWork.Paper2.IntervalChiNegH1EnergyDeriv
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1Bridge

/-- The physical square-root norm estimates with explicit split functions.

This package deliberately does not include `H1EnergyIdentity`: route-specific
wrappers below supply that identity from either the parametric or spectral
route. -/
structure H1SqrtTermBoundsBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) (taxisX uvxx reactX : ℝ → ℝ) : Prop where
  hchi : 0 ≤ -p.χ₀
  hV1 : 0 ≤ V₁
  hV2 : 0 ≤ V₂
  hM : 0 ≤ M
  hL : 0 ≤ L
  htaxis : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    (-p.χ₀) * taxisX τ ≤
      (-p.χ₀) * (V₁ * (H1lapL2Norm u τ * H1gradL2Norm u τ))
  huvxx : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    (-p.χ₀) * uvxx τ ≤
      (-p.χ₀) * (M * (V₂ * H1lapL2Norm u τ))
  hreact : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    reactX τ ≤ L * (H1gradL2Norm u τ) ^ 2

/-- Explicit pointwise `H1EnergyIdentity` plus the shared square-root estimates
gives the landed square-root sup-bound package. -/
theorem H1SupBoundSqrtDIDataBefore_of_identity_and_sqrtBounds
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hb : H1SqrtTermBoundsBefore p u T V₁ V₂ M L
      taxisX uvxx reactX) :
    H1SupBoundSqrtDIDataBefore p u T V₁ V₂ M L
      taxisX uvxx reactX := by
  refine
    { hchi := hb.hchi
      hV1 := hb.hV1
      hV2 := hb.hV2
      hM := hb.hM
      hL := hb.hL
      point := ?_ }
  intro τ hτ0 hτT
  have hτ : τ ∈ Set.Ioo (0 : ℝ) T := ⟨hτ0, hτT⟩
  exact ⟨hId τ hτ, hb.htaxis τ hτ, hb.huvxx τ hτ, hb.hreact τ hτ⟩

/-- Explicit pointwise identity, square-root estimates, and interval
integrability of the same explicit RHS give the final combined sqrt/RHS
package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_RHSInt
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hb : H1SqrtTermBoundsBefore p u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hRHSInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      IntervalIntegrable
        (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX := by
  refine
    { sqrtData :=
        H1SupBoundSqrtDIDataBefore_of_identity_and_sqrtBounds
          hId hb
      rhs_intervalIntegrable := ?_ }
  intro a b ha hab hbT
  exact hRHSInt ha hab hbT

/-- Parametric-route physical split package.

The hard mixed-regularity data remain upstream in whatever proof produces
`hpar`; this package only records the route assembly inputs, pointwise
estimates, and RHS integrability. -/
structure H1ParametricSplitSqrtRHSIntegrableBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) (taxisX uvxx reactX : ℝ → ℝ)
    (uxt : ℝ → ℝ → ℝ) : Prop where
  bounds : H1SqrtTermBoundsBefore p u T V₁ V₂ M L taxisX uvxx reactX
  hpar : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    HasDerivAt (H1energy u)
      (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) τ
  hsub : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) =
      H1IdentityRHSValue p u taxisX uvxx reactX τ
  hRHSInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    IntervalIntegrable
      (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b

/-- The parametric route package supplies the pointwise `H1EnergyIdentity`. -/
theorem H1EnergyIdentity_before_of_parametricSplit
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (h : H1ParametricSplitSqrtRHSIntegrableBefore
      p u T V₁ V₂ M L taxisX uvxx reactX uxt) :
    ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ) := by
  intro τ hτ
  have hsub' :
      (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) =
        -(lapL2sq u τ) + (-p.χ₀) * taxisX τ +
          (-p.χ₀) * uvxx τ + reactX τ := by
    simpa [H1IdentityRHSValue] using h.hsub τ hτ
  exact H1EnergyIdentity_of_parametric_and_IBP (h.hpar τ hτ) hsub'

/-- Parametric-route bridge to the combined sqrt/RHS package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (h : H1ParametricSplitSqrtRHSIntegrableBefore
      p u T V₁ V₂ M L taxisX uvxx reactX uxt) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_RHSInt
    (H1EnergyIdentity_before_of_parametricSplit h) h.bounds h.hRHSInt

/-- Spectral-route physical split package.

The spectral hard inputs remain explicit: the Parseval function equality, the
term-by-term spectral derivative, and the sorted value identity. -/
structure H1SpectralSplitSqrtRHSIntegrableBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) (taxisX uvxx reactX : ℝ → ℝ)
    (uhatT : ℝ → ℕ → ℝ) : Prop where
  bounds : H1SqrtTermBoundsBefore p u T V₁ V₂ M L taxisX uvxx reactX
  hParsevalGrad : H1energy u = specH1energy u
  hder : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    HasDerivAt (specH1energy u)
      (∑' k : ℕ, specTermDeriv u uhatT τ k) τ
  hval : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    (∑' k : ℕ, specTermDeriv u uhatT τ k) =
      H1IdentityRHSValue p u taxisX uvxx reactX τ
  hRHSInt : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    IntervalIntegrable
      (H1IdentityRHSValue p u taxisX uvxx reactX) volume a b

/-- The spectral route package supplies the pointwise `H1EnergyIdentity`. -/
theorem H1EnergyIdentity_before_of_spectralSplit
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (h : H1SpectralSplitSqrtRHSIntegrableBefore
      p u T V₁ V₂ M L taxisX uvxx reactX uhatT) :
    ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ) := by
  intro τ hτ
  have hval' :
      (∑' k : ℕ, specTermDeriv u uhatT τ k) =
        -(lapL2sq u τ) + (-p.χ₀) * taxisX τ +
          (-p.χ₀) * uvxx τ + reactX τ := by
    simpa [H1IdentityRHSValue] using h.hval τ hτ
  exact H1EnergyIdentity_of_spectral h.hParsevalGrad (h.hder τ hτ) hval'

/-- Spectral-route bridge to the combined sqrt/RHS package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (h : H1SpectralSplitSqrtRHSIntegrableBefore
      p u T V₁ V₂ M L taxisX uvxx reactX uhatT) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_RHSInt
    (H1EnergyIdentity_before_of_spectralSplit h) h.bounds h.hRHSInt

/-- Closed-window continuity of the four explicit H¹ identity RHS components.

This is only scalar/RHS regularity data: it does not assert the pointwise
identity or any physical estimate. -/
structure H1IdentityRHSComponentsContinuousBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) (taxisX uvxx reactX : ℝ → ℝ) : Prop where
  lap_cont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)
  taxis_cont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    ContinuousOn taxisX (Set.Icc a b)
  uvxx_cont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    ContinuousOn uvxx (Set.Icc a b)
  react_cont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
    ContinuousOn reactX (Set.Icc a b)

/-- Component continuity plus the same explicit pointwise H¹ identity gives
the landed RHS-integrability package. -/
theorem H1IdentityRHSIntegrableBefore_of_componentsContinuousBefore
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hc : H1IdentityRHSComponentsContinuousBefore p u T
      taxisX uvxx reactX) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSIntegrableBefore_of_component_continuousOn_Icc
    hId
    (fun ha hab hbT => hc.lap_cont ha hab hbT)
    (fun ha hab hbT => hc.taxis_cont ha hab hbT)
    (fun ha hab hbT => hc.uvxx_cont ha hab hbT)
    (fun ha hab hbT => hc.react_cont ha hab hbT)

/-- Pointwise identity, square-root term bounds, and component continuity
produce the final combined sqrt/RHS package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsContinuous
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hb : H1SqrtTermBoundsBefore p u T V₁ V₂ M L
      taxisX uvxx reactX)
    (hc : H1IdentityRHSComponentsContinuousBefore p u T
      taxisX uvxx reactX) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX := by
  have hRHS : H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
    H1IdentityRHSIntegrableBefore_of_componentsContinuousBefore hId hc
  exact H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_RHSInt
    hId hb hRHS.rhs_intervalIntegrable

/-- Parametric-route physical split package using component continuity instead
of raw RHS interval-integrability. -/
structure H1ParametricSplitSqrtComponentContinuousBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) (taxisX uvxx reactX : ℝ → ℝ)
    (uxt : ℝ → ℝ → ℝ) : Prop where
  bounds : H1SqrtTermBoundsBefore p u T V₁ V₂ M L taxisX uvxx reactX
  components : H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX
  hpar : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    HasDerivAt (H1energy u)
      (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) τ
  hsub : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) =
      H1IdentityRHSValue p u taxisX uvxx reactX τ

/-- The parametric component-continuity package supplies pointwise
`H1EnergyIdentity`. -/
theorem H1EnergyIdentity_before_of_parametricSplit_componentsContinuous
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (h : H1ParametricSplitSqrtComponentContinuousBefore
      p u T V₁ V₂ M L taxisX uvxx reactX uxt) :
    ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ) := by
  intro τ hτ
  have hsub' :
      (∫ y in (0 : ℝ)..1, ux u τ y * uxt τ y) =
        -(lapL2sq u τ) + (-p.χ₀) * taxisX τ +
          (-p.χ₀) * uvxx τ + reactX τ := by
    simpa [H1IdentityRHSValue] using h.hsub τ hτ
  exact H1EnergyIdentity_of_parametric_and_IBP (h.hpar τ hτ) hsub'

/-- Parametric route with component continuity gives the final combined
sqrt/RHS package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit_componentsContinuous
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {uxt : ℝ → ℝ → ℝ}
    (h : H1ParametricSplitSqrtComponentContinuousBefore
      p u T V₁ V₂ M L taxisX uvxx reactX uxt) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsContinuous
    (H1EnergyIdentity_before_of_parametricSplit_componentsContinuous h)
    h.bounds h.components

/-- Spectral-route physical split package using component continuity instead
of raw RHS interval-integrability. -/
structure H1SpectralSplitSqrtComponentContinuousBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T V₁ V₂ M L : ℝ) (taxisX uvxx reactX : ℝ → ℝ)
    (uhatT : ℝ → ℕ → ℝ) : Prop where
  bounds : H1SqrtTermBoundsBefore p u T V₁ V₂ M L taxisX uvxx reactX
  components : H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX
  hParsevalGrad : H1energy u = specH1energy u
  hder : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    HasDerivAt (specH1energy u)
      (∑' k : ℕ, specTermDeriv u uhatT τ k) τ
  hval : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
    (∑' k : ℕ, specTermDeriv u uhatT τ k) =
      H1IdentityRHSValue p u taxisX uvxx reactX τ

/-- The spectral component-continuity package supplies pointwise
`H1EnergyIdentity`. -/
theorem H1EnergyIdentity_before_of_spectralSplit_componentsContinuous
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (h : H1SpectralSplitSqrtComponentContinuousBefore
      p u T V₁ V₂ M L taxisX uvxx reactX uhatT) :
    ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ) := by
  intro τ hτ
  have hval' :
      (∑' k : ℕ, specTermDeriv u uhatT τ k) =
        -(lapL2sq u τ) + (-p.χ₀) * taxisX τ +
          (-p.χ₀) * uvxx τ + reactX τ := by
    simpa [H1IdentityRHSValue] using h.hval τ hτ
  exact H1EnergyIdentity_of_spectral h.hParsevalGrad (h.hder τ hτ) hval'

/-- Spectral route with component continuity gives the final combined sqrt/RHS
package. -/
theorem H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit_componentsContinuous
    {p : CM2Params} {T V₁ V₂ M L : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {uhatT : ℝ → ℕ → ℝ}
    (h : H1SpectralSplitSqrtComponentContinuousBefore
      p u T V₁ V₂ M L taxisX uvxx reactX uhatT) :
    H1SupBoundSqrtRHSIntegrableBefore p u T V₁ V₂ M L
      taxisX uvxx reactX :=
  H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsContinuous
    (H1EnergyIdentity_before_of_spectralSplit_componentsContinuous h)
    h.bounds h.components

#print axioms H1SupBoundSqrtDIDataBefore_of_identity_and_sqrtBounds
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_RHSInt
#print axioms H1EnergyIdentity_before_of_parametricSplit
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit
#print axioms H1EnergyIdentity_before_of_spectralSplit
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit
#print axioms H1IdentityRHSIntegrableBefore_of_componentsContinuousBefore
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsContinuous
#print axioms H1EnergyIdentity_before_of_parametricSplit_componentsContinuous
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit_componentsContinuous
#print axioms H1EnergyIdentity_before_of_spectralSplit_componentsContinuous
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit_componentsContinuous

end ShenWork.Paper2.IntervalChiNegH1Bridge
