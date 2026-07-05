import ShenWork.Paper2.IntervalChiNegH1EnergyCore
import ShenWork.Paper2.IntervalChiNegH1EnergyDeriv
import ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer
import ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
import ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity

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
open ShenWork.Paper2.IntervalChiNegH1EnergyIdentity
open ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability
open ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer
open ShenWork.Paper2.IntervalChiNegH1SupBoundDIProducer
open ShenWork.Paper2.IntervalChiNegH1LapComponentContinuity

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

/-- Strict-positive-time version of the component-continuity package.  This is
the shape supplied by the current `lapL2sq` continuity producers. -/
structure H1IdentityRHSComponentsContinuousStrictBefore
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T : ℝ) (taxisX uvxx reactX : ℝ → ℝ) : Prop where
  lap_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b)
  taxis_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn taxisX (Set.Icc a b)
  uvxx_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn uvxx (Set.Icc a b)
  react_cont : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
    ContinuousOn reactX (Set.Icc a b)

/-- Constructor for the strict component-continuity package from the four
strict component fields. -/
theorem H1IdentityRHSComponentsContinuousStrictBefore_of_components
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hLap : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    (hTaxis : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX :=
  { lap_cont := hLap
    taxis_cont := hTaxis
    uvxx_cont := hUvxx
    react_cont := hReact }

/-- Fill the strict lap component from `H1LiftDeriv2JointContinuousBefore`,
carrying the other three strict component continuities explicitly. -/
theorem
    H1IdentityRHSComponentsContinuousStrictBefore_of_liftDeriv2_jointContinuousBefore
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (huxx : H1LiftDeriv2JointContinuousBefore u T)
    (hTaxis : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX :=
  H1IdentityRHSComponentsContinuousStrictBefore_of_components
    (p := p) (u := u) (T := T)
    (taxisX := taxisX) (uvxx := uvxx) (reactX := reactX)
    (lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
      huxx)
    hTaxis hUvxx hReact

/-- Fill the strict lap component from a continuous closed-slab representative
of `liftDeriv2` plus interior-spatial equality, carrying the other strict
component continuities explicitly. -/
theorem
    H1IdentityRHSComponentsContinuousStrictBefore_of_strictSlab_interior_eq_continuous
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1))
    (hTaxis : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousStrictBefore p u T
      taxisX uvxx reactX :=
  H1IdentityRHSComponentsContinuousStrictBefore_of_components
    (p := p) (u := u) (T := T)
    (taxisX := taxisX) (uvxx := uvxx) (reactX := reactX)
    (lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
      hF hEqInterior)
    hTaxis hUvxx hReact

/-- Upgrade strict positive-time lap continuity to the existing closed-window
component package when the zero-starting windows are supplied explicitly. -/
theorem H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hLap0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b))
    (hLapStrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    (hTaxis : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX := by
  refine
    { lap_cont := ?_
      taxis_cont := hTaxis
      uvxx_cont := hUvxx
      react_cont := hReact }
  intro a b ha hab hbT
  by_cases ha_pos : 0 < a
  · exact hLapStrict ha_pos hab hbT
  · have ha_eq : a = 0 := le_antisymm (le_of_not_gt ha_pos) ha
    subst a
    exact hLap0 (b := b) hab hbT

/-- Record-style version of
`H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict`. -/
theorem H1IdentityRHSComponentsContinuousBefore_of_lapEndpoint_and_lapStrict
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hLap0 : H1LapComponentEndpointContinuousBefore u T)
    (hLapStrict : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    (hTaxis : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict
    (p := p) (u := u) (T := T)
    (taxisX := taxisX) (uvxx := uvxx) (reactX := reactX)
    hLap0.lap_cont0 hLapStrict hTaxis hUvxx hReact

/-- Existing `Before` package from positive-time `u_xx` joint continuity plus an
explicit zero-endpoint lap-component continuity input. -/
theorem
    H1IdentityRHSComponentsContinuousBefore_of_liftDeriv2_jointContinuousBefore_and_lap_zero
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (huxx : H1LiftDeriv2JointContinuousBefore u T)
    (hLap0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b))
    (hTaxis : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict
    (p := p) (u := u) (T := T)
    (taxisX := taxisX) (uvxx := uvxx) (reactX := reactX)
    hLap0
    (lapL2sq_continuousOn_strictWindow_of_liftDeriv2_jointContinuousBefore
      huxx)
    hTaxis hUvxx hReact

/-- Record-style version of
`H1IdentityRHSComponentsContinuousBefore_of_liftDeriv2_jointContinuousBefore_and_lap_zero`. -/
theorem
    H1IdentityRHSComponentsContinuousBefore_of_liftDeriv2_jointContinuousBefore_and_lapEndpoint
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (huxx : H1LiftDeriv2JointContinuousBefore u T)
    (hLap0 : H1LapComponentEndpointContinuousBefore u T)
    (hTaxis : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSComponentsContinuousBefore_of_liftDeriv2_jointContinuousBefore_and_lap_zero
    (p := p) (u := u) (T := T)
    (taxisX := taxisX) (uvxx := uvxx) (reactX := reactX)
    huxx hLap0.lap_cont0 hTaxis hUvxx hReact

/-- Existing `Before` package from a positive-time continuous representative of
`liftDeriv2`, plus an explicit zero-endpoint lap-continuity input. -/
theorem
    H1IdentityRHSComponentsContinuousBefore_of_strictSlab_interior_eq_continuous_and_lap_zero
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1))
    (hLap0 : ∀ {b : ℝ}, 0 ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc (0 : ℝ) b))
    (hTaxis : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict
    (p := p) (u := u) (T := T)
    (taxisX := taxisX) (uvxx := uvxx) (reactX := reactX)
    hLap0
    (lapL2sq_continuousOn_strictWindow_of_strictSlab_interior_eq_continuous
      hF hEqInterior)
    hTaxis hUvxx hReact

/-- Record-style version of
`H1IdentityRHSComponentsContinuousBefore_of_strictSlab_interior_eq_continuous_and_lap_zero`. -/
theorem
    H1IdentityRHSComponentsContinuousBefore_of_strictSlab_interior_eq_continuous_and_lapEndpoint
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {F : ℝ → ℝ → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hF : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      ContinuousOn (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1))
    (hEqInterior : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < T →
      Set.EqOn
        (Function.uncurry (fun t x => liftDeriv2 u t x))
        (Function.uncurry F)
        (Set.Icc a b ×ˢ Set.Ioo (0 : ℝ) 1))
    (hLap0 : H1LapComponentEndpointContinuousBefore u T)
    (hTaxis : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSComponentsContinuousBefore p u T taxisX uvxx reactX :=
  H1IdentityRHSComponentsContinuousBefore_of_strictSlab_interior_eq_continuous_and_lap_zero
    (p := p) (u := u) (T := T)
    (F := F) (taxisX := taxisX) (uvxx := uvxx) (reactX := reactX)
    hF hEqInterior hLap0.lap_cont0 hTaxis hUvxx hReact

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
#print axioms H1IdentityRHSComponentsContinuousStrictBefore_of_components
#print axioms H1IdentityRHSComponentsContinuousStrictBefore_of_liftDeriv2_jointContinuousBefore
#print axioms H1IdentityRHSComponentsContinuousStrictBefore_of_strictSlab_interior_eq_continuous
#print axioms H1IdentityRHSComponentsContinuousBefore_of_lap_zero_and_lap_strict
#print axioms H1IdentityRHSComponentsContinuousBefore_of_lapEndpoint_and_lapStrict
#print axioms
  H1IdentityRHSComponentsContinuousBefore_of_liftDeriv2_jointContinuousBefore_and_lap_zero
#print axioms
  H1IdentityRHSComponentsContinuousBefore_of_liftDeriv2_jointContinuousBefore_and_lapEndpoint
#print axioms
  H1IdentityRHSComponentsContinuousBefore_of_strictSlab_interior_eq_continuous_and_lap_zero
#print axioms
  H1IdentityRHSComponentsContinuousBefore_of_strictSlab_interior_eq_continuous_and_lapEndpoint
#print axioms H1IdentityRHSIntegrableBefore_of_componentsContinuousBefore
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_identity_sqrtBounds_componentsContinuous
#print axioms H1EnergyIdentity_before_of_parametricSplit_componentsContinuous
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_parametricSplit_componentsContinuous
#print axioms H1EnergyIdentity_before_of_spectralSplit_componentsContinuous
#print axioms H1SupBoundSqrtRHSIntegrableBefore_of_spectralSplit_componentsContinuous

end ShenWork.Paper2.IntervalChiNegH1Bridge
