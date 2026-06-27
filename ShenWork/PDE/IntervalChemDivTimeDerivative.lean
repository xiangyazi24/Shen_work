import ShenWork.PDE.IntervalCoupledSourceTimeC1
import ShenWork.Paper2.IntervalMildPicardRegularity
import ShenWork.Paper2.IntervalPicardLimitK1
import ShenWork.Paper2.IntervalResolverTimeEndpoint

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalResolverTimeRegularity
open ShenWork.IntervalResolverTimeEndpoint
open ShenWork.PDE.IntervalMildSourceDecayHelper
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Lifted time derivative of the coupled elliptic concentration.  The committed
resolver time-regularity lemmas prove continuity properties of this field from
`ResolverHasSpectralAgreement`. -/
def coupledChemicalTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv (fun r => intervalDomainLift (coupledChemicalConcentration p u r) x) s

/-- The pointwise chain-rule candidate for
`∂ₜ ∂ₓ (u ∂ₓv / (1+v)^β)`, lifted to `[0,1]`.

The `∂ₜu` factor is `PicardLimitK1.slopeSlice`, the committed K1 derivative
datum.  The `∂ₜv` factor is `coupledChemicalTimeDerivativeLift`, supplied by the
resolver time-regularity route. -/
def coupledChemDivTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv
    (fun y : ℝ =>
      let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
      let vt : ℝ → ℝ := coupledChemicalTimeDerivativeLift p u s
      ShenWork.Paper2.PicardLimitK1.slopeSlice u s y * deriv v y /
          (1 + v y) ^ p.β +
        intervalDomainLift (u s) y * deriv vt y / (1 + v y) ^ p.β -
        p.β * intervalDomainLift (u s) y * deriv v y * vt y /
          (1 + v y) ^ (p.β + 1))
    x

/-- Coefficient derivative candidate produced by the chem-div chain rule. -/
def coupledChemDivAdot (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  cosineCoeffs (coupledChemDivTimeDerivativeLift p u s) n

/-- Resolver-fed joint continuity of `∂ₜv` on the open time/closed space slab. -/
theorem coupledChemicalTimeDerivative_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1) := by
  simpa [coupledChemicalTimeDerivativeLift, Function.uncurry] using
    (resolver_timeDeriv_jointContinuousOn_closed H)

/-- Resolver-fed fixed-space continuity of `∂ₜv` on a closed positive window. -/
theorem coupledChemicalTimeDerivative_continuousOn_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U T c x : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => coupledChemicalTimeDerivativeLift p u s x)
      (Icc c T) := by
  simpa [coupledChemicalTimeDerivativeLift] using
    (resolver_lift_timeDeriv_continuousOn_Icc_of_lt_horizon
      (v := coupledChemicalConcentration p u) H hc hTU hx)

/-- Local pointwise chain-rule and compact-slab continuity hypotheses for the
explicit chem-div derivative field.

This is the intentionally non-circular analytic gap left by the skeleton: it is
about the pointwise chain-rule formula and a local dominated-convergence slab,
not about an arbitrary coefficient derivative. -/
structure CoupledChemDivLocalChainRule
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      MeasureTheory.IntervalIntegrable (coupledChemDivSourceLift p u s)
        MeasureTheory.volume (0 : ℝ) 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => coupledChemDivSourceLift p u r x)
        (coupledChemDivTimeDerivativeLift p u s x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

/-- The complete chem-div coefficient field package consumed by the coupled
source `DuhamelSourceTimeC1` constructor.

The derivative is fixed to `coupledChemDivAdot`; callers can no longer choose an
arbitrary coefficient derivative. -/
structure CoupledChemDivTimeC1Fields
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  Cchem : ℝ
  hCchem : 0 ≤ Cchem
  hH2 : ∀ s, 0 ≤ s →
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
  hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs (coupledChemDivSourceLift p u s) k|
      ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2
  hzero : ∀ s, 0 ≤ s →
    |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem
  hchain : CoupledChemDivLocalChainRule p u
  hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n)
  MchemDot : ℝ
  hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot

/-- The old coefficient `HasDerivAt` field, derived from the local pointwise
chain-rule package by the committed cosine-coefficient time-Leibniz theorem. -/
theorem coupledChemDivCoeff_hasDerivAt_of_fields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (F : CoupledChemDivTimeC1Fields p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s := by
  rcases F.hchain.exists_local_slab s with
    ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
  exact
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
      (f := coupledChemDivSourceLift p u)
      (f' := coupledChemDivTimeDerivativeLift p u)
      (τ := s) (δ := δ) (n := n) hδ hf_cont hdiff hcont_deriv

/-- Chem-div source `DuhamelSourceTimeC1` from the explicit derivative field
package. -/
noncomputable def coupledChemDivSource_timeC1_of_fields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (F : CoupledChemDivTimeC1Fields p u) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u) := by
  have hderiv : ∀ s n,
      HasDerivAt
        (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
        (coupledChemDivAdot p u s n) s :=
    fun s n => coupledChemDivCoeff_hasDerivAt_of_fields F s n
  exact
    coupledChemDivSource_duhamelSourceTimeC1
      (p := p) (u := u) F.hH2 (C := F.Cchem) F.hCchem F.hdecay
      F.hzero (adot := coupledChemDivAdot p u) hderiv F.hadotcont
      (Mdot := F.MchemDot) F.hMdot

end ShenWork.IntervalCoupledRegularityBootstrap
