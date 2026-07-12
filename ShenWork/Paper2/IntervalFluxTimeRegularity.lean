import ShenWork.Paper2.IntervalConjugateChemDivSourceTimeC1On
import ShenWork.PDE.IntervalNeumannEllipticGreenGradient

/-!
# Flux time-regularity package on positive conjugate windows

This file records the positive-window time-regularity data for the chemotaxis
flux route and wires it into the existing `CoupledChemDivLocalChainRule` /
`chemDivSource_duhamelSourceTimeC1On_of_timeRegularFlux` interface.
-/

open Set
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalConjugatePicard (ConjugateMildSolutionData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Carried time-derivative data for `u` on a positive conjugate window. -/
structure FluxTimeRegularityInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) (c T' : ℝ) where
  ut : ℝ → intervalDomainPoint → ℝ
  hut : ∀ s ∈ Icc c T', ∀ x, HasDerivAt (fun t => S.u t x) (ut s x) s
  Dut : ℝ
  hDut : ∀ s ∈ Icc c T', ∀ x, |ut s x| ≤ Dut
  hc : 0 < c
  hT' : T' < S.T

/-- Green value-kernel time-derivative bound from a source already bounded
against the Green `L¹` mass.  The intended source is
`ν γ u^(γ-1) ∂ₜu`; the final step uses the delivered `1/μ` Green mass. -/
theorem resolver_time_deriv_bound_of_ut
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀} {c T' : ℝ}
    (_I : FluxTimeRegularityInputs p S c T')
    {source : ℝ → ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hkernel : ∀ s ∈ Icc c T', ∀ x ∈ Icc (0 : ℝ) 1,
      |∫ y in (0 : ℝ)..1,
          ShenWork.PDE.neumannEllipticGreen p.μ x y * source s y|
        ≤ A * ∫ y in (0 : ℝ)..1,
          |ShenWork.PDE.neumannEllipticGreen p.μ x y|) :
    ∀ s ∈ Icc c T', ∀ x ∈ Icc (0 : ℝ) 1,
      |∫ y in (0 : ℝ)..1,
          ShenWork.PDE.neumannEllipticGreen p.μ x y * source s y|
        ≤ A * (1 / p.μ) := by
  intro s hs x hx
  calc
    |∫ y in (0 : ℝ)..1,
        ShenWork.PDE.neumannEllipticGreen p.μ x y * source s y|
        ≤ A * ∫ y in (0 : ℝ)..1,
            |ShenWork.PDE.neumannEllipticGreen p.μ x y| :=
      hkernel s hs x hx
    _ ≤ A * (1 / p.μ) :=
      mul_le_mul_of_nonneg_left
        (ShenWork.PDE.neumannEllipticGreen_l1_value_le p.hμ x hx) hA

/-- Green gradient-kernel time-derivative bound from a source already bounded
against the gradient-kernel `L¹` mass.  The final step uses the delivered
`1 / sqrt μ` Green-gradient mass. -/
theorem resolver_grad_time_deriv_bound_of_ut
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀} {c T' : ℝ}
    (_I : FluxTimeRegularityInputs p S c T')
    {source : ℝ → ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hkernel : ∀ s ∈ Icc c T', ∀ x ∈ Icc (0 : ℝ) 1,
      |∫ y in (0 : ℝ)..1,
          ShenWork.PDE.neumannEllipticGreenDx p.μ x y * source s y|
        ≤ A * ∫ y in (0 : ℝ)..1,
          |ShenWork.PDE.neumannEllipticGreenDx p.μ x y|) :
    ∀ s ∈ Icc c T', ∀ x ∈ Icc (0 : ℝ) 1,
      |∫ y in (0 : ℝ)..1,
          ShenWork.PDE.neumannEllipticGreenDx p.μ x y * source s y|
        ≤ A * (1 / Real.sqrt p.μ) := by
  intro s hs x hx
  calc
    |∫ y in (0 : ℝ)..1,
        ShenWork.PDE.neumannEllipticGreenDx p.μ x y * source s y|
        ≤ A * ∫ y in (0 : ℝ)..1,
            |ShenWork.PDE.neumannEllipticGreenDx p.μ x y| :=
      hkernel s hs x hx
    _ ≤ A * (1 / Real.sqrt p.μ) :=
      mul_le_mul_of_nonneg_left
        (ShenWork.PDE.neumannEllipticGreenDx_l1_le p.hμ x hx) hA

/-- Coefficient-uniform bound for the committed chem-div time-derivative field
from a slab-continuity hypothesis and a pointwise `L∞` bound on the field. -/
theorem flux_time_deriv_bound_of_inputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀} {c T' : ℝ}
    (_I : FluxTimeRegularityInputs p S c T')
    {B : ℝ} (hB : 0 ≤ B)
    (hflux_cont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p S.u))
      (Icc c T' ×ˢ Icc (0 : ℝ) 1))
    (hfield_bound : ∀ s ∈ Icc c T', ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivTimeDerivativeLift p S.u s x| ≤ B) :
    ∀ s ∈ Icc c T', ∀ k,
      |coupledChemDivAdot p S.u s k| ≤ 2 * B := by
  intro s hs k
  have hslice : ContinuousOn
      (fun x => coupledChemDivTimeDerivativeLift p S.u s x)
      (Icc (0 : ℝ) 1) := by
    have hpair : ContinuousOn (fun x : ℝ => (s, x)) (Icc (0 : ℝ) 1) := by
      fun_prop
    have hmem : ∀ x ∈ Icc (0 : ℝ) 1,
        (s, x) ∈ Icc c T' ×ˢ Icc (0 : ℝ) 1 := by
      intro x hx
      exact ⟨hs, hx⟩
    simpa [Function.uncurry] using hflux_cont.comp hpair hmem
  simpa [coupledChemDivAdot] using
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hslice hB (hfield_bound s hs) k

/-- Positive-window flux regularity package in the exact shape needed by the
conjugate chem-div source-time-`C¹` constructor. -/
structure FluxTimeRegularityPackage
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) (c T' : ℝ) where
  inputs : FluxTimeRegularityInputs p S c T'
  hchain : CoupledChemDivLocalChainRule p S.u
  hflux_cont : ContinuousOn
    (Function.uncurry (coupledChemDivTimeDerivativeLift p S.u))
    (Icc c T' ×ˢ Icc (0 : ℝ) 1)
  Bdot : ℝ
  hBdot : 0 ≤ Bdot
  hfield_bound : ∀ s ∈ Icc c T', ∀ x ∈ Icc (0 : ℝ) 1,
    |coupledChemDivTimeDerivativeLift p S.u s x| ≤ Bdot

/-- Extract the local chain-rule structure carried by the flux-regularity
package. -/
theorem coupledChemDivLocalChainRule_of_fluxTimeRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀} {c T' : ℝ}
    (R : FluxTimeRegularityPackage p S c T') :
    CoupledChemDivLocalChainRule p S.u :=
  R.hchain

/-- Final wiring into the existing positive-window chem-div source package. -/
noncomputable def chemDivSource_duhamelSourceTimeC1On_of_fluxTimeRegularity
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {S : ConjugateMildSolutionData p u₀} {c T' : ℝ}
    (R : FluxTimeRegularityPackage p S c T')
    (envelope : ℕ → ℝ) (henv_sum : Summable envelope)
    (henv : ∀ s ∈ Icc c T', ∀ k,
      |coupledChemDivSourceCoeffs p S.u s k| ≤ envelope k) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p S.u) c T' :=
  chemDivSource_duhamelSourceTimeC1On_of_timeRegularFlux
    (p := p) (S := S) R.inputs.hc R.inputs.hT'
    envelope henv_sum henv
    (coupledChemDivLocalChainRule_of_fluxTimeRegularity R)
    R.hflux_cont (2 * R.Bdot)
    (flux_time_deriv_bound_of_inputs R.inputs R.hBdot
      R.hflux_cont R.hfield_bound)

end ShenWork.IntervalCoupledRegularityBootstrap
