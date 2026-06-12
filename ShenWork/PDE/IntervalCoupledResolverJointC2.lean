import ShenWork.PDE.IntervalResolverJointC2C2Coeff
import ShenWork.PDE.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalCoupledRegularityBootstrap

/-- Coupled-chemical resolver joint `C²` at an interior point, from the committed
resolver spectral-agreement package plus the local uniform-`C²` spectral-series
certificate. -/
theorem coupledChemicalConcentration_resolver_jointC2At
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U s x : ℝ}
    (H :
      ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement U
        (coupledChemicalConcentration p u))
    (hs0 : 0 < s) (hsU : s < U) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hC2 :
      ∀ (a₀ : ℕ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
        (_ha₀ : ∀ n, |a₀ n| ≤ M)
        (a : ℝ → ℕ → ℝ)
        (_src : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 a)
        (offset : ℝ) (_hτ : 0 < s - offset),
        (∀ᶠ r in 𝓝 s, ∀ y : intervalDomainPoint,
          coupledChemicalConcentration p u r y =
            ∑' n, localRestartCoeff a₀ a (r - offset) n *
              cosineMode n y.1) →
        ResolverSpectralJointC2At a₀ a offset s x) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        (s, x) ∧
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
            q.2)
        (s, x) :=
  resolver_jointC2At_of_spectralAgreement H hs0 hsU hx hC2

/-- C2-coefficient strengthened coupled resolver reducer.  This is the same
transfer as `coupledChemicalConcentration_resolver_jointC2At`, but lets the
spectral-series producer consume the strengthened `DuhamelSourceTimeC2Coeff`
package while the agreement ledger still stores `DuhamelSourceTimeC1`. -/
theorem coupledChemicalConcentration_resolver_jointC2At_c2Coeff
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U s x : ℝ}
    (H :
      ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement U
        (coupledChemicalConcentration p u))
    (hs0 : 0 < s) (hsU : s < U) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hC2 :
      ∀ (a₀ : ℕ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
        (_ha₀ : ∀ n, |a₀ n| ≤ M)
        (a : ℝ → ℕ → ℝ)
        (_src : DuhamelSourceTimeC2Coeff a)
        (offset : ℝ) (_hτ : 0 < s - offset),
        (∀ᶠ r in 𝓝 s, ∀ y : intervalDomainPoint,
          coupledChemicalConcentration p u r y =
            ∑' n, localRestartCoeff a₀ a (r - offset) n *
              cosineMode n y.1) →
        ResolverSpectralJointC2At a₀ a offset s x)
    (lift :
      ∀ (a₀ : ℕ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
        (_ha₀ : ∀ n, |a₀ n| ≤ M)
        (a : ℝ → ℕ → ℝ)
        (_src : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 a)
        (offset : ℝ) (_hτ : 0 < s - offset),
        (∀ᶠ r in 𝓝 s, ∀ y : intervalDomainPoint,
          coupledChemicalConcentration p u r y =
            ∑' n, localRestartCoeff a₀ a (r - offset) n *
              cosineMode n y.1) →
        DuhamelSourceTimeC2Coeff a) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        (s, x) ∧
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
            q.2)
        (s, x) :=
  resolver_jointC2At_of_spectralAgreement_c2Coeff
    H hs0 hsU hx hC2 lift

/-- Coupled-chemical resolver joint `C²` from the C2-coefficient strengthened
spectral-agreement package. -/
theorem coupledChemicalConcentration_resolver_jointC2At_c2Data
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U s x : ℝ}
    (H : ResolverHasSpectralAgreementC2Coeff U
        (coupledChemicalConcentration p u))
    (hs0 : 0 < s) (hsU : s < U) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hC2 :
      ∀ (a₀ : ℕ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
        (_ha₀ : ∀ n, |a₀ n| ≤ M)
        (a : ℝ → ℕ → ℝ)
        (_src : DuhamelSourceTimeC2Coeff a)
        (offset : ℝ) (_hτ : 0 < s - offset),
        (∀ᶠ r in 𝓝 s, ∀ y : intervalDomainPoint,
          coupledChemicalConcentration p u r y =
            ∑' n, localRestartCoeff a₀ a (r - offset) n *
              cosineMode n y.1) →
        ResolverSpectralJointC2At a₀ a offset s x) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        (s, x) ∧
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
            q.2)
        (s, x) :=
  resolver_jointC2At_of_spectralAgreement_c2Data
    H hs0 hsU hx hC2

end ShenWork.IntervalCoupledRegularityBootstrap
