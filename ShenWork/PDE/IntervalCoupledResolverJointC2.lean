import ShenWork.PDE.IntervalResolverJointC2
import ShenWork.PDE.IntervalCoupledRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2
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

end ShenWork.IntervalCoupledRegularityBootstrap
