import ShenWork.PDE.IntervalResolverSpectralTimeC2

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverJointC2

/-- C2-coefficient strengthened reducer: the analytic spectral certificate may
use `DuhamelSourceTimeC2Coeff`, while the existing spectral-agreement ledger still
stores the weaker `DuhamelSourceTimeC1` package. -/
theorem resolver_jointC2At_of_spectralAgreement_c2Coeff
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement T v)
    {s x : ℝ} (hs0 : 0 < s) (hsT : s < T)
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hC2 :
      ∀ (a₀ : ℕ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
        (_ha₀ : ∀ n, |a₀ n| ≤ M)
        (a : ℝ → ℕ → ℝ)
        (_src : DuhamelSourceTimeC2Coeff a)
        (offset : ℝ) (_hτ : 0 < s - offset),
        (∀ᶠ r in 𝓝 s, ∀ y : intervalDomainPoint,
          v r y =
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
          v r y =
            ∑' n, localRestartCoeff a₀ a (r - offset) n *
              cosineMode n y.1) →
        DuhamelSourceTimeC2Coeff a) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (v q.1) q.2) (s, x) ∧
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => deriv (intervalDomainLift (v q.1)) q.2)
        (s, x) := by
  refine resolver_jointC2At_of_spectralAgreement H hs0 hsT hx ?_
  intro a₀ M hM ha₀ a src offset hτ hagree
  exact hC2 a₀ M hM ha₀ a (lift a₀ M hM ha₀ a src offset hτ hagree)
    offset hτ hagree

end ShenWork.IntervalResolverJointC2
