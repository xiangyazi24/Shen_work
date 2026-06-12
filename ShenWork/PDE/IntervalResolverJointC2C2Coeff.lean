import ShenWork.PDE.IntervalResolverSpectralTimeC2

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralTimeC2 (DuhamelSourceTimeC2Coeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverJointC2

/-- C2-coefficient strengthened spectral agreement.

The ordinary `ResolverHasSpectralAgreement` is retained for existing C1/time
regularity consumers, while `exists_c2_data` exposes the same local restart
data with the strengthened source-coefficient package required by the concrete
joint-C2 producer. -/
structure ResolverHasSpectralAgreementC2Coeff
    (T : ℝ) (v : ℝ → intervalDomainPoint → ℝ) : Prop where
  toSpectralAgreement :
    ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement T v
  exists_c2_data : ∀ t₀, 0 < t₀ → t₀ < T →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M)
      (a : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC2Coeff a) (offset : ℝ),
      (0 < t₀ - offset) ∧
      (∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
        v s x = ∑' n, localRestartCoeff a₀ a (s - offset) n *
          cosineMode n x.1)

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

/-- Reducer from the strengthened spectral-agreement package. -/
theorem resolver_jointC2At_of_spectralAgreement_c2Data
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreementC2Coeff T v)
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
        ResolverSpectralJointC2At a₀ a offset s x) :
    ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (v q.1) q.2) (s, x) ∧
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => deriv (intervalDomainLift (v q.1)) q.2)
        (s, x) := by
  rcases H.exists_c2_data s hs0 hsT with
    ⟨a₀, M, hM, ha₀, a, src, offset, hτ, hagree⟩
  have hseries : ResolverSpectralJointC2At a₀ a offset s x :=
    hC2 a₀ M hM ha₀ a src offset hτ hagree
  have hvalue_agree :=
    resolver_value_eventuallyEq_spectralSeries_of_agreement
      (v := v) (a₀ := a₀) (a := a) (offset := offset) hx hagree
  have hgrad_agree :=
    resolver_grad_eventuallyEq_spectralGradSeries_of_agreement
      (v := v) (a₀ := a₀) (a := a) (offset := offset) hx hagree
  exact
    ⟨resolver_value_contDiffAt_of_spectral_eventuallyEq
        hseries.value_c2 hvalue_agree,
      resolver_grad_contDiffAt_of_spectral_eventuallyEq
        hseries.grad_c2 hgrad_agree⟩

end ShenWork.IntervalResolverJointC2
