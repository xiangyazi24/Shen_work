/-
  V-side time regularity from DuhamelSourceTimeC1 of the resolver
  spectral coefficients.

  The resolver `v(t,x) = ∑ₖ vₖ(t) cos(kπx)` with time-varying
  coefficients. Given `DuhamelSourceTimeC1` of `vₖ`, we derive:
  - `DifferentiableAt` of `v` in time at each interior point
  - Joint (t,x) continuity of `∂ₜv`
  - Joint (t,x) continuity of `v` on closed slabs

  The `DuhamelSourceTimeC1` of the resolver coefficients is obtainable
  from G3 `duhamelSourceTimeC1_mul_weight` applied to the source
  coefficients, but that composition requires F2 (source time-C¹ for
  the Picard limit). Here we prove the DOWNSTREAM consequence
  unconditionally from the spectral hypothesis.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import ShenWork.PDE.IntervalMildTimeDerivContinuity
import ShenWork.PDE.IntervalMildFrontierFromSpectral

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff restartCosineSeries_hasDerivAt_time)
open ShenWork.CosineSpectrum (cosineMode)
open Set Filter Topology

noncomputable section

namespace ShenWork.IntervalResolverTimeRegularity

/-- The spectral hypothesis for v-side regularity: the resolver
series `v(t,x) = ∑ cₖ(t) cos(kπx)` agrees with the mild chemical
concentration in a time neighborhood, and the coefficients `cₖ`
have `DuhamelSourceTimeC1`. -/
structure ResolverHasSpectralAgreement
    (T : ℝ) (v : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_data : ∀ t₀, 0 < t₀ → t₀ < T →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M)
      (a : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 a) (offset : ℝ),
      (0 < t₀ - offset) ∧
      (∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
        v s x = ∑' n, localRestartCoeff a₀ a (s - offset) n *
          cosineMode n x.1)

/-- Convert `ResolverHasSpectralAgreement` to the u-side
`HasTimeNeighborhoodSpectralAgreement`. The types are identical — the
resolver series has the same spectral structure as the solution series. -/
theorem resolverSpectral_to_timeNeighborhoodSpectral
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement T v) :
    ShenWork.IntervalMildTimeDerivContinuity.HasTimeNeighborhoodSpectralAgreement T v where
  exists_data := H.exists_data

/-- **V-side time differentiability**: `DifferentiableAt` of the
resolver in time, from `ResolverHasSpectralAgreement`. -/
theorem resolver_differentiableAt_time
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement T v)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ < T)
    (x : intervalDomainPoint) :
    DifferentiableAt ℝ (fun s => v s x) t₀ := by
  obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ₀, hagree⟩ :=
    H.exists_data t₀ ht₀ ht₀T
  exact (ShenWork.IntervalMildTimeDerivContinuity.mildSolution_hasDerivAt_time
    hM ha₀ src hτ₀ hagree x).differentiableAt

/-- **V-side time derivative continuity**: `ContinuousOn` of the
time derivative for each fixed x. -/
theorem resolver_timeDeriv_continuousOn
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement T v)
    (x : intervalDomainPoint) :
    ContinuousOn (fun s => deriv (fun r => v r x) s) (Ioo (0 : ℝ) T) :=
  ShenWork.IntervalMildTimeDerivContinuity.mildSolution_timeDeriv_continuousOn_fixed_x
    (resolverSpectral_to_timeNeighborhoodSpectral H) x

/-- **V-side joint time-derivative continuity** on the open slab. -/
theorem resolver_timeDeriv_jointContinuousOn
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement T v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Ioo (0 : ℝ) 1) :=
  ShenWork.IntervalMildTimeDerivContinuity.mildSolution_timeDeriv_jointContinuousOn
    (resolverSpectral_to_timeNeighborhoodSpectral H)

/-- **V-side joint solution continuity** on the closed slab. -/
theorem resolver_jointContinuousOn_closed
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement T v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) => intervalDomainLift (v t) x))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  ShenWork.IntervalMildFrontierFromSpectral.mildSolution_jointContinuousOn_closed
    (resolverSpectral_to_timeNeighborhoodSpectral H)

/-- **V-side joint time-derivative continuity** on the closed slab. -/
theorem resolver_timeDeriv_jointContinuousOn_closed
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement T v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
  ShenWork.IntervalMildFrontierFromSpectral.mildSolution_timeDeriv_jointContinuousOn_closed
    (resolverSpectral_to_timeNeighborhoodSpectral H)

end ShenWork.IntervalResolverTimeRegularity
