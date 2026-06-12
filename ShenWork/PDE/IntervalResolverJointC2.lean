import ShenWork.Paper2.IntervalResolverTimeRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverJointC2

/-- The local spectral series supplied by `ResolverHasSpectralAgreement`. -/
def resolverSpectralSeries
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset : ℝ) :
    ℝ × ℝ → ℝ :=
  fun q => ∑' n, localRestartCoeff a₀ a (q.1 - offset) n * cosineMode n q.2

/-- The spatial derivative of the local spectral series. -/
def resolverSpectralGradSeries
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset : ℝ) :
    ℝ × ℝ → ℝ :=
  fun q => deriv (fun y => resolverSpectralSeries a₀ a offset (q.1, y)) q.2

/-- Pointwise C² certificate for the termwise-differentiated spectral series.

The intended producer for this certificate is the uniform convergence argument
mirroring `resolver_jointContinuousOn_closed`, with the extra `(kπ)^j`
weights for all `t,x` partials of total order at most two. -/
structure ResolverSpectralJointC2At
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset s x : ℝ) : Prop where
  value_c2 :
    ContDiffAt ℝ 2 (resolverSpectralSeries a₀ a offset) (s, x)
  grad_c2 :
    ContDiffAt ℝ 2 (resolverSpectralGradSeries a₀ a offset) (s, x)

/-- Transfer joint `C²` from an agreeing local spectral series to the resolver. -/
theorem resolver_value_contDiffAt_of_spectral_eventuallyEq
    {v : ℝ → intervalDomainPoint → ℝ} {series : ℝ × ℝ → ℝ} {s x : ℝ}
    (hseries : ContDiffAt ℝ 2 series (s, x))
    (hagrees :
      (fun q : ℝ × ℝ => intervalDomainLift (v q.1) q.2)
        =ᶠ[𝓝 (s, x)] series) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (v q.1) q.2) (s, x) :=
  hseries.congr_of_eventuallyEq hagrees

/-- Transfer joint `C²` from the spatial derivative of an agreeing local
spectral series to `∂ₓv`. -/
theorem resolver_grad_contDiffAt_of_spectral_eventuallyEq
    {v : ℝ → intervalDomainPoint → ℝ} {gradSeries : ℝ × ℝ → ℝ} {s x : ℝ}
    (hseries : ContDiffAt ℝ 2 gradSeries (s, x))
    (hagrees :
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (v q.1)) q.2) =ᶠ[𝓝 (s, x)] gradSeries) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => deriv (intervalDomainLift (v q.1)) q.2) (s, x) :=
  hseries.congr_of_eventuallyEq hagrees

/-- The value component of `ResolverHasSpectralAgreement` as a neighborhood
equality of the lifted two-variable resolver with its local spectral series. -/
theorem resolver_value_eventuallyEq_spectralSeries_of_agreement
    {v : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hagree :
      ∀ᶠ r in 𝓝 s, ∀ y : intervalDomainPoint,
        v r y =
          ∑' n, localRestartCoeff a₀ a (r - offset) n * cosineMode n y.1) :
    (fun q : ℝ × ℝ => intervalDomainLift (v q.1) q.2)
      =ᶠ[𝓝 (s, x)] resolverSpectralSeries a₀ a offset := by
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ := eventually_nhds_iff.1 hagree
  have hprod : V ×ˢ Ioo (0 : ℝ) 1 ∈ 𝓝 (s, x) :=
    (hV_open.prod isOpen_Ioo).mem_nhds (mem_prod.2 ⟨hV_mem, hx⟩)
  refine eventually_of_mem hprod ?_
  intro q hq
  obtain ⟨ht, hxq⟩ := mem_prod.1 hq
  have hxIcc : q.2 ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hxq
  simp [resolverSpectralSeries, intervalDomainLift, hxIcc,
    hV_agree q.1 ht ⟨q.2, hxIcc⟩]

/-- The spatial derivative component of `ResolverHasSpectralAgreement` as a
neighborhood equality with the derivative of the local spectral series. -/
theorem resolver_grad_eventuallyEq_spectralGradSeries_of_agreement
    {v : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hagree :
      ∀ᶠ r in 𝓝 s, ∀ y : intervalDomainPoint,
        v r y =
          ∑' n, localRestartCoeff a₀ a (r - offset) n * cosineMode n y.1) :
    (fun q : ℝ × ℝ => deriv (intervalDomainLift (v q.1)) q.2)
      =ᶠ[𝓝 (s, x)] resolverSpectralGradSeries a₀ a offset := by
  obtain ⟨V, hV_agree, hV_open, hV_mem⟩ := eventually_nhds_iff.1 hagree
  have hprod : V ×ˢ Ioo (0 : ℝ) 1 ∈ 𝓝 (s, x) :=
    (hV_open.prod isOpen_Ioo).mem_nhds (mem_prod.2 ⟨hV_mem, hx⟩)
  refine eventually_of_mem hprod ?_
  intro q hq
  obtain ⟨ht, hxq⟩ := mem_prod.1 hq
  have hlocal :
      intervalDomainLift (v q.1) =ᶠ[𝓝 q.2]
        fun y : ℝ => resolverSpectralSeries a₀ a offset (q.1, y) := by
    filter_upwards [Ioo_mem_nhds hxq.1 hxq.2] with y hy
    have hyIcc : y ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hy
    simp [resolverSpectralSeries, intervalDomainLift, hyIcc,
      hV_agree q.1 ht ⟨y, hyIcc⟩]
  simpa [resolverSpectralGradSeries] using hlocal.deriv_eq

/-- Resolver joint `C²` at an interior point, reduced to the spectral-series
uniform-`C²` certificate for the local restart expansion supplied by
`ResolverHasSpectralAgreement`. -/
theorem resolver_jointC2At_of_spectralAgreement
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ShenWork.IntervalResolverTimeRegularity.ResolverHasSpectralAgreement T v)
    {s x : ℝ} (hs0 : 0 < s) (hsT : s < T)
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hC2 :
      ∀ (a₀ : ℕ → ℝ) (M : ℝ) (_hM : 0 ≤ M)
        (_ha₀ : ∀ n, |a₀ n| ≤ M)
        (a : ℝ → ℕ → ℝ)
        (_src : ShenWork.IntervalDuhamelClosedC2.DuhamelSourceTimeC1 a)
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
  rcases H.exists_data s hs0 hsT with
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
