/-
  Closed positive time windows for the resolver time derivative.

  The existing `ResolverHasSpectralAgreement U v` package supplies spectral data
  only at times `t₀` with `t₀ < U`.  Consequently the current machinery proves
  a closed window ending at `T` whenever `T` is strictly inside such a horizon.

  The literal horizon-endpoint theorem with only `ResolverHasSpectralAgreement T v`
  would need an additional spectral-agreement fact at `t₀ = T`.
-/
import ShenWork.Paper2.IntervalResolverTimeRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalResolverTimeRegularity
open Set Topology

noncomputable section

namespace ShenWork.IntervalResolverTimeEndpoint

/-- Fixed-domain-point time-derivative continuity on a closed positive window.

This is the closed-window restriction of
`resolver_timeDeriv_continuousOn` when the right endpoint is strictly inside
the spectral horizon. -/
theorem resolver_timeDeriv_continuousOn_Icc_of_lt_horizon
    {U T c : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement U v)
    (hc : 0 < c) (hTU : T < U) (x : intervalDomainPoint) :
    ContinuousOn (fun s => deriv (fun r => v r x) s) (Icc c T) := by
  exact (resolver_timeDeriv_continuousOn H x).mono (by
    intro s hs
    exact ⟨lt_of_lt_of_le hc hs.1, lt_of_le_of_lt hs.2 hTU⟩)

/-- Lifted fixed-`x` time-derivative continuity on a closed positive window.

This is obtained by composing the joint closed-spatial theorem with
`s ↦ (s, x)`. -/
theorem resolver_lift_timeDeriv_continuousOn_Icc_of_lt_horizon
    {U T c x : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement U v)
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => deriv (fun r => intervalDomainLift (v r) x) s)
      (Icc c T) := by
  have hjoint :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s => intervalDomainLift (v s) x) t))
        (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
    (resolver_timeDeriv_jointContinuousOn_closed H).mono (by
      intro p hp
      obtain ⟨ht, hx'⟩ := mem_prod.1 hp
      exact mem_prod.2
        ⟨⟨lt_of_lt_of_le hc ht.1, lt_of_le_of_lt ht.2 hTU⟩, hx'⟩)
  have hmaps : MapsTo (fun s : ℝ => (s, x)) (Icc c T)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    intro s hs
    exact mem_prod.2 ⟨hs, hx⟩
  have hcont : ContinuousOn (fun s : ℝ => (s, x)) (Icc c T) :=
    (continuous_id.prodMk continuous_const).continuousOn
  simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
    hjoint.comp hcont hmaps

/-- Joint continuity on `Icc c T × [0,1]`, with `T` strictly inside the
spectral horizon.  This mirrors
`mildSolution_timeDeriv_jointContinuousOn_closed` via
`resolver_timeDeriv_jointContinuousOn_closed`. -/
theorem resolver_timeDeriv_jointContinuousOn_Icc_time_closedSpace_of_lt_horizon
    {U T c : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement U v)
    (hc : 0 < c) (hTU : T < U) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  exact (resolver_timeDeriv_jointContinuousOn_closed H).mono (by
    intro p hp
    obtain ⟨ht, hx⟩ := mem_prod.1 hp
    exact mem_prod.2
      ⟨⟨lt_of_lt_of_le hc ht.1, lt_of_le_of_lt ht.2 hTU⟩, hx⟩)

/-- Lifted fixed-`x` continuity on `Ioc 0 T`, with `T` strictly inside the
spectral horizon. -/
theorem resolver_lift_timeDeriv_continuousOn_Ioc_of_lt_horizon
    {U T x : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement U v)
    (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => deriv (fun r => intervalDomainLift (v r) x) s)
      (Ioc (0 : ℝ) T) := by
  have hjoint :
      ContinuousOn
        (Function.uncurry
          (fun (t : ℝ) (x : ℝ) =>
            deriv (fun s => intervalDomainLift (v s) x) t))
        (Ioc (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) :=
    (resolver_timeDeriv_jointContinuousOn_closed H).mono (by
      intro p hp
      obtain ⟨ht, hx'⟩ := mem_prod.1 hp
      exact mem_prod.2 ⟨⟨ht.1, lt_of_le_of_lt ht.2 hTU⟩, hx'⟩)
  have hmaps : MapsTo (fun s : ℝ => (s, x)) (Ioc (0 : ℝ) T)
      (Ioc (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
    intro s hs
    exact mem_prod.2 ⟨hs, hx⟩
  have hcont : ContinuousOn (fun s : ℝ => (s, x)) (Ioc (0 : ℝ) T) :=
    (continuous_id.prodMk continuous_const).continuousOn
  simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
    hjoint.comp hcont hmaps

/-- Joint continuity on `Ioc 0 T × [0,1]`, with `T` strictly inside the
spectral horizon. -/
theorem resolver_timeDeriv_jointContinuousOn_Ioc_time_closedSpace_of_lt_horizon
    {U T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement U v) (hTU : T < U) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioc (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1) := by
  exact (resolver_timeDeriv_jointContinuousOn_closed H).mono (by
    intro p hp
    obtain ⟨ht, hx⟩ := mem_prod.1 hp
    exact mem_prod.2 ⟨⟨ht.1, lt_of_le_of_lt ht.2 hTU⟩, hx⟩)

end ShenWork.IntervalResolverTimeEndpoint
