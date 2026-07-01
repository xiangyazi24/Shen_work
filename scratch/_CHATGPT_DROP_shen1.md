# Q2866 (shen1) — intervalDomain Moser-energy window FTC

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

The smallest honest next theorem is **not** “classical continuity implies the window FTC.”  The clean split is:

1. use the existing interval-domain time-Leibniz theorem to prove the interior derivative statement for
   `Y_p(t) = integratedMoserEnergy intervalDomain u p t`;
2. use the existing closed-energy continuity theorem to supply `ContinuousOn Y_p (Icc t1 t2)`;
3. keep **window integrability of `deriv Y_p`** as an explicit input;
4. apply Mathlib’s interval FTC
   `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.

So `AbsoluteContinuousOn` does **not** have to be an input if you use Mathlib’s FTC lemma with `HasDerivAt + IntervalIntegrable deriv`.  But the integrability of `deriv Y_p` cannot be dropped, and it is not a consequence of the already-proved continuity result alone.

## Placement

Do **not** put this theorem in `ShenWork/PDE/P3MoserIntegratedClosure.lean` if it depends on endpoint-continuity facts from `P3MoserEnergyContinuity`; that would create the wrong dependency direction.

Best placement:

```lean
ShenWork/PDE/P3MoserEnergyContinuity.lean
```

near the existing endpoint-continuity section, because that file already imports both:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz
```

and it already defines/exports:

```lean
IntervalDomainPowerEnergyEndpointContinuity
intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
intervalDomain_powerEnergyEndpointContinuity_of_initialPowerEnergyContinuity
```

An alternative clean placement is a new file:

```lean
ShenWork/PDE/P3MoserEnergyWindowFTC.lean
```

with imports:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic
```

Then later actual-wiring files can import this producer without making `P3MoserIntegratedClosure` concrete-domain-specific.

## The theorem to add

This is the smallest honest producer for the existing abstract package:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- The abstract Moser energy on the concrete interval domain is the plain
`intervalDomainPowerEnergy` from the time-Leibniz file. -/
theorem intervalDomain_integratedMoserEnergy_eq_powerEnergy
    (p : ℝ) (u : ℝ → intervalDomain.Point → ℝ) :
    (fun t : ℝ => integratedMoserEnergy intervalDomain u p t) =
      fun t : ℝ => intervalDomainPowerEnergy p u t := by
  funext t
  unfold integratedMoserEnergy intervalDomainPowerEnergy
  change intervalDomainIntegral (fun x => (u t x) ^ p) =
    ∫ y in (0 : ℝ)..1, (intervalDomainLift (u t) y) ^ p
  unfold intervalDomainIntegral
  refine intervalIntegral.integral_congr (fun y hy => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hy
  simp [intervalDomainLift, hy]

/-- Concrete interval-domain producer for the abstract Moser-energy window FTC.

This theorem intentionally keeps `hderivInt` as an input.  The existing
classical-solution/time-Leibniz API gives the derivative at strict interior
times, and the endpoint-continuity API gives closed-window continuity; neither
one by itself proves integrability of `deriv Y_p` on every closed window. -/
theorem intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hend : IntervalDomainPowerEnergyEndpointContinuity u T p0)
    (hderivInt :
      IntegratedMoserEnergyDerivativeWindowIntegrability
        intervalDomain u T p0) :
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0 := by
  refine ⟨hderivInt, ?_⟩
  intro p hp t1 ht1 t2 ht2
  let Y : ℝ → ℝ := fun τ => integratedMoserEnergy intervalDomain u p τ
  have hab : t1 ≤ t2 := ht2.1

  -- Closed-window continuity of `Y_p` comes from the endpoint-continuity
  -- residual plus the already proved interior continuity theorem.
  have hY_cont : ContinuousOn Y (Set.Icc t1 t2) := by
    have hclosed :
        ContinuousOn
          (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
          (Set.Icc (0 : ℝ) T) :=
      intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity
        hsol hend p hp
    have hsub : Set.Icc t1 t2 ⊆ Set.Icc (0 : ℝ) T := by
      intro s hs
      exact ⟨le_trans ht1.1 hs.1, le_trans hs.2 ht2.2⟩
    simpa [Y, integratedMoserEnergy] using hclosed.mono hsub

  -- The derivative hypothesis for the FTC is only needed on the open interval
  -- `(t1,t2)`, so closed-window endpoints `0` and `T` cause no derivative
  -- obligation.  Strict interior follows from `ht1`, `ht2`, and `s ∈ Ioo t1 t2`.
  have hY_deriv :
      ∀ s ∈ Set.Ioo t1 t2,
        HasDerivAt Y (deriv Y s) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt ht1.1 hs.1
    have hsT : s < T := lt_of_lt_of_le hs.2 ht2.2
    have hpow :=
      intervalDomainPowerEnergy_hasDerivAt
        (p := params) (T := T) (q := p) (u := u) (v := v)
        hsol ⟨hs0, hsT⟩
    have hYeq := intervalDomain_integratedMoserEnergy_eq_powerEnergy p u
    have hpow_deriv :
        HasDerivAt (fun τ => intervalDomainPowerEnergy p u τ)
          (deriv (fun τ => intervalDomainPowerEnergy p u τ) s) s := by
      simpa [hpow.deriv] using hpow
    simpa [Y, hYeq] using hpow_deriv

  -- This is the Mathlib FTC shape already used elsewhere in the repo.
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := t1) (b := t2) (f := Y)
      (f' := fun s : ℝ => deriv Y s)
      hab hY_cont hY_deriv (hderivInt p hp t1 ht1 t2 ht2)
  simpa [Y] using hFTC

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

I would expect at most minor namespace/import adjustment around `intervalDomainIntegral` or the exact simplification of `hYeq`; the proof route is the important part and matches existing repo idioms.

## Why this is the right split

### Existing derivative API is enough for the open interval

`IntervalDomainLpTimeLeibniz.lean` already has the key interior derivative facts:

```lean
intervalDomainPowerEnergy_hasDerivAt
intervalDomain_lp_timeLeibniz
intervalDomain_lp_energy_hLpTime_frontier
```

For the window FTC, the derivative obligation is only on `Set.Ioo t1 t2`.  If
`t1 ∈ Icc 0 T`, `t2 ∈ Icc t1 T`, and `s ∈ Ioo t1 t2`, then:

```lean
have hs0 : 0 < s := lt_of_le_of_lt ht1.1 hs.1
have hsT : s < T := lt_of_lt_of_le hs.2 ht2.2
```

so the existing strict-time Leibniz theorem applies.  No endpoint derivative is needed.

### Existing closed continuity is a separate endpoint input

`intervalDomain_energyContinuousOn_Icc_of_classical_endpointContinuity` is exactly the right continuity producer for the FTC’s `ContinuousOn Y (Icc t1 t2)` assumption.  It depends on:

```lean
IntervalDomainPowerEnergyEndpointContinuity u T p0
```

which is honest: the classical solution record only gives interior-time regularity; the closed interval endpoints need compatibility data.  The right endpoint can be handled from a global classical solution on a longer horizon, but the left endpoint is still represented by the existing `IntervalDomainInitialPowerEnergyContinuityAtZero` residual.

### Mathlib FTC exists; absolute continuity is optional, not required here

The repo already uses:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
```

in `ShenWork/Paper2/IntervalRestartVariationOfConstants.lean`.  Its use pattern is:

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
  (a := a) (b := b) (f := F) (f' := F')
  hab hF_cont hF_deriv hF'_intervalIntegrable
```

That is the same pattern needed here.  Therefore an explicit `AbsoluteContinuousOn` field is not necessary for the window FTC package, provided we can supply `IntervalIntegrable (fun s => deriv Y s)`.

But this is **not** saying continuity alone gives FTC.  The derivative integrability field is doing essential work.

## What remains genuinely open

The theorem above still requires:

```lean
IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0
```

This is the real remaining analytic producer if you want a fully concrete `IntegratedMoserEnergyWindowFTC`.

A weaker strict-window result should be reachable from the existing APIs:

```lean
theorem intervalDomain_integratedMoserEnergy_deriv_intervalIntegrable_of_strictWindow
    {params : CM2Params} {T p a b : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ha : 0 < a) (hb : b < T) :
    IntervalIntegrable
      (fun s => deriv (fun τ => integratedMoserEnergy intervalDomain u p τ) s)
      volume a b := by
  -- route:
  -- 1. use `intervalDomainPowerDeriv_continuousOn` on the compact slab
  --    `Icc a b ×ˢ Icc 0 1 ⊆ Ioo 0 T ×ˢ Icc 0 1`;
  -- 2. prove continuity/interval-integrability in `s` of
  --    `s ↦ ∫ y in 0..1, intervalDomainPowerDeriv p u s y`;
  -- 3. use `intervalDomainPowerEnergy_hasDerivAt` to identify this explicit
  --    RHS with `deriv Y s` for all `s ∈ Ioo a b`;
  -- 4. transfer interval integrability by congruence, endpoints ignored.
  admit
```

However, that strict-window theorem does **not** automatically give the full closed-window integrability package required by `IntegratedMoserEnergyWindowFTC`, because the full structure quantifies windows touching `0` and `T`.  Current interior classical regularity gives no uniform control of the time derivative as `s ↓ 0`.  So for the full closed-window package, one of the following must remain explicit:

1. `IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0`; or
2. an equivalent explicit RHS integrability residual for
   `s ↦ ∫_0^1 intervalDomainPowerDeriv p u s y dy`; or
3. a stronger absolute-continuity/trace theorem for `Y_p` on `[0,T]`.

The first option is the smallest and aligns exactly with the current `IntegratedMoserEnergyWindowFTC` fields.

## Recommended next PR-sized step

Add only the theorem:

```lean
intervalDomain_integratedMoserEnergyWindowFTC_of_classical_endpoint_derivIntegrable
```

in `P3MoserEnergyContinuity.lean` or a new `P3MoserEnergyWindowFTC.lean`.  This reduces the frontier from “explicit FTC” to the sharper and honest pair:

```lean
IntervalDomainPowerEnergyEndpointContinuity u T p0
IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0
```

Then a later producer can attack derivative-window integrability separately, first for strict windows and then with a left-endpoint trace/integrability residual for windows touching `0`.
