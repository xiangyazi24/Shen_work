# Q2876 (shen1) — initial-window derivative integrability bridge

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

I do **not** see a way to produce

```lean
IntegratedMoserEnergyDerivativeInitialWindowIntegrability intervalDomain u T p0
```

from the existing initial-trace/global-classical/endpoint-energy-continuity APIs alone.

Reason:

* `IsPaper2GlobalClassicalSolution` is `∀ T > 0, IsPaper2ClassicalSolution ... T`, and `IsPaper2ClassicalSolution` gives regularity only for strict interior times `0 < t < T`.
* `InitialTrace` is a value convergence/sup-norm approach statement as used by `conjugatePicardLimit_initialTrace_of_conjugate_data`; it does not bound or integrate `∂ₜ u` near `t = 0`.
* endpoint power-energy continuity gives `ContinuousWithinAt Y (Icc 0 T) 0`, but continuity of `Y` at `0` plus differentiability on `(0,T)` does not imply `IntervalIntegrable (deriv Y) volume 0 b`.
* the strict-window theorem gives integrability on every `[a,b]`, `a > 0`, but Mathlib’s `IntervalIntegrable` on `0..b` is actual Lebesgue/Bochner integrability over `Ioc 0 b`; local integrability away from `0` is insufficient.

The smallest honest PDE-shaped residual is therefore not the derivative of the abstract energy directly, but the **explicit time-Leibniz RHS profile**:

```lean
s ↦ intervalDomainPowerEnergyDerivIntegral q u s
```

integrable on initial windows.  Global classical then identifies this profile with the derivative of `integratedMoserEnergy` for every `s > 0`, and `IntervalIntegrable.congr` transfers integrability on `Ioc 0 b`.  This is a no-sorry bridge and keeps the remaining PDE work exactly where it belongs: prove a near-`0` integrability estimate for the explicit profile.

## Code to add

Put this in `ShenWork/PDE/P3MoserEnergyContinuity.lean`, after the current strict-window derivative-integrability facts and after the existing definition

```lean
def intervalDomainPowerEnergyDerivIntegral
    (q : ℝ) (u : ℝ → intervalDomain.Point → ℝ) (s : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u s y
```

If `IntegratedMoserEnergyDerivativeInitialWindowIntegrability` is already defined locally, omit its duplicate definition below.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Tactic

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Initial-window derivative-integrability residual for Moser energies.

This is the exact left-endpoint piece missing after strict-window integrability:
`IntervalIntegrable` over `0..b` means integrability on `Ioc 0 b`, so no value
or derivative at the endpoint `0` itself is requested. -/
def IntegratedMoserEnergyDerivativeInitialWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u q τ) s)
        volume 0 b

/-- PDE-shaped initial-window residual: integrability near `t = 0` of the
explicit time-Leibniz RHS for the interval-domain power energy.

This is the preferred residual because it talks about the concrete producer
`intervalDomainPowerDeriv`, not about an opaque `deriv` of an already-integrated
energy. -/
def IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        volume 0 b

/-- At every positive time, global classical regularity identifies the derivative
of the abstract integrated Moser energy with the explicit interval-domain
power-derivative integral.

The proof uses the horizon `s + 1`, so it never needs a pre-selected finite
horizon and never touches `s = 0`. -/
theorem intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral_of_global_pos
    {params : CM2Params} {q s : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hs0 : 0 < s) :
    deriv (fun τ => integratedMoserEnergy intervalDomain u q τ) s =
      intervalDomainPowerEnergyDerivIntegral q u s := by
  have hTpos : 0 < s + 1 := by linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain params (s + 1) u v :=
    hglobal.classical hTpos
  have hpow :
      HasDerivAt (fun τ => intervalDomainPowerEnergy q u τ)
        (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u s y) s :=
    intervalDomainPowerEnergy_hasDerivAt
      (p := params) (T := s + 1) (q := q) (u := u) (v := v)
      hsol ⟨hs0, by linarith⟩
  have hYeq :
      (fun τ : ℝ => integratedMoserEnergy intervalDomain u q τ) =
        fun τ : ℝ => intervalDomainPowerEnergy q u τ := by
    funext τ
    unfold integratedMoserEnergy intervalDomainPowerEnergy
    change intervalDomainIntegral (fun x => (u τ x) ^ q) =
      ∫ y in (0 : ℝ)..1, (intervalDomainLift (u τ) y) ^ q
    unfold intervalDomainIntegral
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hy
    simp [intervalDomainLift, hy]
  rw [hYeq]
  simpa [intervalDomainPowerEnergyDerivIntegral] using hpow.deriv

/-- No-sorry bridge from explicit initial-window integrability of the
Leibniz-RHS profile to initial-window integrability of the actual derivative of
`integratedMoserEnergy`.

The congruence is on `Ioc 0 b` (via `Set.uIoc_of_le`), so every relevant time is
strictly positive and the global-classical derivative-identification lemma
applies. -/
theorem intervalDomain_integratedMoserEnergyDerivativeInitialWindowIntegrability_of_powerDerivIntegral_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hpowInit :
      IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0) :
    IntegratedMoserEnergyDerivativeInitialWindowIntegrability
      intervalDomain u T p0 := by
  intro q hq b hb
  have hpowInt :
      IntervalIntegrable
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        volume 0 b :=
    hpowInit q hq b hb
  refine IntervalIntegrable.congr ?_ hpowInt
  intro s hs
  rw [Set.uIoc_of_le hb.1] at hs
  exact
    intervalDomain_integratedMoserEnergy_deriv_eq_powerDerivIntegral_of_global_pos
      (params := params) (q := q) (s := s) (u := u) (v := v)
      hglobal hs.1

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

## Why this is the right residual

The residual

```lean
IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0
```

is strictly more PDE-shaped than asking directly for

```lean
IntegratedMoserEnergyDerivativeInitialWindowIntegrability intervalDomain u T p0
```

because it targets the concrete integrand produced by the interval-domain time-Leibniz API:

```lean
intervalDomainPowerDeriv q u s y
  = q * (intervalDomainLift (u s) y) ^ (q - 1) *
      deriv (fun r => intervalDomainLift (u r) y) s
```

A later analytic producer can prove it using small-time estimates for `u`, `∂ₜu`, or the PDE RHS.  That is a genuine near-initial-time estimate.  It cannot be replaced by `InitialTrace`, because `InitialTrace` only controls `u(t) → u₀` in sup norm, not the integrability of `∂ₜu` or of the chain-rule energy derivative near `0`.

## Optional even-more-PDE residual

If you want one level closer to the PDE equation, define the residual in terms of the weighted time term already used in `IntervalDomainLpTimeLeibniz.lean`:

```lean
def IntervalDomainLpWeightedTimeTermInitialWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => q * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm q u s))
        volume 0 b
```

Then convert this to `IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability` using the compiled identity

```lean
intervalDomainPowerTimeTerm_eq_scaled_weighted
```

at positive times, again by `IntervalIntegrable.congr` on `Ioc 0 b`.  I would land the explicit `intervalDomainPowerEnergyDerivIntegral` residual first, because it is syntactically closest to the existing derivative-identification theorem and avoids another layer of positivity rewrites.

## Bottom line

Current APIs produce:

* all strict windows;
* all positive-left-start windows via global classical and horizon extension;
* endpoint **continuity** of the energy.

They do **not** produce the initial derivative integrability needed for the full closed-window FTC.  The smallest honest next residual is initial-window integrability of `intervalDomainPowerEnergyDerivIntegral`; the no-sorry bridge above turns that residual into the abstract `IntegratedMoserEnergyDerivativeInitialWindowIntegrability` consumed downstream.
