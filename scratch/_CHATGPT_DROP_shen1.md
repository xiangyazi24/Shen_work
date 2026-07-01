# Q2875 (shen1) — closed-window derivative integrability after strict-window closure

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

The full closed-window

```lean
IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0
```

should **not** be claimed from the current APIs consisting only of:

* global classical solution;
* endpoint energy continuity;
* strict-window derivative integrability/continuity.

The right endpoint is not a real obstruction once you have a global classical solution: for a window `[a,b]` with `0 < a` and `b ≤ T`, apply the strict-window theorem on the longer horizon `T + 1`, so `b < T + 1` even when `b = T`.

The left endpoint is the real obstruction.  Windows starting at `0` require integrability of

```lean
deriv (fun τ => integratedMoserEnergy intervalDomain u q τ)
```

on `(0,b]`.  Strict-window integrability on every `[a,b]` with `a > 0` does not imply integrability on `(0,b]`.  Endpoint continuity of the energy also does not imply absolute integrability of the derivative near `0`: a continuous function on `[0,b]` may be differentiable on `(0,b]` with derivative locally integrable on every `[a,b]` but not Lebesgue integrable near `0`.  Mathlib’s `IntervalIntegrable` is an actual integrability requirement, not an improper/conditional FTC placeholder.

So the smallest honest bridge is: prove all positive-left-start windows from global classical + strict-window theorem, and keep only **initial-window derivative integrability** as a residual.

## Recommended exact interface

Put these declarations in `ShenWork/PDE/P3MoserEnergyContinuity.lean` after the strict-window theorem, or in a small new file such as:

```lean
ShenWork/PDE/P3MoserEnergyDerivativeWindow.lean
```

with imports:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Tactic
```

The code below is designed as no-sorry interface/wiring code.  It uses the compiled strict theorem named in the question:

```lean
intervalDomain_deriv_intervalIntegrable_of_strictWindow
```

If your local theorem has a longer name, only that final call needs renaming.

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

This is exactly the part not supplied by strict-window integrability: windows
whose left endpoint is `0`.  It deliberately asks for the actual derivative
profile consumed by `IntegratedMoserEnergyDerivativeWindowIntegrability`, avoiding
any endpoint-time derivative-identification issue at `0`. -/
def IntegratedMoserEnergyDerivativeInitialWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u q τ) s)
        volume 0 b

/-- Positive-left-start derivative integrability for all windows inside `[0,T]`.

For `intervalDomain`, this will be supplied by global classical regularity plus
the strict-window theorem, using a longer horizon to include the right endpoint
`T`. -/
def IntegratedMoserEnergyDerivativePositiveStartWindowIntegrability
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ a b, 0 < a → a ≤ b → b ≤ T →
      IntervalIntegrable
        (fun s => deriv (fun τ => integratedMoserEnergy D u q τ) s)
        volume a b

/-- Pure bridge from the initial-window residual plus all positive-left-start
windows to the full closed-window derivative-integrability package.

This theorem is intentionally abstract in `D`: it is just the case split on
whether the left endpoint is `0`. -/
theorem integratedMoserEnergyDerivativeWindowIntegrability_of_initial_and_positiveStart
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ} {T p0 : ℝ}
    (hinit : IntegratedMoserEnergyDerivativeInitialWindowIntegrability D u T p0)
    (hpos : IntegratedMoserEnergyDerivativePositiveStartWindowIntegrability D u T p0) :
    IntegratedMoserEnergyDerivativeWindowIntegrability D u T p0 := by
  intro q hq t1 ht1 t2 ht2
  by_cases ht10 : t1 = 0
  · subst t1
    exact hinit q hq t2 ht2
  · have ht1_pos : 0 < t1 := by
      exact lt_of_le_of_ne ht1.1 (fun h : (0 : ℝ) = t1 => ht10 h.symm)
    exact hpos q hq t1 t2 ht1_pos ht2.1 ht2.2

/-- A global classical interval-domain solution supplies all derivative-integrable
windows with positive left endpoint.

The right endpoint `T` is handled by applying the strict-window theorem on the
longer horizon `T + 1`. -/
theorem intervalDomain_integratedMoserEnergyDerivativePositiveStartWindowIntegrability_of_global_classical
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v) :
    IntegratedMoserEnergyDerivativePositiveStartWindowIntegrability
      intervalDomain u T p0 := by
  intro q _hq a b ha hab hbT
  have hTplus_pos : 0 < T + 1 := by
    have hT_pos : 0 < T := lt_of_lt_of_le ha (le_trans hab hbT)
    linarith
  have hsolLong :
      IsPaper2ClassicalSolution intervalDomain params (T + 1) u v :=
    hglobal.classical hTplus_pos
  have hb_lt_Tplus : b < T + 1 := by
    linarith
  exact
    intervalDomain_deriv_intervalIntegrable_of_strictWindow
      (params := params) (T := T + 1) (q := q) (a := a) (b := b)
      (u := u) (v := v) hsolLong ha hab hb_lt_Tplus

/-- Full closed-window derivative integrability from global classical regularity
plus the honest left-endpoint derivative-integrability residual. -/
theorem intervalDomain_integratedMoserEnergyDerivativeWindowIntegrability_of_global_classical_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hinit :
      IntegratedMoserEnergyDerivativeInitialWindowIntegrability
        intervalDomain u T p0) :
    IntegratedMoserEnergyDerivativeWindowIntegrability intervalDomain u T p0 :=
  integratedMoserEnergyDerivativeWindowIntegrability_of_initial_and_positiveStart
    hinit
    (intervalDomain_integratedMoserEnergyDerivativePositiveStartWindowIntegrability_of_global_classical
      (params := params) (T := T) (p0 := p0) (u := u) (v := v) hglobal)

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

## Why endpoint energy continuity is not enough

The full FTC package has two logically separate requirements:

```lean
IntervalIntegrable (deriv Y) volume t1 t2
∫ deriv Y = Y t2 - Y t1
```

Endpoint continuity helps with the `ContinuousOn Y (Icc t1 t2)` side of Mathlib’s FTC, but it does not produce the first line.  In particular, the theorem already used for FTC,

```lean
intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
```

requires derivative interval integrability as an input.  There is no Mathlib theorem of the form “continuous on `[0,b]`, differentiable on `(0,b)`, and locally integrable derivative on every `[a,b]` implies `IntervalIntegrable deriv 0 b`,” because that statement is false for Lebesgue/Bochner integrability.

A typical analytic counter-shape is a function continuous at `0`, differentiable on `(0,b]`, whose derivative behaves like a non-integrable oscillatory/singular term near `0`.  It can be locally integrable on every `[a,b]`, `a>0`, while not integrable on `(0,b]`.  Thus the left endpoint needs a genuine trace/integrability theorem, not a continuity wrapper.

## Optional more PDE-shaped residual

The residual above asks directly for the derivative profile.  If you prefer a producer closer to the interval-domain Leibniz APIs, introduce a second residual for the explicit RHS:

```lean
def IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => intervalDomainPowerEnergyDerivIntegral q u s)
        volume 0 b
```

Then prove a separate conversion to
`IntegratedMoserEnergyDerivativeInitialWindowIntegrability` using the derivative-identification theorem on the longer global horizon `T+1` and an a.e.-congruence lemma for `IntervalIntegrable`.  I would not make this the first bridge unless you have confirmed the exact local lemma name for interval-integrability under a.e. equality in Mathlib 4.29.1.  The direct derivative residual above is smaller and immediately wires into the existing abstract package.

## Final recommended frontier statement

The headline frontier after the compiled strict-window work should be:

```lean
IntegratedMoserEnergyDerivativeInitialWindowIntegrability intervalDomain u T p0
```

not the full closed-window predicate.  With global classical regularity, the theorem above reduces the full closed-window predicate exactly to that left-endpoint residual, with no axioms and no fake endpoint differentiability.
