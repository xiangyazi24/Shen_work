# Q2877 (shen1) — weighted-time-term initial-window bridge

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

Yes, a no-sorry bridge is available, but not from the weighted-time-term residual **alone** unless positivity is available.  The compiled identity

```lean
intervalDomainPowerTimeTerm_eq_scaled_weighted
```

has the hypothesis

```lean
(hpos : ∀ x : intervalDomain.Point, 0 < u t x)
```

because it rewrites `|u|` to `u` and uses `Real.rpow_add` on positive bases.  Therefore the thinnest correct bridge is:

1. a pure bridge assuming positive slices at all positive times;
2. a global-classical wrapper, since `IsPaper2GlobalClassicalSolution` supplies positivity for every `s > 0` by using horizon `s + 1`.

This is robust for `b = 0`: the interval-integrability congruence is over `uIoc 0 b`; when `b = 0` that set is empty, and the proof never needs a value at `s = 0`.

## Code to add

Put this in `ShenWork/PDE/P3MoserEnergyContinuity.lean`, after the existing definitions

```lean
intervalDomainPowerEnergyDerivIntegral
IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability
```

If the weighted residual is already defined locally, omit the duplicate `def` below.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import Mathlib.Tactic

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- PDE-shaped initial-window residual for the weighted time-term appearing in
the interval-domain Lp chain rule.

This is one step closer to the PDE than
`IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability`: it asks for
integrability of the already-existing weighted time-term profile. -/
def IntervalDomainLpWeightedTimeTermInitialWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s =>
          q * intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm q u s))
        volume 0 b

/-- Pointwise identity between the explicit power-energy derivative integral and
the weighted time-term, under positivity of the time slice.

The positivity hypothesis is necessary for the absolute-value and real-power
rewrites inside `intervalDomainPowerTimeTerm_eq_scaled_weighted`. -/
theorem intervalDomainPowerEnergyDerivIntegral_eq_scaled_weighted_of_pos
    (q s : ℝ) (u : ℝ → intervalDomain.Point → ℝ)
    (hpos : ∀ x : intervalDomain.Point, 0 < u s x) :
    intervalDomainPowerEnergyDerivIntegral q u s =
      q * intervalDomain.integral
        (intervalDomainLpEnergyWeightedTimeTerm q u s) := by
  calc
    intervalDomainPowerEnergyDerivIntegral q u s
        = ∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u s y := by
            rfl
    _ = intervalDomain.integral
          (fun x => q * (u s x) ^ (q - 1) * intervalDomain.timeDeriv u s x) :=
            intervalDomainPowerDeriv_integral_eq_timeTerm q u s
    _ = q * intervalDomain.integral
          (intervalDomainLpEnergyWeightedTimeTerm q u s) :=
            intervalDomainPowerTimeTerm_eq_scaled_weighted q s u hpos

/-- No-sorry bridge from weighted-time-term initial-window integrability to the
explicit power-derivative-integral initial-window residual, assuming positivity
of `u` at every positive time.

The congruence is on `uIoc 0 b`; after rewriting by `Set.uIoc_of_le hb.1`, every
relevant `s` satisfies `0 < s`, so the supplied positivity hypothesis applies.
This is robust when `b = 0`, since `Ioc 0 0` is empty. -/
theorem intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial_of_pos
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hpos : ∀ s, 0 < s → ∀ x : intervalDomain.Point, 0 < u s x)
    (hwt : IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0) :
    IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0 := by
  intro q hq b hb
  have hwtInt :
      IntervalIntegrable
        (fun s =>
          q * intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm q u s))
        volume 0 b :=
    hwt q hq b hb
  refine IntervalIntegrable.congr ?_ hwtInt
  intro s hs
  rw [Set.uIoc_of_le hb.1] at hs
  exact intervalDomainPowerEnergyDerivIntegral_eq_scaled_weighted_of_pos
    q s u (hpos s hs.1)

/-- Global classical solutions supply the positivity needed by the pure bridge:
for each positive time `s`, run the classical solution API on horizon `s + 1`. -/
theorem intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hwt : IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0) :
    IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0 := by
  refine
    intervalDomain_powerDerivIntegralInitialWindowIntegrability_of_weightedTimeTerm_initial_of_pos
      (T := T) (p0 := p0) (u := u) ?_ hwt
  intro s hs x
  have hTpos : 0 < s + 1 := by linarith
  have hsol : IsPaper2ClassicalSolution intervalDomain params (s + 1) u v :=
    hglobal.classical hTpos
  exact hsol.u_pos' (x := x) hs (by linarith)

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

## Notes on imports/namespaces

The important extra open is:

```lean
open ShenWork.Paper2.IntervalDomainEnergyStep
```

because the definition

```lean
intervalDomainLpEnergyWeightedTimeTerm
```

lives in `ShenWork.Paper2.IntervalDomainEnergyStep`, while the identities

```lean
intervalDomainPowerDeriv_integral_eq_timeTerm
intervalDomainPowerTimeTerm_eq_scaled_weighted
```

are exported in the `ShenWork.Paper2` namespace by `IntervalDomainLpTimeLeibniz.lean`.

## If the local file already defines the weighted residual

Use only the three theorem declarations.  The bridge theorem names can also be shortened locally, but I recommend keeping both:

```lean
..._of_pos
...
```

because the first is reusable without a `params`/`v`/global-classical dependency, while the second is the interval-domain PDE wrapper used downstream.

## Why positivity is unavoidable

The weighted term is

```lean
|u t x| ^ (q - 2) * u t x * intervalDomain.timeDeriv u t x
```

whereas the power-derivative integral uses

```lean
q * (u t x) ^ (q - 1) * intervalDomain.timeDeriv u t x
```

The equality between them uses `abs_of_pos` and the real-power law

```lean
(u t x) ^ (q - 2) * u t x = (u t x) ^ (q - 1)
```

which is exactly why `intervalDomainPowerTimeTerm_eq_scaled_weighted` requires
`∀ x, 0 < u t x`.  Without positivity, the proposed theorem from `hwt` alone is not well-typed/provable from the current identity; global classical supplies the missing positivity for all `s > 0`.
