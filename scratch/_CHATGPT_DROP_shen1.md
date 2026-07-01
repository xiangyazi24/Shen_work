# Q2888 (shen1) — audit of combined initial-window integrability

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target file: `ShenWork/PDE/P3MoserEnergyContinuity.lean`  
Source edit requested: none; answer file only.

## Verdict

`IntervalDomainLpPDECombinedInitialWindowIntegrability` is **not already provable** from the currently visible global-classical + initial-trace + endpoint-energy-continuity APIs.

The new combined residual is nevertheless an honest and useful thinning of the old initial-edge requirement: it asks only for near-zero time integrability of the **single scalar PDE combination** that is equal, at positive times, to the weighted Lp time term. It avoids the false stronger demand that the diffusion, chemotaxis, and logistic scalar profiles be separately time-integrable at `0`.

The missing point is exactly the endpoint one: current APIs give strict-positive-time regularity and identities on every `[a,b] ⊆ (0,T)`, and endpoint continuity of the energy value at `0`; they do **not** give integrability of the derivative / weighted time profile on `0..b`.

## What current APIs give

The visible/current route has these ingredients.

1. `IsPaper2GlobalClassicalSolution.classical` gives a classical solution on every finite positive horizon, hence strict-positive-time regularity/positivity. It does not give a classical statement at `t = 0`.

2. `intervalDomainPowerEnergy_hasDerivAt` / `intervalDomain_lp_timeLeibniz` give the Lp-energy derivative identity only for `0 < t < T`.

3. `intervalDomain_lp_energy_hPDEIntegral_of_regularity` gives, again only for `0 < t < T`,

```lean
intervalDomain.integral (intervalDomainLpEnergyWeightedTimeTerm pExp u t) =
  intervalDomainLpDiffusionIntegral pExp u t -
    params.χ₀ * intervalDomainLpChemotaxisIntegral params pExp u v t +
    intervalDomainLpLogisticIntegral params pExp u t
```

4. The endpoint package in `P3MoserEnergyContinuity.lean` is value continuity of

```lean
fun t => intervalDomain.integral (fun x => (u t x) ^ p)
```

at `0` and `T`. This is not a time-integrability statement for the derivative/PDE scalar profile.

Therefore current APIs prove positive-start window integrability, schematically:

```lean
∀ q, p0 ≤ q → ∀ a b, 0 < a → a ≤ b → b < T →
  IntervalIntegrable
    (fun s =>
      q * intervalDomainLpDiffusionIntegral q u s -
        q * (params.χ₀ *
          intervalDomainLpChemotaxisIntegral params q u v s) +
        q * intervalDomainLpLogisticIntegral params q u s)
    volume a b
```

They do **not** prove the initial-window version:

```lean
IntervalIntegrable ... volume 0 b
```

for arbitrary `b ∈ Set.Icc 0 T`.

This distinction matters because, for `0 ≤ b`, `IntervalIntegrable f volume 0 b` is an integrability assertion on the near-zero interval `Ioc 0 b`, not a statement about the value of `f 0`. Changing or defining the endpoint value at `0` is irrelevant; controlling possible blow-up as `s ↓ 0` is the missing analytic estimate.

## Why initial trace / endpoint energy continuity are insufficient

`InitialTrace` controls only convergence of `u t` to the initial datum in a sup-norm sense for `t > 0` small. The endpoint power-energy continuity residual controls only

```lean
ContinuousWithinAt
  (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
  (Set.Icc 0 T) 0
```

Neither statement implies any of the following:

```lean
IntervalIntegrable
  (fun s => deriv (fun τ => intervalDomainPowerEnergy q u τ) s)
  volume 0 b
```

or

```lean
IntervalIntegrable
  (fun s => q * intervalDomain.integral
    (intervalDomainLpEnergyWeightedTimeTerm q u s))
  volume 0 b
```

or the combined PDE scalar integrability itself.

The strict-positive-time identity

```lean
weighted time term = PDE combined scalar
```

also does not create integrability near `0`; it only lets you transfer integrability once one side has already been proved on `0..b`.

## Thinnest honest residual/API

There are two honest ways to proceed, depending on what you want the upstream PDE producer to own.

### Option A: keep your new combined residual as the direct initial-edge residual

This is the thinnest direct residual for the current bridge:

```lean
def IntervalDomainLpPDECombinedInitialWindowIntegrability
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s =>
          q * intervalDomainLpDiffusionIntegral q u s -
            q * (params.χ₀ *
              intervalDomainLpChemotaxisIntegral params q u v s) +
            q * intervalDomainLpLogisticIntegral params q u s)
        volume 0 b
```

This is honest because it asks exactly for the scalar near-zero time integrability needed to identify the derivative integrand on initial windows. It is not derivable from the current value-continuity APIs.

### Option B: use weighted-time-term initial integrability as the upstream residual

Mathematically, this is slightly cleaner because it names the object that is directly the Lp-energy derivative at positive times:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Initial-window time integrability of the weighted Lp time term.
If this name already exists in the local file, reuse the existing definition. -/
def IntervalDomainLpWeightedTimeTermInitialWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s =>
          q * intervalDomain.integral
            (intervalDomainLpEnergyWeightedTimeTerm q u s))
        volume 0 b

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

Then add the bridge from weighted initial integrability to your combined residual:

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Positive-time weighted-term/PDE-combined equality, global-horizon form.
This should be proved by choosing the horizon `t + 1`, applying the existing
finite-horizon PDE integral identity, and normalizing the scalar algebra. -/
theorem intervalDomain_weightedTimeTerm_eq_pdeCombined_scaled_of_global_pos
    {params : CM2Params} {q t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ht0 : 0 < t) :
    q * intervalDomain.integral
        (intervalDomainLpEnergyWeightedTimeTerm q u t) =
      q * intervalDomainLpDiffusionIntegral q u t -
        q * (params.χ₀ *
          intervalDomainLpChemotaxisIntegral params q u v t) +
        q * intervalDomainLpLogisticIntegral params q u t

/-- Weighted initial-window integrability produces the combined PDE initial-window
integrability. This uses only positive-time equality on `Ioc 0 b`; it does not
need or assert any endpoint PDE identity at `s = 0`. -/
theorem intervalDomain_lpPDECombinedInitialWindowIntegrability_of_weightedTimeTerm_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hweighted :
      IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

Proof route for the second theorem:

```lean
intro q hq b hb
have hW := hweighted q hq b hb
-- Convert by congruence on the interval domain of `0..b`.
-- Since `hb.1 : 0 ≤ b`, points of the interval-integrability domain are in
-- `Ioc 0 b`, hence have `0 < s`; the endpoint `s = 0` is irrelevant.
refine hW.congr ?_
intro s hs
rw [Set.uIoc_of_le hb.1] at hs
have hs0 : 0 < s := hs.1
exact intervalDomain_weightedTimeTerm_eq_pdeCombined_scaled_of_global_pos
  (q := q) (t := s) hglobal hs0
```

Depending on the exact local orientation of `IntervalIntegrable.congr`, the last two lines may need `.symm`; the mathematical proof is a pure a.e./Ioc congruence.

## Power-energy derivative/FTC version

If the intended producer is an absolute-continuity / FTC theorem for the Lp power energy, add the residual at that level instead. This is stronger than mere combined integrability, but it is the mathematically canonical object for the final `IntegratedMoserEnergyWindowFTC`.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Initial-window derivative integrability for the power-energy profile.
This is the minimal integrability half of an initial-window AC/FTC input. -/
def IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ b ∈ Set.Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun s => deriv (fun τ => intervalDomainPowerEnergy q u τ) s)
        volume 0 b

/-- Full initial-window FTC/absolute-continuity input for the power-energy profile.
Use this if the upstream PDE theorem can produce FTC directly rather than only
local integrability of the derivative. -/
structure IntervalDomainPowerEnergyInitialWindowFTC
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  deriv_intervalIntegrable :
    IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0
  initial_window_ftc :
    ∀ q, p0 ≤ q →
      ∀ b ∈ Set.Icc (0 : ℝ) T,
        (∫ s in (0 : ℝ)..b,
          deriv (fun τ => intervalDomainPowerEnergy q u τ) s) =
          intervalDomainPowerEnergy q u b -
            intervalDomainPowerEnergy q u 0

/-- Positive-time derivative/PDE-combined identity, global-horizon form. -/
theorem intervalDomain_powerEnergy_deriv_eq_pdeCombined_of_global_pos
    {params : CM2Params} {q t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (ht0 : 0 < t) :
    deriv (fun τ => intervalDomainPowerEnergy q u τ) t =
      q * intervalDomainLpDiffusionIntegral q u t -
        q * (params.χ₀ *
          intervalDomainLpChemotaxisIntegral params q u v t) +
        q * intervalDomainLpLogisticIntegral params q u t

/-- Derivative initial-window integrability produces combined PDE initial-window
integrability, by positive-time derivative/PDE equality on `Ioc 0 b`. -/
theorem intervalDomain_lpPDECombinedInitialWindowIntegrability_of_powerEnergyDeriv_initial
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hderiv :
      IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0

/-- Full AC/FTC input also produces the combined initial-window integrability,
using only its derivative-integrability field. -/
theorem intervalDomain_lpPDECombinedInitialWindowIntegrability_of_powerEnergyInitialWindowFTC
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hftc : IntervalDomainPowerEnergyInitialWindowFTC u T p0) :
    IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

Proof route for `intervalDomain_powerEnergy_deriv_eq_pdeCombined_of_global_pos`:

1. Set the finite horizon to `t + 1`.
2. Use `hglobal.classical (by linarith : 0 < t + 1)`.
3. Apply `intervalDomainPowerEnergy_hasDerivAt` at `t` and rewrite `deriv` using `HasDerivAt.deriv`.
4. Use `intervalDomainPowerDeriv_integral_eq_timeTerm` and `intervalDomainPowerTimeTerm_eq_scaled_weighted` to identify the derivative with the scaled weighted time term.
5. Use `intervalDomain_lp_energy_hPDEIntegral_of_regularity` to rewrite the weighted time term as the PDE combined scalar.
6. Finish with `ring_nf` / `ring` for

```lean
q * (D - χC + L) = q * D - q * (χC) + q * L
```

Proof route for `intervalDomain_lpPDECombinedInitialWindowIntegrability_of_powerEnergyDeriv_initial`:

```lean
intro q hq b hb
have hD := hderiv q hq b hb
refine hD.congr ?_
intro s hs
rw [Set.uIoc_of_le hb.1] at hs
have hs0 : 0 < s := hs.1
exact intervalDomain_powerEnergy_deriv_eq_pdeCombined_of_global_pos
  (q := q) (t := s) hglobal hs0
```

Again, depending on the local `congr` orientation, use `.symm`.

## Recommended next step

Do **not** try to prove `IntervalDomainLpPDECombinedInitialWindowIntegrability` from `InitialTrace` or endpoint power-energy continuity alone.

The next honest theorem should be one of these:

1. **If keeping the current combined residual:** keep `IntervalDomainLpPDECombinedInitialWindowIntegrability` as an explicit assumption to `intervalDomain_integratedMoserEnergyWindowFTC_of_global_atZero_pdeCombined`; this is already the thinnest direct initial-edge assumption.

2. **If reducing it one layer upstream:** prove

```lean
IntervalDomainLpWeightedTimeTermInitialWindowIntegrability u T p0
```

or

```lean
IntervalDomainPowerEnergyDerivIntegralInitialWindowIntegrability u T p0
```

from a genuine near-zero PDE estimate, and then add the congruence bridge above.

3. **If the producer can prove absolute continuity:** add `IntervalDomainPowerEnergyInitialWindowFTC` and use it to produce `IntegratedMoserEnergyWindowFTC` directly. This is stronger but mathematically cleaner than manufacturing FTC from continuity.

The key rule is: the initial edge must be discharged by a real near-zero integrability/absolute-continuity theorem, not by endpoint continuity and not by pointwise strict-positive-time equality alone.
