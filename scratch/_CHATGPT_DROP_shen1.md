# Q2880 (shen1) — PDE-term initial-window integrability frontier

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

## Executive answer

The current repo APIs do **not** appear to prove the full initial-window residual

```lean
IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0
```

from `IsPaper2GlobalClassicalSolution`, `InitialTrace`, or endpoint energy continuity alone.

What exists now is strong but pointwise-in-time:

```lean
intervalDomainLift_lp_diffusion_intervalIntegrable_of_regularity
intervalDomainLift_lp_chemotaxis_intervalIntegrable_of_regularity
intervalDomainLift_lp_logistic_intervalIntegrable_of_regularity
```

These show spatial interval integrability for each fixed positive time `s`.  They do **not** imply time integrability of the scalar profiles on `0..b = Ioc 0 b`.

The compiled PDE-integral identity

```lean
intervalDomain_lp_energy_hPDEIntegral_of_regularity
```

is also pointwise in time.  It is excellent for congruence once scalar time integrability is known, but it does not itself prove any time integrability near `0`.

So the honest split is:

1. **Positive-start / strict windows** are reducible to continuity of the three scalar PDE profiles on compact time windows.  This can be packaged no-sorry by `ContinuousOn.intervalIntegrable`.
2. **Initial windows starting at `0`** remain a real residual.  Neither `InitialTrace` nor endpoint power-energy continuity controls the time singularity of diffusion/chemotaxis/logistic scalar profiles.
3. The thinnest residual for the current Moser route is still the existing component initial-window integrability residual.  A useful auxiliary positive-start package can be added so future closed-window variants split exactly into “initial edge + positive-start interior.”

## No-sorry code: positive-start/strict-window split

Put this in `ShenWork/PDE/P3MoserEnergyContinuity.lean` after the existing definition

```lean
IntervalDomainLpPDETermInitialWindowIntegrability
```

If imports/namespaces are already present in the file, only add the declarations.

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

/-- Positive-left-start time integrability of the three scalar PDE terms in the
Lp weighted time identity.

This is the part one expects to get from classical regularity/continuity on
compact strict time slabs.  It intentionally does not include windows whose left
endpoint is `0`. -/
def IntervalDomainLpPDETermPositiveStartWindowIntegrability
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ a b, 0 < a → a ≤ b → b ≤ T →
      IntervalIntegrable
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        volume a b ∧
      IntervalIntegrable
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        volume a b ∧
      IntervalIntegrable
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        volume a b

/-- Continuity package for the three scalar PDE term profiles on positive-start
closed time windows.

This is the natural continuity residual/proposition from which the positive-start
integrability package follows by `ContinuousOn.intervalIntegrable`.  Existing
spatial integrability lemmas do not by themselves supply this continuity. -/
def IntervalDomainLpPDETermPositiveStartWindowContinuity
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ a b, 0 < a → a ≤ b → b ≤ T →
      ContinuousOn
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        (Set.Icc a b) ∧
      ContinuousOn
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        (Set.Icc a b) ∧
      ContinuousOn
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        (Set.Icc a b)

/-- No-sorry conversion from positive-start continuity of the three scalar PDE
profiles to positive-start interval integrability.

This is the reusable strict-window producer skeleton.  The real analytic work,
if desired later, is to prove `IntervalDomainLpPDETermPositiveStartWindowContinuity`
from joint time-space regularity of the three integrands. -/
theorem intervalDomain_lpPDETermPositiveStartWindowIntegrability_of_continuity
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hcont : IntervalDomainLpPDETermPositiveStartWindowContinuity params u v T p0) :
    IntervalDomainLpPDETermPositiveStartWindowIntegrability params u v T p0 := by
  intro q hq a b ha hab hbT
  rcases hcont q hq a b ha hab hbT with ⟨hD, hC, hL⟩
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  · apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]

/-- Full closed-window integrability package for the three scalar PDE terms.

This is not required by the current initial-window residual, but it is useful as
the exact analogue of the earlier derivative-integrability split. -/
def IntervalDomainLpPDETermClosedWindowIntegrability
    (params : CM2Params) (u v : ℝ → intervalDomain.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ q, p0 ≤ q →
    ∀ t1 ∈ Set.Icc (0 : ℝ) T, ∀ t2 ∈ Set.Icc t1 T,
      IntervalIntegrable
        (fun s => q * intervalDomainLpDiffusionIntegral q u s)
        volume t1 t2 ∧
      IntervalIntegrable
        (fun s =>
          q * (params.χ₀ *
            intervalDomainLpChemotaxisIntegral params q u v s))
        volume t1 t2 ∧
      IntervalIntegrable
        (fun s => q * intervalDomainLpLogisticIntegral params q u s)
        volume t1 t2

/-- Pure split: initial-edge integrability plus positive-left-start integrability
imply integrability on every closed time window inside `[0,T]`.

For windows starting at `0`, use the existing initial-window residual.  For all
other windows, use positive-start integrability. -/
theorem intervalDomain_lpPDETermClosedWindowIntegrability_of_initial_and_positiveStart
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hinit : IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0)
    (hpos : IntervalDomainLpPDETermPositiveStartWindowIntegrability params u v T p0) :
    IntervalDomainLpPDETermClosedWindowIntegrability params u v T p0 := by
  intro q hq t1 ht1 t2 ht2
  by_cases ht10 : t1 = 0
  · subst t1
    exact hinit q hq t2 ht2
  · have ht1_pos : 0 < t1 :=
      lt_of_le_of_ne ht1.1 (fun h : (0 : ℝ) = t1 => ht10 h.symm)
    exact hpos q hq t1 t2 ht1_pos ht2.1 ht2.2

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

## What can be proved from current APIs?

### 1. Strict/positive-start windows

A no-sorry theorem from **continuity** to time integrability is straightforward and is given above.  However, I do not see an already-named repo theorem proving

```lean
ContinuousOn (fun s => q * intervalDomainLpDiffusionIntegral q u s) (Icc a b)
ContinuousOn (fun s => q * (params.χ₀ * intervalDomainLpChemotaxisIntegral ... s)) (Icc a b)
ContinuousOn (fun s => q * intervalDomainLpLogisticIntegral ... s) (Icc a b)
```

from `IsPaper2GlobalClassicalSolution` or `IsPaper2ClassicalSolution`.

The existing lemmas with names

```lean
intervalDomainLift_lp_diffusion_intervalIntegrable_of_regularity
intervalDomainLift_lp_chemotaxis_intervalIntegrable_of_regularity
intervalDomainLift_lp_logistic_intervalIntegrable_of_regularity
```

are spatial integrability lemmas at a fixed positive time.  They are exactly what the pointwise PDE-integral identity uses, but they do not provide time continuity or time integrability of the resulting scalar integrals.

A future no-sorry producer for `IntervalDomainLpPDETermPositiveStartWindowContinuity` would need a parametric-integral continuity proof for each of the three integrands.  That is plausible on strict compact slabs, but it requires joint time-space continuity/boundedness of the lifted diffusion, chemotaxis, and logistic integrands.  The currently exposed named lemmas do not package that as a scalar-profile continuity theorem.

### 2. Closed initial-window integrability

This does **not** follow from the current APIs.

`InitialTrace` proves value convergence of `u(t)` to `u₀` in a sup-norm sense.  Endpoint power-energy continuity proves continuity of

```lean
s ↦ ∫ u(s)^q
```

at `0`.  Neither statement controls the time singularity of

```lean
s ↦ intervalDomainLpDiffusionIntegral q u s
s ↦ intervalDomainLpChemotaxisIntegral params q u v s
s ↦ intervalDomainLpLogisticIntegral params q u s
```

on `Ioc 0 b`.  Pointwise-in-time classical regularity also cannot be integrated in time without a uniform-in-time or integrable-in-time bound.

### 3. Thinnest honest residual

For the current WindowFTC route, the thinnest honest residual remains:

```lean
IntervalDomainLpPDETermInitialWindowIntegrability params u v T p0
```

If you want a more modular future API, use the split above:

* `IntervalDomainLpPDETermPositiveStartWindowContinuity` or `...PositiveStartWindowIntegrability` for strict/positive-left-start windows;
* `IntervalDomainLpPDETermInitialWindowIntegrability` for the initial edge.

Only the initial edge is genuinely hard for the current Moser WindowFTC route.
