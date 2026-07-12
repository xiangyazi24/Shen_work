# Task: Wire endpoint-zero continuity into the assembly chain

## Context

Codex task 2 proved `intervalDomainPowerEnergyContinuousWithinAt_zero_withInitialSlice_of_initialTrace`
in `ShenWork/PDE/P3MoserEnergyContinuity.lean`. This gives `ContinuousWithinAt` at t=0 for a
specific exponent `p0` with hypothesis `1 ≤ p0`.

The assembly chain needs `IntervalDomainInitialPowerEnergyContinuityAtZero` (defined at
`P3MoserEnergyContinuity.lean:140`), which universally quantifies over all `p ≥ p0`.

For GLOBAL classical solutions, `IntervalDomainPowerEnergyEndpointContinuity` (with BOTH
`atZero` and `atRight`) can be produced via `intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical`
(P3MoserEnergyContinuity.lean:2283) from `atZero` + `IsPaper2GlobalClassicalSolution`.

## Goal

Add to `ShenWork/PDE/P3MoserEnergyContinuity.lean` (at the end, before the final `end`):

### Theorem 1: Package as IntervalDomainInitialPowerEnergyContinuityAtZero

```lean
theorem intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_classical_withInitialSlice
    {p : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hp0 : 1 ≤ p0) :
    IntervalDomainInitialPowerEnergyContinuityAtZero
      (intervalDomainWithInitialSlice u₀ u) T p0
```

The proof: `IntervalDomainInitialPowerEnergyContinuityAtZero` is `∀ p, p0 ≤ p → ContinuousWithinAt...`.
Apply `intervalDomainPowerEnergyContinuousWithinAt_zero_withInitialSlice_of_initialTrace` with `p`
instead of `p0`, using `le_trans hp0 hp` to get `1 ≤ p`.

IMPORTANT: First read the EXACT definition of `IntervalDomainInitialPowerEnergyContinuityAtZero`
at P3MoserEnergyContinuity.lean:140. Make sure the types match exactly.

### Theorem 2: Full endpoint continuity for global solutions + re-anchored trajectory

```lean
theorem intervalDomain_powerEnergyEndpointContinuity_withInitialSlice_of_global_classical
    {p : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hp0 : 1 ≤ p0) :
    IntervalDomainPowerEnergyEndpointContinuity
      (intervalDomainWithInitialSlice u₀ u) T p0
```

The proof: use Theorem 1 for `atZero`, then use
`intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical`
(or its logic) for `atRight`.

For `atRight`: since we have a global classical solution, `T` is an interior point of `(0, T+1)`.
Classical regularity gives energy continuity on open intervals. So `ContinuousWithinAt` at `T`
from the left holds.

IMPORTANT: Check if `intervalDomainWithInitialSlice u₀ u` preserves enough regularity for
the global classical solution arguments. The `intervalDomainWithInitialSlice` only modifies
`u` at `t = 0`, so for `t > 0` it's identical to `u`. The `atRight` argument only uses
`t > 0` behavior, so it should go through.

If the re-anchored trajectory causes issues with the global solution arguments, provide a
version with explicit `u 0 = u₀` hypothesis instead.

## What to read FIRST

1. `P3MoserEnergyContinuity.lean:140` — `IntervalDomainInitialPowerEnergyContinuityAtZero` definition
2. `P3MoserEnergyContinuity.lean:122` — `IntervalDomainPowerEnergyEndpointContinuity` definition  
3. `P3MoserEnergyContinuity.lean:181` — `intervalDomainWithInitialSlice` definition
4. `P3MoserEnergyContinuity.lean:2283` — `intervalDomain_powerEnergyEndpointContinuity_of_atZero_and_global_classical`
5. The existing `intervalDomainPowerEnergyContinuousWithinAt_zero_withInitialSlice_of_initialTrace`
6. `IsPaper2GlobalClassicalSolution` definition (grep for it)

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserEnergyContinuity.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- Add code at the END of the file, before the final `end` statements
- If the WithInitialSlice version is too hard, deliver a version with `hzeroSlice : u 0 = u₀` instead
- Deliver what compiles + precise stall report if stuck
- Work only in /Users/huangx/repos/Shen_work/
