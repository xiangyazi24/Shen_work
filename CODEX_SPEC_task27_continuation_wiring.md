# Task 27: Wire T25 continuation framework into the global assembly

## Goal

Create `ShenWork/PDE/P3MoserContinuationWiring.lean` that replaces the circular
`hBoundedBefore` hypothesis in the global assembly with T25's non-circular
continuation framework.

## Background

The current global wiring (`P3MoserAssemblyGlobalWiring.lean`) carries `hBoundedBefore`
as a hypothesis — this is circular because the assembly is supposed to PRODUCE
bounded-before, not RECEIVE it.

T25 (`P3MoserFirstCrossingContinuation.lean`) breaks this circularity by defining
4 residual predicates (A-D) and proving `boundedBefore_of_classical_and_assembly`
which produces `IsPaper2BoundedBefore` from these residuals.

## What to produce

A theorem that supplies `hBoundedBefore` to the assembly filler by using T25's
continuation theorem. The new theorem should carry T25's 4 residuals as hypotheses
instead of the circular `hBoundedBefore`.

Concretely, produce:

```lean
theorem intervalDomain_integratedDropResiduals_via_continuation
    {p : CM2Params}
    (hbdns : IntervalDomainBoundednessHyp p)
    (hClosedTrace : ...)  -- same as assembly filler
    (hFTC : ...)  -- same as assembly filler
    (hGap : ...)  -- same as assembly filler, or from T26
    (hDyadicEndpoint : ...)  -- same as assembly filler
    -- NEW: T25's residuals instead of circular hBoundedBefore
    (hShort : ShortTimeBoundedBeforeResidual intervalDomain p)
    (hAssembly : SubintervalAssemblyResidual intervalDomain p)
    (hExtend : ExtensionByContinuityResidual intervalDomain p)
    (hClosure : FirstCrossingSupremumClosureResidual intervalDomain p) :
    IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p
```

The proof should:
1. Use T25's `boundedBefore_of_classical_and_assembly` to produce `IsPaper2BoundedBefore`
   from the 4 residuals
2. Feed the produced `IsPaper2BoundedBefore` into the assembly filler
3. The result is non-circular because the residuals DON'T use `IsPaper2BoundedBefore`
   as input

## Files to read first

1. `ShenWork/PDE/P3MoserFirstCrossingContinuation.lean` — T25's full file
2. `ShenWork/PDE/P3MoserAssemblyFiller.lean` — assembly filler (consumer)
3. `ShenWork/PDE/P3MoserAssemblyGlobalWiring.lean` — current global wiring

## Key type connections

The assembly filler's `hBoundedBefore` slot wants:
```
∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
      IsPaper2BoundedBefore intervalDomain T u
```

T25's main theorem produces:
```
IsPaper2BoundedBefore D T u
```
from `ShortTimeBoundedBeforeResidual D p`, `SubintervalAssemblyResidual D p`,
`ExtensionByContinuityResidual D p`, `FirstCrossingSupremumClosureResidual D p`,
and `IsPaper2ClassicalSolution D p T u v`.

So the bounded-before producer is:
```
fun hsol hcross hboot =>
  boundedBefore_of_classical_and_assembly hShort hAssembly hExtend hClosure hsol
```

Note: the `hcross` and `hboot` arguments are unused by the continuation theorem,
which only needs the classical solution. This is correct — the continuation breaks
the circularity by NOT requiring the bootstrap machinery to produce bounded-before.

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserContinuationWiring.lean
```
