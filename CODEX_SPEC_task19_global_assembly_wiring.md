# CODEX_SPEC Task 19: Wire assembly filler into the global chain

## Goal

Write `ShenWork/PDE/P3MoserAssemblyGlobalWiring.lean` — a theorem that
uses the assembly filler (`intervalDomain_integratedDropResiduals_of_classical`
in `P3MoserAssemblyFiller.lean`) to produce the route residuals package, with
`hClassicalRegularity` discharged by the global chain's
`IntervalDomainGlobalClassicalRegularityInputs`.

## Context

The global chain (`Paper3/IntervalDomainGlobalChain.lean`) produces
`IntervalDomainMassLpSmoothingRouteResiduals p` but carries 5 hypotheses:
`closedEnergyTrace`, `integratedMoserDissipation`, `relativeMassGradient`,
`quantitativeEndpoint`, and `hinputs`.

The assembly filler (`P3MoserAssemblyFiller.lean`) decomposes
`integratedMoserDissipation` and `relativeMassGradient` into smaller pieces:
`hFTC`, `hClassicalRegularity`, `hBoundedBefore`, `hGap`.

`hClassicalRegularity` is ALREADY discharged by `hinputs` via
`intervalDomain_classicalRegularitySupplier_global_withInitialSlice`
(IntervalDomainGlobalChain.lean:81-96).

## What to write

A theorem that:
1. Takes `hinputs : IntervalDomainGlobalClassicalRegularityInputs p`
2. Takes `hbdns : IntervalDomainBoundednessHyp p`
3. Takes `ha : 0 < p.a` and `hχ0 : 0 < p.χ₀`
4. Takes the remaining CARRIED hypotheses: hClosedTrace, hFTC, hBoundedBefore,
   hGap, hDyadicEndpoint (same types as in assembly filler)
5. Produces `IntervalDomainMassLpSmoothingRouteResiduals p`

The proof:
- Call `intervalDomain_integratedDropResiduals_of_classical` (assembly filler)
  with hbdns, hClosedTrace, hFTC,
  `(intervalDomain_classicalRegularitySupplier_global_withInitialSlice hinputs)`,
  hBoundedBefore, hGap, hDyadicEndpoint
  → gives `IntegratedDropResiduals`
- Call `.to_routeResiduals` with the regularity supplier from hinputs,
  ha, hχ0 → gives `RouteResiduals`

## Files to read first

1. `ShenWork/PDE/P3MoserAssemblyFiller.lean` — the assembly filler theorem
   (lines 34-153, note exact hypothesis types)
2. `ShenWork/Paper3/IntervalDomainGlobalChain.lean` — the global chain
   (lines 1-172, note `IntervalDomainGlobalClassicalRegularityInputs` at 62,
    `intervalDomain_classicalRegularitySupplier_global_withInitialSlice` at 81,
    and `to_routeResiduals` usage at 161)
3. `ShenWork/Paper3/IntervalDomainIntegratedMoserAssembly.lean` — find the
   `to_routeResiduals` method signature (grep for it)

## Imports

```lean
import ShenWork.PDE.P3MoserAssemblyFiller
import ShenWork.Paper3.IntervalDomainGlobalChain
```

## Rules

- 0 sorry, 0 custom axiom, 0 native_decide
- Write ONLY `ShenWork/PDE/P3MoserAssemblyGlobalWiring.lean`
- Add `#print axioms` for the main theorem at the end
- Verify: `lake env lean ShenWork/PDE/P3MoserAssemblyGlobalWiring.lean`
- This is WIRING only — no new mathematical content, just connecting existing
  theorems. If something doesn't type-check, read the exact types carefully
  and adjust.
