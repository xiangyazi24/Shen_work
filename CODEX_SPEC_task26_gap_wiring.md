# Task 26: Wire T22 gap producer into the global assembly

## Goal

Create `ShenWork/PDE/P3MoserGapProducerWiring.lean` that provides the `hGap` hypothesis
consumed by `P3MoserAssemblyGlobalWiring.intervalDomain_massLpSmoothingRouteResiduals_global_assembly_wiring`.

The key theorem from T22 (in `P3MoserEnergyGapRefactor.lean`) is:

```
theorem lpBootstrapEnergyInequalityWithGap_of_classical_pDep
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hp0_gap : gapThresholdPDep params.χ₀ ≤ p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0) :
    LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0
```

The assembly filler's `hGap` slot wants:
```
∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T u v →
    CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
    AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
      LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0
```

## What to produce

A theorem that wraps `lpBootstrapEnergyInequalityWithGap_of_classical_pDep` to match
the assembly's expected signature. The only difference is:
- T22 needs `gapThresholdPDep params.χ₀ ≤ p0` as an extra hypothesis
- The assembly's slot doesn't have this threshold constraint

**Solution**: The wrapping theorem should carry `gapThresholdPDep params.χ₀ ≤ p0` as a
hypothesis of the outer theorem. Alternatively, if `AbstractLpBootstrapHypothesis`
already implies `p0 ≥ 4` (since the bootstrap starts from a threshold), then discharge
it from there.

The simplest approach: produce a theorem with signature exactly matching the assembly's
`hGap` slot, carrying the threshold condition as an extra parameter at the outer level:

```lean
theorem intervalDomain_gap_of_classical_pDep
    {p : CM2Params}
    (hp0_threshold : gapThresholdPDep p.χ₀ ≤ p0_start)  -- threshold for gap
    ... :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0
```

## Files to read first

1. `ShenWork/PDE/P3MoserEnergyGapRefactor.lean` — T22's output (the gap producer)
2. `ShenWork/PDE/P3MoserAssemblyFiller.lean` — the assembly filler (consumer of hGap)
3. `ShenWork/PDE/P3MoserAssemblyGlobalWiring.lean` — global wiring (where hGap is consumed)
4. `ShenWork/PDE/P3MoserIntegratedDissipationPDEv2.lean` lines 30-50 — `LpBootstrapEnergyInequalityWithGap` definition
5. `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean` lines 1-50 — `AbstractLpBootstrapHypothesis` definition

## Constraints

- NO sorry, NO axiom, NO native_decide
- All `#print axioms` must show ONLY `[propext, Classical.choice, Quot.sound]`
- File must compile: `lake env lean ShenWork/PDE/P3MoserGapProducerWiring.lean`

## Verification

```bash
lake env lean ShenWork/PDE/P3MoserGapProducerWiring.lean
```

Last lines must show `#print axioms` with only `propext, Classical.choice, Quot.sound`.
