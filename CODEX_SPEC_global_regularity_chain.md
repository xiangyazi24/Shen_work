# Task: Chain global solution regularity into the assembly

## Context

We now have all the pieces for the GLOBAL classical solution case to produce
`IntervalDomainIntegratedMoserClassicalRegularityData` — we just need to wire
them together.

The pieces:
1. `intervalDomain_powerEnergyEndpointContinuity_withInitialSlice_of_global_classical`
   (P3MoserEnergyContinuity.lean:2482) — produces `IntervalDomainPowerEnergyEndpointContinuity`
   for re-anchored trajectory from global classical + trace + datum
2. `intervalDomain_classicalRegularityData_of_global_atZero_gradientContinuous`
   (P3MoserGradientIntegrability.lean:170) — produces `IntervalDomainIntegratedMoserClassicalRegularityData`
   from global classical + atZero + gradient continuity

The chain for global solutions:
- `IsPaper2GlobalClassicalSolution` + `InitialTrace` + `PaperPositiveInitialDatum`
  → `IntervalDomainPowerEnergyEndpointContinuity` (piece 1)
  → needs gradient continuity (irreducible)
  → `IntervalDomainIntegratedMoserClassicalRegularityData` (piece 2)

## Goal

Create `ShenWork/Paper3/IntervalDomainGlobalChain.lean` that provides:

### Theorem: Full classicalRegularity for global solutions (modulo gradient continuity)

```lean
theorem intervalDomain_classicalRegularityData_global_withInitialSlice
    {p : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hp0 : 1 ≤ p0)
    (hgrad : ∀ q, p0 ≤ q →
        ContinuousOn (intervalDomainMoserGradientEnergy
          (intervalDomainWithInitialSlice u₀ u) q) (Set.Icc 0 T)) :
    IntervalDomainIntegratedMoserClassicalRegularityData
      (intervalDomainWithInitialSlice u₀ u) T p0
```

The proof chains pieces 1 and 2 (or their underlying logic). 

### Theorem: Full assembly input package for global solutions

Wire the classicalRegularity into the assembly. Given:
- `IsPaper2GlobalClassicalSolution`
- `InitialTrace`, `PaperPositiveInitialDatum`
- `boundednessHyp` (parameter)
- `closedEnergyTrace` (carried)
- `integratedMoserDissipation` (carried)
- `relativeMassGradient` (carried)  
- `quantitativeEndpoint` (carried)
- gradient continuity (carried, irreducible)

Produce: `IntervalDomainMassLpSmoothingRouteResiduals` (the final route residuals).

This means calling:
1. `IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals.to_integratedStepResiduals`
   with `classicalRegularity` filled by the theorem above
2. Then `.to_routeResiduals`

Read `IntervalDomainIntegratedMoserAssembly.lean` to see the exact signatures.

## What to read FIRST

1. `ShenWork/Paper3/IntervalDomainIntegratedMoserAssembly.lean` — the assembly structure
2. `ShenWork/PDE/P3MoserEnergyContinuity.lean` lines 2460-2510 — endpoint wiring
3. `ShenWork/PDE/P3MoserGradientIntegrability.lean` lines 170-185 — gradient→regularity
4. `ShenWork/PDE/P3MoserRegularityProducer.lean` — find `IntervalDomainIntegratedMoserClassicalRegularityData`
5. Grep for `intervalDomainMoserGradientEnergy`, `IntervalDomainMoserGradientStrictWindowContinuity`
6. Grep for `IntervalDomainMassLpSmoothingRouteResiduals`

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/Paper3/IntervalDomainGlobalChain.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- Work only in /Users/huangx/repos/Shen_work/
- The `hgrad` (gradient continuity) must remain as a HYPOTHESIS — it is irreducible
- All other PDE frontiers (`closedEnergyTrace`, `integratedMoserDissipation`, etc.) remain as hypotheses
