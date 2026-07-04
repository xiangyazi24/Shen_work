# CODEX_SPEC Task 20: Produce hFTC from global classical chain

## Goal

Write `ShenWork/PDE/P3MoserFTCGlobalProducer.lean` — a theorem that produces
the assembly filler's `hFTC` hypothesis from the global chain's re-anchoring
data.

## Target type

The assembly filler's hFTC is:
```lean
∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
  IsPaper2ClassicalSolution intervalDomain p T u v →
  CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
  AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
    IntegratedMoserEnergyWindowFTC intervalDomain u T p0
```

## Producer chain

The existing code has this chain in `P3MoserEnergyContinuity.lean`:

1. `intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData`
   (line 2445): Takes global classical + `IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData`
   → produces `IntegratedMoserEnergyWindowFTC`.

2. `IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData` has two fields:
   - `atZero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0`
   - `pdeCombinedInitial : IntervalDomainLpPDECombinedInitialWindowIntegrability params u v T p0`

3. `intervalDomain_initialPowerEnergyContinuityAtZero_of_trace_paperPositive_classical_withInitialSlice`
   (line 2463): produces `atZero` from trace + positive datum + classical solution.

4. `P3MoserPDECombinedInitialProducer.lean` has producers for `pdeCombinedInitial`
   from global classical + derivative window integrability or FTC.

BUT: the hFTC hypothesis takes LOCAL classical `(hsol, hcross, hboot)`. The
producers need GLOBAL classical. The bridge is `IntervalDomainGlobalClassicalRegularityInputs`
which guarantees that the local solution can be re-anchored as part of a global one.

## What to write

A theorem:
```lean
theorem intervalDomain_assemblyFTC_of_globalInputs
    {p : CM2Params}
    (hinputs : IntervalDomainGlobalClassicalRegularityInputs p)
    [additional hypotheses if needed] :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyWindowFTC intervalDomain u T p0
```

## Approach

1. From `hinputs hsol hcross hboot`, extract `(u₀, uRaw, rfl, hglobal, htrace, hdatum, hp0, hgrad)`.
2. Use `hglobal` (global classical) + extracted data to produce `atZero` and `pdeCombinedInitial`.
3. Build `IntervalDomainIntegratedMoserEnergyWindowFTCGlobalPDEInitialData`.
4. Call `intervalDomain_integratedMoserEnergyWindowFTC_of_globalPDEInitialData`.

The tricky part: `hinputs` guarantees gradient continuity, which gives the
regularity data. But the FTC needs derivative integrability, which comes from
the PDE combined initial data. Check whether `hinputs` already provides
enough to produce the FTC, or whether additional hypotheses are needed.

If additional hypotheses are needed (e.g., derivative integrability at t=0),
carry them explicitly and document what they are.

## Files to read

1. `ShenWork/PDE/P3MoserEnergyContinuity.lean` — FTC producers (lines 2316-2460)
2. `ShenWork/PDE/P3MoserPDECombinedInitialProducer.lean` — PDE combined initial
3. `ShenWork/Paper3/IntervalDomainGlobalChain.lean` — hinputs structure (lines 62-77)

## Imports

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserPDECombinedInitialProducer
import ShenWork.Paper3.IntervalDomainGlobalChain
```

## Rules

- 0 sorry, 0 custom axiom
- Write ONLY `ShenWork/PDE/P3MoserFTCGlobalProducer.lean`
- If the FTC cannot be fully produced from hinputs alone, carry the remaining
  hypotheses explicitly and add a comment documenting the residual.
- Add `#print axioms` at the end
- Verify: `lake env lean ShenWork/PDE/P3MoserFTCGlobalProducer.lean`
