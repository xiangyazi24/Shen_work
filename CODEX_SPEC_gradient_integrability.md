# Task: Produce gradientTimeIntegrable from classical solution regularity

## Context

The `IntervalDomainIntegratedMoserClassicalRegularityData` structure (at
`P3MoserRegularityProducer.lean:143`) has two fields:
1. `endpointEnergy : IntervalDomainPowerEnergyEndpointContinuity u T p0` — partially done
2. `gradientTimeIntegrable` — the target of THIS task

The `gradientTimeIntegrable` field says:
```lean
gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume
```

This is: the map `t ↦ ∫_Ω |∇(u(t,·)^{p/2})|² dx` is integrable over `[0,T]`.

## Goal

Investigate whether this can be proved from `IsPaper2ClassicalSolution` (or
`IsPaper2GlobalClassicalSolution`) and produce as much as possible.

### Step 1: Read and understand the existing infrastructure

Read these files to understand what regularity `IsPaper2ClassicalSolution` provides:
1. `ShenWork/Paper2/Statements.lean` — find `IsPaper2ClassicalSolution` definition
2. `ShenWork/PDE/P3MoserRegularityProducer.lean` — find any existing producers of gradient integrability
3. `ShenWork/PDE/P3MoserEnergyContinuity.lean` — find anything about gradient energy or derivative integrability
4. `ShenWork/PDE/P3MoserIntegratedClosure.lean` — find gradient-related results

Grep for: `gradientTimeIntegrable`, `gradNorm.*IntegrableOn`, `IntegrableOn.*gradNorm`,
`DerivativeWindowIntegrability`, `derivativePositiveStart`, `gradientEnergy`

### Step 2: Mathematical argument

For a classical solution on `(0,T) × Ω` (where Ω = [0,1]):
- `u(t,·)` is smooth for each `t ∈ (0,T)`
- The gradient `∂_x u(t,x)` is continuous on `(0,T) × [0,1]`
- Therefore `t ↦ ∫₀¹ |∂_x(u(t,x)^{p/2})|² dx` is continuous on `(0,T)`
- A continuous function on `(0,T)` is integrable on `[a,b] ⊂ (0,T)` for any compact `[a,b]`
- The question is boundary behavior at `t=0` and `t=T`

The existing `IntervalDomainIntegratedMoserGlobalClassicalRegularityData` has the same field,
suggesting this is genuinely carried (not derivable from classical solution alone).

### Step 3: Deliver what you can

If the full `gradientTimeIntegrable` is too hard to produce from classical solution:
1. Check if there's a WEAKER version that IS producible (e.g., integrability on `(ε, T-ε)`)
2. Check if there's an existing structure that carries it but can be partially discharged
3. Report precisely what's missing — which step fails and why

Create results in a NEW file: `ShenWork/PDE/P3MoserGradientIntegrability.lean`

## Build command
```bash
cd ~/repos/Shen_work && lake env lean ShenWork/PDE/P3MoserGradientIntegrability.lean 2>&1 | tail -30
```

## Rules
- No sorry, no axiom, no native_decide
- This is a RESEARCH task — deliver what you can prove + precise stall report
- Work only in /Users/huangx/repos/Shen_work/
